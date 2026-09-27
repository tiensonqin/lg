open Ast
open Types
open Lowered
module Env = Compiler_environment

let record_type_key = Resolver.record_type_key

let declare_type ?(type_parameters = []) ?manifest scope env name kind =
  Type_registry.declare ~type_parameters ?manifest ~scope name kind
    (Env.types env)
  |> Result.map (fun (type_id, types) -> (type_id, Env.with_types types env))

let compile_opaque_type ?location scope env next_type name =
  match declare_type scope env name Opaque with
  | Error _ as error -> error
  | Ok (_, env) ->
      Ok
        ( scope,
          env,
          next_type,
          Opaque_type { type_name = Names.sanitize_name name; location } )

let compile_type_alias ?location scope env next_type name type_parameters
    manifest_form =
  match manifest_form with
  | FKeyword keyword -> (
      match
        Type_annotation.of_keyword_with_parameters type_parameters keyword
      with
      | Error _ as error -> error
      | Ok manifest -> (
          let manifest =
            Function_elaborator.infer_named_record scope env manifest
          in
          let type_name = Names.sanitize_name name in
          match
            declare_type ~type_parameters ~manifest scope env name Alias
          with
          | Error _ as err -> err
          | Ok (_type_id, env) ->
              Ok
                ( scope,
                  env,
                  next_type,
                  Type_alias { type_name; type_parameters; manifest; location }
                )))
  | _ -> Error.error "type-alias expects a type keyword target"

let compile_type_record_fields ?location ?(allow_empty = false) ?emitted_name
    ?(nominal = true) ?(reuse_existing = false) scope env next_type name
    type_parameters fields =
  if fields = [] && not allow_empty then
    Error.error "type-record expects at least one field"
  else
    let type_name =
      Option.value emitted_name ~default:(Names.sanitize_name name)
    in
    (* Forward defrecords publish placeholder metadata before their declaration.
       A new record cannot have existing consumers of such a placeholder. *)
    let replaces_record_metadata = Env.mem (record_type_key scope name) env in
    let existing_record =
      if reuse_existing then
        match Resolver.lookup_type_declaration scope env name with
        | Some { kind = Record; type_parameters = existing_parameters; _ }
          when existing_parameters = type_parameters -> (
            match Resolver.lookup_record_type scope env name with
            | Ok record -> Some record
            | Error _ -> None)
        | Some _ | None -> None
      else None
    in
    match existing_record with
    | Some record ->
        let compatible_fields =
          List.length record.fields = List.length fields
          && List.for_all2
               (fun existing declared ->
                 String.equal existing.keyword declared.keyword
                 && Types.equal existing.ty declared.ty)
               record.fields fields
        in
        if not compatible_fields then
          Error.error ("defrecord does not match declared type " ^ name)
        else Ok (scope, env, next_type, Group [])
    | None -> (
        match declare_type scope env name Record with
        | Error _ as err -> err
        | Ok (type_id, env) ->
            let record_ty =
              Types.named_record ~type_id ~nominal ~type_name ~type_parameters
                ~set_module_name:("Set_" ^ type_name) fields
            in
            let env =
              Env.add
                (record_type_key scope name)
                (Types.binding type_name record_ty)
                env
            in
            let env =
              match record_ty with
              | TNamed_record record when replaces_record_metadata ->
                  let refresh = Types.refresh_named_record record in
                  Env.fold
                    (fun key (binding : Types.binding) env ->
                      let ty = refresh binding.ty in
                      if ty == binding.ty then env
                      else Env.add key { binding with ty } env)
                    env env
              | _ -> env
            in
            Ok
              ( scope,
                env,
                next_type,
                Type_def
                  {
                    type_id;
                    type_name;
                    type_parameters;
                    fields;
                    nominal;
                    location;
                  } ))

let compile_type_record ?location ?(allow_empty = false) ?emitted_name
    ?(nominal = true) scope env next_type name type_parameters field_forms =
  let field_spec = function
    | FList [ (FSymbol field_name as name_form); type_form ] ->
        let annotation =
          match type_form with
          | FKeyword keyword -> Ok ([], keyword)
          | FList [ FSymbol "forall"; parameters; FKeyword keyword ] ->
              Result.map
                (fun parameters -> (parameters, keyword))
                (Type_parameters.parse parameters)
          | _ ->
              Error.error
                "record field type must be :type or (forall [parameters] :type)"
        in
        Result.bind annotation (fun (quantified, keyword) ->
            if
              List.exists (fun name -> List.mem name type_parameters) quantified
            then
              Error.error
                "record field quantifiers must not shadow record type \
                 parameters"
            else
              Result.map
                (fun ty ->
                  {
                    keyword = ":" ^ field_name;
                    ocaml_name = Names.sanitize_name field_name;
                    ty = Function_elaborator.infer_named_record scope env ty;
                    quantified;
                    mutable_ = false;
                    runtime_map = false;
                    location = Source_context.find name_form;
                  })
                (Type_annotation.of_keyword_with_parameters
                   (quantified @ type_parameters)
                   keyword))
    | _ -> Error.error "type-record fields must be (name :type)"
  in
  let rec parse (fields : field list) = function
    | [] -> Ok (List.rev fields)
    | field_form :: rest -> (
        match field_spec field_form with
        | Error _ as err -> err
        | Ok field ->
            if
              List.exists
                (fun (existing : field) ->
                  existing.ocaml_name = field.ocaml_name)
                fields
            then Error.error "duplicate record field name"
            else parse (field :: fields) rest)
  in
  match parse [] field_forms with
  | Error _ as err -> err
  | Ok fields ->
      (* Field annotations can reference parametric records without arguments
         (e.g. :option<fn<string;model/CacheModel>>); the resulting free type
         variables become implicit type parameters of the record, matching
         how deftype generalizes unannotated field types. Field-level forall
         quantifiers stay field-scoped. *)
      let rec free_variables bound ty =
        let free_in_fields fields =
          List.concat_map
            (fun (field : field) ->
              free_variables (field.quantified @ bound) field.ty)
            fields
        in
        match ty with
        | TVar name when not (List.mem name bound) -> [ name ]
        | TPoly_variant row ->
            List.concat_map (free_variables bound) (List.filter_map snd row.tags)
        | TNullable ty | TArray ty | TRef ty | TList ty | TVector ty | TSet ty
        | TSeq ty ->
            free_variables bound ty
        | TOcaml_app (_, arguments) | TTuple arguments ->
            List.concat_map (free_variables bound) arguments
        | TConstraint constraint_ ->
            List.concat_map (free_variables bound)
              (Types.constraint_children constraint_)
        | TFn (parameters, return_ty) ->
            List.concat_map (free_variables bound) (return_ty :: parameters)
        | TOverloaded_fn arities ->
            List.concat_map
              (fun (arity : fn_arity) ->
                free_variables bound arity.return_ty
                @ List.concat_map (free_variables bound) arity.fixed_params
                @ Option.fold ~none:[] ~some:(free_variables bound)
                    arity.rest_param)
              arities
        | TRecord fields -> free_in_fields fields
        | TNamed_record record ->
            List.concat_map (free_variables bound) record.type_arguments
        | _ -> []
      in
      let fields, implicit_parameters =
        fields
        |> List.map (fun (field : field) ->
               let ty = (Type_solver.generalize field.ty).body in
               ( { field with ty },
                 free_variables (field.quantified @ type_parameters) ty ))
        |> List.split
      in
      let implicit_parameters =
        List.concat implicit_parameters |> List.sort_uniq String.compare
      in
      compile_type_record_fields ?location ~allow_empty ?emitted_name ~nominal
        scope env next_type name
        (type_parameters @ implicit_parameters)
        fields

let record_type_public_binding module_path name env =
  let key = record_type_key module_path name in
  match Env.find_opt key env with
  | Some binding ->
      Ok
        ( key,
          {
            binding with
            ty =
              Types.qualify_module_type
                (Names.module_path_to_ocaml module_path)
                binding.ty;
          } )
  | None -> Error.error ("internal error: missing record metadata for " ^ name)

let compile_type_variant ?location scope env next_type name type_parameters
    constructor_forms =
  let emitted_constructor_name name =
    let buffer = Buffer.create (String.length name) in
    String.iter
      (function
        | ('a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | '\'') as ch ->
            Buffer.add_char buffer ch
        | '!' -> Buffer.add_string buffer "_bang"
        | _ -> Buffer.add_char buffer '_')
      name;
    String.capitalize_ascii (Buffer.contents buffer)
  in
  let constructor_name = function
    | FSymbol constructor as form -> Ok (constructor, Source_context.find form)
    | _ -> Error.error "type-variant constructors must be symbols"
  in
  let payload_type parameters = function
    | FKeyword keyword -> (
        match Type_annotation.of_keyword_with_parameters parameters keyword with
        | Ok ty -> Ok (Function_elaborator.infer_named_record scope env ty)
        | Error _ as error -> error)
    | _ -> Error.error "type-variant payload types must be keywords"
  in
  let constructor_spec = function
    | FSymbol constructor as form ->
        Ok
          {
            constructor_name = constructor;
            payload_types = [];
            result_type = None;
            location = Source_context.find form;
          }
    | FList (constructor_form :: payload_forms) -> (
        match constructor_name constructor_form with
        | Error _ as err -> err
        | Ok (constructor_name, location) ->
            let local_parameters =
              match payload_forms with
              | (FVector _ as parameters) :: rest ->
                  Result.map
                    (fun parameters -> (parameters, rest))
                    (Type_parameters.parse parameters)
              | _ -> Ok ([], payload_forms)
            in
            Result.bind local_parameters
              (fun (local_parameters, payload_forms) ->
                let payload_type =
                  payload_type (local_parameters @ type_parameters)
                in
                let rec parse_payloads acc = function
                  | [] -> Ok (List.rev acc)
                  | payload_form :: rest -> (
                      match payload_type payload_form with
                      | Error _ as err -> err
                      | Ok payload_ty -> parse_payloads (payload_ty :: acc) rest
                      )
                in
                let payload_forms, result_form =
                  match List.rev payload_forms with
                  | FList [ FSymbol "returns"; result ] :: rest ->
                      (List.rev rest, Some result)
                  | _ -> (payload_forms, None)
                in
                let result_type =
                  match result_form with
                  | None -> Ok None
                  | Some form -> Result.map Option.some (payload_type form)
                in
                Result.bind result_type (fun result_type ->
                    parse_payloads [] payload_forms
                    |> Result.map (fun payload_types ->
                        {
                          constructor_name;
                          payload_types;
                          result_type;
                          location;
                        }))))
    | _ -> Error.error "type-variant constructors must be symbols"
  in
  let rec parse constructors = function
    | [] -> Ok (List.rev constructors)
    | constructor_form :: rest -> (
        match constructor_spec constructor_form with
        | Error _ as err -> err
        | Ok constructor ->
            if
              List.exists
                (fun existing ->
                  emitted_constructor_name existing.constructor_name
                  = emitted_constructor_name constructor.constructor_name)
                constructors
            then
              Error.error
                ("duplicate variant constructor " ^ constructor.constructor_name)
            else parse (constructor :: constructors) rest)
  in
  match parse [] constructor_forms with
  | Error _ as err -> err
  | Ok [] -> Error.error "type-variant expects at least one constructor"
  | Ok constructors -> (
      let type_name = Names.sanitize_name name in
      let result_type =
        match type_parameters with
        | [] -> TOcaml type_name
        | parameters ->
            TOcaml_app (type_name, List.map (fun name -> TVar name) parameters)
      in
      let constructor_bindings =
        constructors
        |> List.map (fun constructor ->
            ( Names.scoped_key scope constructor.constructor_name,
              Types.binding
                ~gadt_constructor:(Option.is_some constructor.result_type)
                (emitted_constructor_name constructor.constructor_name)
                (TFn
                   ( constructor.payload_types,
                     Option.value constructor.result_type ~default:result_type
                   )) ))
      in
      let constructors =
        List.map
          (fun constructor ->
            { constructor with constructor_name = emitted_constructor_name constructor.constructor_name })
          constructors
      in
      match declare_type scope env name Variant with
      | Error _ as err -> err
      | Ok (_type_id, env) ->
          let env =
            Env.add_closed_sum_constructors result_type
              (List.map
                 (fun constructor ->
                   (constructor.constructor_name, constructor.payload_types))
                 constructors)
              env
          in
          let env =
            Env.add_predicate_sum_constructors result_type
              (List.map
                 (fun constructor ->
                   (constructor.constructor_name, constructor.payload_types))
                 constructors)
              env
          in
          Ok
            ( scope,
              Env.add_bindings constructor_bindings env,
              next_type,
              Type_variant
                { type_name; type_parameters; constructors; location } ))
