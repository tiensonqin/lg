open Ast
open Types
open Lowered

module Env = Compiler_environment

let fixed_arities = function
  | TFn (parameters, _) -> Some [ List.length parameters ]
  | TOverloaded_fn arities
    when List.for_all (fun arity -> Option.is_none arity.rest_param) arities ->
      Some
        (List.map (fun arity -> List.length arity.fixed_params) arities
        |> List.sort_uniq Int.compare)
  | _ -> None

let export_method_bindings scope env protocol_id signatures =
  List.fold_left
    (fun env (signature : Protocol_registry.method_signature) ->
      let method_name = Method_id.name signature.method_id in
      let name = Names.scoped_key scope method_name in
      match Env.find_opt name env with
      | Some _ -> env
      | None ->
          let marker =
            Protocol.lookup_marker scope env method_name
            |> Option.value
                 ~default:
                   (Protocol.marker_binding protocol_id
                      {
                        Protocol.method_id = signature.method_id;
                        method_name;
                        method_ty = signature.method_ty;
                      })
          in
          Env.add name
            marker
            env)
    env signatures

let export_protocol_binding scope env protocol_name protocol_id =
  Env.add (Names.scoped_key scope protocol_name)
    (Protocol.protocol_binding protocol_id) env

let validate_core_protocol_surface protocol_id source_signatures declaration =
  let source_methods =
    List.map
      (fun (signature : Protocol_registry.method_signature) ->
        (Method_id.name signature.method_id, signature.method_ty))
      source_signatures
    |> List.sort compare
  in
  let builtin_methods =
    Protocol_registry.Method_map.bindings declaration.Protocol_registry.methods
    |> List.map (fun (method_id, signature) ->
           (Method_id.name method_id, signature.Protocol_registry.method_ty))
    |> List.sort compare
  in
  let source_names = List.map fst source_methods in
  let builtin_names = List.map fst builtin_methods in
  if source_names <> builtin_names then
    Error.error ~code:Error_code.Protocol
      ("clojure.core protocol " ^ Protocol_id.name protocol_id
     ^ " must declare the compiler-backed method surface exactly")
  else
    let rec validate = function
      | [], [] -> Ok ()
      | (name, source_ty) :: source_rest, (_, builtin_ty) :: builtin_rest -> (
          match (fixed_arities source_ty, fixed_arities builtin_ty) with
          | Some source_arities, Some builtin_arities
            when source_arities = builtin_arities ->
              validate (source_rest, builtin_rest)
          | _ ->
              Error.error ~code:Error_code.Protocol
                ("clojure.core protocol method " ^ name
               ^ " must preserve the compiler-backed arities"))
      | _ -> assert false
    in
    validate (source_methods, builtin_methods)

let define ?location scope env protocol_name method_forms =
  let canonical_name = Protocol.canonical_protocol_name protocol_name in
  let builtin_id = Protocol_id.create ~owner:[] ~name:canonical_name in
  let builtin_declaration =
    if String.equal scope "clojure.core" then
      Protocol_registry.find_protocol builtin_id (Env.protocols env)
    else None
  in
  let declaration_scope, declaration_name =
    match builtin_declaration with
    | Some _ -> ("", canonical_name)
    | None -> (scope, protocol_name)
  in
  match
    Protocol.defprotocol declaration_scope declaration_name method_forms
  with
  | Error _ as err -> err
  | Ok (protocol_id, signatures) ->
      let resolve_type = Function_elaborator.infer_named_record scope env in
      let signatures =
        List.map
          (fun (signature : Protocol_registry.method_signature) ->
            let method_name = Method_id.name signature.method_id in
            let method_ty =
              Signature_overlay.find_value
                (Names.scoped_key scope method_name)
                (Env.signatures env)
              |> Option.value ~default:signature.method_ty
            in
            {
              signature with
              method_ty = resolve_type method_ty;
            })
          signatures
      in
      let method_locations =
        List.filter_map
          (function
            | FList (((FSymbol method_name) as name_form) :: _) ->
                Source_context.find name_form
                |> Option.map (fun location ->
                       (Protocol.method_id protocol_id method_name, location))
            | _ -> None)
          method_forms
      in
      (match builtin_declaration with
      | Some declaration -> (
          match
            validate_core_protocol_surface protocol_id signatures declaration
          with
          | Error _ as err -> err
          | Ok () ->
              let env =
                export_protocol_binding scope env protocol_name protocol_id
                |> fun env ->
                export_method_bindings scope env protocol_id signatures
              in
              Ok
                ( env,
                  Comment
                    ("source declaration for compiler-backed protocol "
                   ^ protocol_name) ))
      | None ->
      (match
         Protocol_registry.declare ?location ~method_locations protocol_id signatures
           (Env.protocols env)
       with
      | Error _ as err -> err
      | Ok protocols ->
          let env =
            Env.with_protocols protocols env
            |> fun env ->
            export_protocol_binding scope env protocol_name protocol_id
            |> fun env ->
            export_method_bindings scope env protocol_id signatures
          in
          Ok (env, Comment ("protocol " ^ protocol_name))))

let marker scope env protocol_name method_name =
  match
    Protocol.lookup_protocol_marker ~refine:false scope env protocol_name
      method_name
  with
  | None ->
      Error.error ~code:Error_code.Protocol
        ("protocol " ^ protocol_name ^ " does not define method " ^ method_name)
  | Some marker
    when not
           (match Protocol.find_protocol_id scope env protocol_name with
           | Some protocol_id ->
               Protocol.marker_has_protocol_id marker protocol_id
           | None -> false) ->
      Error.error ~code:Error_code.Protocol
        ("protocol " ^ protocol_name ^ " does not define method " ^ method_name)
  | Some marker -> Ok marker

let add_implementation ?location env method_name receiver_ty marker binding =
  match
    (marker.protocol_id, Protocol.registry_receiver_id receiver_ty)
  with
  | None, _ | _, None ->
      Error.error ~code:Error_code.Protocol
        ("protocol implementations do not support receiver type "
       ^ source_name receiver_ty)
  | Some protocol_id, Some receiver_id ->
      let method_id = Protocol.method_id protocol_id method_name in
      let existing =
        Protocol_registry.find_implementation protocol_id method_id receiver_id
          (Env.protocols env)
      in
      let protocols =
        match existing with
        | Some existing
          when existing.forward_declared
               && existing.ocaml_name = binding.ocaml_name ->
            Ok
              (Protocol_registry.replace_implementation protocol_id method_id
                 receiver_id binding (Env.protocols env))
        | Some _ ->
            Error.error ~code:Error_code.Duplicate
              ("duplicate implementation of " ^ Protocol_id.name protocol_id
             ^ "/" ^ method_name ^ " for " ^ source_name receiver_ty)
        | None ->
            Protocol_registry.add_implementation ?location protocol_id
              method_id receiver_id binding (Env.protocols env)
      in
      (match protocols with
      | Error _ as err -> err
      | Ok protocols ->
          let env = Env.with_protocols protocols env in
          let protocol_evidence =
            Env.protocol_evidence env
            |> Option.map
                 (Protocol_registry.replace_implementation protocol_id
                    method_id receiver_id binding)
          in
          Ok (Env.with_protocol_evidence protocol_evidence env))

let add_marker_implementation env protocol_id receiver_ty =
  match Protocol.registry_receiver_id receiver_ty with
  | None ->
      Error.error ~code:Error_code.Protocol
        ("marker protocol implementations do not support receiver type "
       ^ source_name receiver_ty)
  | Some receiver_id ->
      let add registry =
        Protocol_registry.add_marker_implementation protocol_id receiver_id
          registry
      in
      let env = Env.with_protocols (add (Env.protocols env)) env in
      Ok
        (Env.with_protocol_evidence
           (Option.map add (Env.protocol_evidence env))
           env)

let update_overloaded_implementation env method_name receiver_ty
    (marker : binding) (binding : binding) =
  match
    ( marker.protocol_id,
      Protocol.registry_receiver_id receiver_ty,
      binding.ty )
  with
  | Some protocol_id, Some receiver_id, TFn (parameters, return_ty) ->
      let method_id = Protocol.method_id protocol_id method_name in
      let update registry =
        match
          Protocol_registry.find_implementation protocol_id method_id
            receiver_id registry
        with
        | Some ({ ty = TOverloaded_fn arities; _ } as implementation) ->
            let argument_count = List.length parameters in
            let arities =
              List.map
                (fun arity ->
                  if
                    Option.is_none arity.rest_param
                    && List.length arity.fixed_params = argument_count
                  then
                    {
                      fixed_params = parameters;
                      rest_param = None;
                      return_ty;
                    }
                  else arity)
                arities
            in
            Protocol_registry.replace_implementation protocol_id method_id
              receiver_id
              {
                implementation with
                ty = TOverloaded_fn arities;
                forward_declared = false;
              }
              registry
        | Some _ | None -> registry
      in
      let env = Env.with_protocols (update (Env.protocols env)) env in
      Ok
        (Env.with_protocol_evidence
           (Option.map update (Env.protocol_evidence env))
           env)
  | _ ->
      Error.error ~code:Error_code.Protocol
        ("multi-arity protocol implementation " ^ method_name
       ^ " must compile to a fixed-arity function")

let method_return_needs_context env method_ty =
  let rec contains_contextual_closed_sum ty =
    Env.variant_constructors ty env <> []
    ||
    match ty with
    | TNullable inner | TArray inner | TRef inner | TList inner | TVector inner
    | TSet inner | TSeq inner ->
        contains_contextual_closed_sum inner
    | TOcaml_app (_, arguments) | TTuple arguments ->
        List.exists contains_contextual_closed_sum arguments
    | _ -> false
  in
  let expected_return_ty =
    match method_ty with
    | TFn (_, return_ty) -> Some return_ty
    | TOverloaded_fn [ arity ] -> Some arity.return_ty
    | _ -> None
  in
  Option.fold ~none:false
    ~some:(fun return_ty ->
      match return_ty with
      | TFn _ | TOverloaded_fn _ -> true
      | _ -> contains_contextual_closed_sum return_ty)
    expected_return_ty

let compile_defprotocol ?location scope env next_type protocol_name method_forms =
  match define ?location scope env protocol_name method_forms with
  | Error _ as err -> err
  | Ok (env, item) -> Ok (scope, env, next_type, item)

let protocol_receiver_type scope env = function
  | FKeyword ":default" -> Ok (TVar Receiver_id.default_type_variable)
  | FSymbol "nil" | FKeyword ":nil" -> Ok TNil
  | FKeyword receiver_keyword -> Type_annotation.of_keyword receiver_keyword
  | FSymbol type_name -> (
      match Resolver.lookup_record_type scope env type_name with
      | Ok record -> Ok (TNamed_record record)
      | Error _ -> (
          match Resolver.lookup_type_declaration scope env type_name with
          | Some
              {
                Type_registry.kind = Variant;
                type_id;
                type_parameters;
                _;
              } ->
              let emitted_name =
                Names.sanitize_name (Type_id.name type_id)
              in
              if type_parameters = [] then Ok (TOcaml emitted_name)
              else
                Ok
                  (TOcaml_app
                     ( emitted_name,
                       List.map (fun parameter -> TVar parameter) type_parameters
                     ))
          | Some _ | None ->
              Error.error ~code:Error_code.Unresolved ("unknown protocol receiver type " ^ type_name)))
  | _ ->
      Error.error ~code:Error_code.Protocol
        "extend-type receiver must be a type keyword, record, or closed variant"

let protocol_parameter_overrides receiver_ty = function
  | TFn (parameter_tys, _) ->
      let instantiated_variables = ref [] in
      let instantiate name =
        match List.assoc_opt name !instantiated_variables with
        | Some ty -> ty
        | None ->
            let ty = Type_solver.fresh () in
            instantiated_variables := (name, ty) :: !instantiated_variables;
            ty
      in
      List.mapi
        (fun index ty ->
          if index = 0 then Some receiver_ty
          else
            match ty with
            | TUnknown | TMeta _ -> None
            | TVar name -> Some (instantiate name)
            | ty -> Some ty)
        parameter_tys
  | _ -> [ Some receiver_ty ]

let common_implementation_parameter_constraints env protocol_id method_id =
  let registry =
    Compiler_environment.protocol_evidence env
    |> Option.value ~default:(Env.protocols env)
  in
  let parameter_lists =
    Protocol_registry.implementations_for_method protocol_id method_id registry
    |> List.filter_map (fun (implementation : binding) ->
           match implementation.ty with
           | TFn (_receiver :: parameters, _) -> Some parameters
           | TFn ([], _) | _ -> None)
  in
  match parameter_lists with
  | [] -> []
  | first :: rest
    when List.for_all
           (fun parameters -> List.length parameters = List.length first)
           rest ->
      List.mapi
        (fun index _ ->
          let candidates =
            parameter_lists
            |> List.filter_map (fun parameters ->
                   match List.nth parameters index with
                   | TUnknown | TMeta _ | TVar _ -> None
                   | ty
                     when Option.is_some
                            (Types.capability_constraint_value ty) ->
                       Some ty
                   | _ -> None)
          in
          match candidates with
          | candidate :: candidates
            when List.for_all (Types.equal candidate) candidates ->
              Some candidate
          | [] | _ :: _ -> None)
        first
  | _ -> []

let refine_protocol_implementation_type expected actual =
  let refine_position expected actual =
    match actual with
    | TUnknown | TMeta _ | TVar _ -> (
        match expected with
        | TUnknown | TMeta _ | TVar _ -> actual
        | expected -> expected)
    | actual -> actual
  in
  match (expected, actual) with
  | TFn (expected_params, expected_return), TFn (actual_params, actual_return)
    when List.length expected_params = List.length actual_params ->
      TFn
        ( List.map2 refine_position expected_params actual_params,
          refine_position expected_return actual_return )
  | _, actual -> actual

let predeclare_implementations scope env receiver_form protocol_name method_forms =
  Result.bind (protocol_receiver_type scope env receiver_form) (fun receiver_ty ->
      let implementation_name method_name argument_count overloaded =
        let base =
          Protocol.impl_ocaml_name scope protocol_name method_name receiver_ty
        in
        if overloaded then base ^ "_" ^ string_of_int argument_count else base
      in
      let select_method_arity (marker : binding) argument_count =
        match marker.ty with
        | TOverloaded_fn arities ->
            arities
            |> List.find_opt (fun arity ->
                   Option.is_none arity.rest_param
                   && List.length arity.fixed_params = argument_count)
            |> Option.map (fun arity ->
                   {
                     marker with
                     ty = TFn (arity.fixed_params, arity.return_ty);
                   })
        | TFn (parameters, _) when List.length parameters = argument_count ->
            Some marker
        | _ -> None
      in
      let overloaded_binding (marker : binding) method_name =
        match marker.ty with
        | TOverloaded_fn arities ->
            let overload_targets =
              List.map
                (fun arity ->
                  implementation_name method_name
                    (List.length arity.fixed_params)
                    true)
                arities
            in
            let ocaml_name =
              match overload_targets with
              | ocaml_name :: _ -> ocaml_name
              | [] ->
                  Protocol.impl_ocaml_name scope protocol_name method_name
                    receiver_ty
            in
            Some
              (Types.binding ~forward_declared:true ~overload_targets ocaml_name
                 (Types.instantiate_receiver_method_type receiver_ty marker.ty))
        | _ -> None
      in
      let rec loop env = function
        | [] -> Ok env
        | FList (FSymbol method_name :: (FVector _ as params) :: _) :: rest ->
            Result.bind (marker scope env protocol_name method_name)
              (fun protocol_marker ->
                Result.bind (Type_annotation.parse_params params)
                  (fun parsed_params ->
                    let argument_count = List.length parsed_params in
                    match select_method_arity protocol_marker argument_count with
                    | None ->
                        Error.error ~code:Error_code.Unsupported
                          (method_name
                         ^ " called with unsupported protocol method arity "
                         ^ string_of_int argument_count)
                    | Some selected_marker ->
                        let binding =
                          match
                            overloaded_binding protocol_marker method_name
                          with
                          | Some binding -> binding
                          | None ->
                              Types.binding ~forward_declared:true
                                (implementation_name method_name argument_count
                                   false)
                                (Types.instantiate_receiver_method_type receiver_ty
                                   selected_marker.ty)
                        in
                        (match
                           Protocol.lookup_marker_impl env protocol_marker
                             method_name receiver_ty
                         with
                        | Some _ -> loop env rest
                        | None ->
                            Result.bind
                              (add_implementation env method_name receiver_ty
                                 protocol_marker binding)
                              (fun env -> loop env rest))))
        | _ :: rest -> loop env rest
      in
      loop env method_forms)

let predeclare_implementations_from_evidence scope env receiver_form
    protocol_name method_forms =
  match
    ( Protocol.find_protocol_id scope env protocol_name,
      Env.protocol_evidence env )
  with
  | None, _ | _, None -> Ok env
  | Some _, Some evidence ->
      Result.bind (protocol_receiver_type scope env receiver_form)
        (fun receiver_ty ->
          let rec predeclare env = function
            | [] -> Ok env
            | FList (FSymbol method_name :: _params :: _) :: rest ->
                Result.bind (marker scope env protocol_name method_name)
                  (fun marker ->
                    match
                      ( marker.protocol_id,
                        Protocol.registry_receiver_id receiver_ty )
                    with
                    | Some protocol_id, Some receiver_id ->
                        let method_id =
                          Protocol.method_id protocol_id method_name
                        in
                        (match
                           Protocol_registry.find_implementation protocol_id
                             method_id receiver_id evidence
                         with
                        | None -> predeclare env rest
                        | Some binding ->
                            Result.bind
                              (add_implementation env method_name receiver_ty
                                 marker
                                 { binding with forward_declared = true })
                              (fun env -> predeclare env rest))
                    | None, _ | _, None -> predeclare env rest)
            | _ :: rest -> predeclare env rest
          in
          predeclare env method_forms)

let compile_extend_type scope env next_type receiver_form protocol_name method_forms =
  match protocol_receiver_type scope env receiver_form with
  | Error _ as err -> err
  | Ok receiver_ty ->
      let marker_protocol =
        Option.bind
          (Protocol.find_protocol_id scope env protocol_name)
          (fun protocol_id ->
            Option.bind
              (Protocol_registry.find_protocol protocol_id (Env.protocols env))
              (fun declaration ->
                if
                  method_forms = []
                  && Protocol_registry.Method_map.is_empty declaration.methods
                then Some protocol_id
                else None))
      in
      if Option.is_some marker_protocol then
        Result.map
          (fun env -> (scope, env, next_type, Group []))
          (add_marker_implementation env (Option.get marker_protocol) receiver_ty)
      else
      let select_method_arity (marker : binding) argument_count =
        match marker.ty with
        | TOverloaded_fn arities ->
            arities
            |> List.find_opt (fun arity ->
                   Option.is_none arity.rest_param
                   && List.length arity.fixed_params = argument_count)
            |> Option.map (fun arity ->
                   {
                     marker with
                     ty = TFn (arity.fixed_params, arity.return_ty);
                   })
        | TFn (parameters, _) when List.length parameters = argument_count ->
            Some marker
        | _ -> None
      in
      let implementation_name method_name argument_count overloaded =
        let base =
          Protocol.impl_ocaml_name scope protocol_name method_name receiver_ty
        in
        if overloaded then base ^ "_" ^ string_of_int argument_count else base
      in
      let overloaded_implementation (marker : binding) method_name =
        match marker.ty with
        | TOverloaded_fn arities ->
            let overload_targets =
              List.map
                (fun arity ->
                  implementation_name method_name
                    (List.length arity.fixed_params)
                    true)
                arities
            in
            let ocaml_name =
              match overload_targets with
              | ocaml_name :: _ -> ocaml_name
              | [] ->
                  Protocol.impl_ocaml_name scope protocol_name method_name
                    receiver_ty
            in
            Some
              (Types.binding ~overload_targets ocaml_name
                 (Types.instantiate_receiver_method_type receiver_ty marker.ty))
        | _ -> None
      in
      let rec form_mentions name = function
        | FSymbol candidate -> candidate = name
        | FList
            (FSymbol ("record" | "clojure.core/record" | "cljs.core/record")
            :: _type_name :: field_forms) ->
            List.exists
              (function
                | FList [ _field_name; value ] -> form_mentions name value
                | form -> form_mentions name form)
              field_forms
        | FList forms | FVector forms ->
            List.exists (form_mentions name) forms
        | FMap pairs ->
            List.exists
              (fun (key, value) ->
                form_mentions name key || form_mentions name value)
              pairs
        | FInt _ | FFloat _ | FDecimal _ | FChar _ | FString _ | FRegex _
        | FBool _
        | FKeyword _ | FCoreSymbol _ ->
            false
      in
      let bind_record_fields params body_forms =
        match (receiver_ty, params) with
        | TNamed_record record, FVector _ ->
            let receiver_name, parameter_names =
              match Destructure.parse_param_specs params with
              | Ok ({ source_name = receiver_name; _ } :: specs) ->
                  let parameter_names =
                    specs
                    |> List.concat_map (fun (spec : Destructure.param_spec) ->
                           spec.source_name
                           :: Destructure.pattern_names spec.pattern)
                  in
                  (receiver_name, receiver_name :: parameter_names)
              | Ok [] | Error _ ->
                  ( match params with
                  | FVector (FSymbol receiver_name :: _) -> receiver_name
                  | _ -> "__lg_deftype_this" ),
                  Destructure.pattern_names params
            in
            let bindings =
              record.fields
              |> List.filter (fun (field : field) ->
                     let name = Names.keyword_source_name field.keyword in
                     (not (List.mem name parameter_names))
                     && List.exists (form_mentions name) body_forms)
              |> List.concat_map (fun (field : field) ->
                     let name = Names.keyword_source_name field.keyword in
                     [ FSymbol name;
                       FList
                         [ FSymbol (".-" ^ name);
                           FSymbol receiver_name;
                         ];
                     ])
            in
            if bindings = [] then body_forms
            else [ FList (FSymbol "let" :: FVector bindings :: body_forms) ]
        | _ -> body_forms
      in
      let compile_method implementation_names env = function
        | FList (((FSymbol method_name) as name_form) :: params :: body_forms) -> (
            match marker scope env protocol_name method_name with
            | Error _ as err -> err
            | Ok protocol_marker -> (
                match Protocol.annotate_receiver receiver_ty params with
                | Error _ as err -> err
                | Ok params -> (
                    let body_forms = bind_record_fields params body_forms in
                    match Type_annotation.parse_params params with
                    | Error _ as error -> error
                    | Ok parsed_params ->
                      let argument_count = List.length parsed_params in
                      (match select_method_arity protocol_marker argument_count with
                      | None ->
                          Error.error ~code:Error_code.Unsupported
                            (method_name
                           ^ " called with unsupported protocol method arity "
                           ^ string_of_int argument_count)
                      | Some marker ->
                        let param_type_overrides =
                          protocol_parameter_overrides receiver_ty marker.ty
                        in
                        let param_type_overrides =
                          match marker.protocol_id with
                          | None -> param_type_overrides
                          | Some protocol_id ->
                              let method_id =
                                Protocol.method_id protocol_id method_name
                              in
                              let inferred =
                                common_implementation_parameter_constraints env
                                  protocol_id method_id
                              in
                              List.mapi
                                (fun index override ->
                                  match (index, override) with
                                  | 0, _ -> override
                                  | _, Some _ -> override
                                  | _, None ->
                                      List.nth_opt inferred (index - 1)
                                      |> Option.join)
                                param_type_overrides
                        in
                        let expected_method_ty =
                          Types.instantiate_receiver_method_type receiver_ty
                            marker.ty
                        in
                        let use_return_context =
                          method_return_needs_context env expected_method_ty
                        in
                        let method_env =
                          if use_return_context then
                            Env.with_expected_type (Some expected_method_ty) env
                          else env
                        in
                        match
                          Expression_elaborator.compile_fn ~param_type_overrides
                            ~preferred_record:receiver_ty
                            ~use_open_context:use_return_context scope method_env
                            params body_forms
                        with
                        | Error _ as err -> err
                        | Ok expr -> (
                        match (marker.ty, expr.ty) with
                        | TFn (expected_params, _), TFn (actual_params, _)
                          when List.length expected_params <> List.length actual_params ->
                            Error.error ~code:Error_code.Type_mismatch (method_name ^ " called with incompatible arguments")
                        | TFn (expected_params, expected_ret),
                          TFn (actual_params, actual_ret)
                          -> (
                            match actual_params with
                            | [] ->
                                Error.error ~code:Error_code.Protocol
                                  "protocol methods must have a receiver parameter"
                            | actual_receiver :: _ ->
                                let receiver_value_ty =
                                  Types.constraint_value_type actual_receiver
                                in
                                if
                                  not
                                    (Types.same_shape receiver_ty receiver_value_ty
                                    || Option.equal ( = )
                                         (Protocol.registry_receiver_id receiver_ty)
                                         (Protocol.registry_receiver_id
                                            receiver_value_ty))
                                then
                                  Error.error ~code:Error_code.Protocol
                                    ("protocol implementation receiver must be "
                                   ^ source_name receiver_ty
                                   ^ ", got " ^ source_name actual_receiver)
                                else
                                  let mismatch =
                                    List.combine expected_params actual_params
                                    |> List.mapi (fun index (expected, actual) ->
                                           (index, expected, actual))
                                    |> List.find_opt
                                         (fun (_index, expected, actual) ->
                                           (not
                                              (match expected with
                                              | TUnknown | TMeta _ | TVar _ ->
                                                  true
                                              | _ -> false))
                                           && not
                                                (Types.assignable
                                                   ~policy:Host_boundary
                                                   ~expected ~actual))
                                  in
                                  (match mismatch with
                                  | Some (index, expected, _actual) ->
                                      Error.error ~code:Error_code.Protocol
                                        ("protocol method " ^ method_name ^ " parameter "
                                       ^ string_of_int (index + 1) ^ " must be "
                                       ^ source_name expected)
                                  | None
                                    when (not
                                            (match expected_ret with
                                            | TUnknown | TMeta _ | TVar _ ->
                                                true
                                            | _ -> false))
                                         && not
                                           (Types.assignable ~policy:Host_boundary
                                              ~expected:expected_ret
                                              ~actual:actual_ret) ->
                                  Error.error ~code:Error_code.Protocol
                                    ("protocol method " ^ method_name ^ " must return "
                                   ^ source_name expected_ret)
                                  | None -> (
                                  let overloaded =
                                    match protocol_marker.ty with
                                    | TOverloaded_fn _ -> true
                                    | _ -> false
                                  in
                                  let ocaml_name =
                                    implementation_name method_name
                                      argument_count overloaded
                                  in
                                  let binding =
                                    Expression_support.binding_of_expr
                                      ocaml_name expr
                                  in
                                  let binding =
                                    if
                                      Option.is_none binding.return_param_index
                                      && Types.equal receiver_ty actual_ret
                                    then
                                      { binding with return_param_index = Some 0 }
                                    else binding
                                  in
                                  let register env =
                                    match
                                      overloaded_implementation protocol_marker
                                        method_name
                                    with
                                    | None ->
                                        add_implementation
                                          ?location:
                                            (Source_context.find name_form)
                                          env method_name receiver_ty marker
                                          binding
                                    | Some implementation ->
                                        let existing =
                                          Protocol.lookup_marker_impl env
                                            protocol_marker method_name
                                            receiver_ty
                                        in
                                        let added =
                                          match existing with
                                          | Some _ -> Ok env
                                          | None ->
                                              add_implementation
                                                ?location:
                                                  (Source_context.find name_form)
                                                env method_name receiver_ty
                                                protocol_marker implementation
                                        in
                                        Result.bind added (fun env ->
                                            update_overloaded_implementation env
                                              method_name receiver_ty
                                              protocol_marker binding)
                                  in
                                  (match register env with
                                  | Error _ as err -> err
                                  | Ok env ->
                                      let item =
                                        if
                                          Semantic_ir.exists_identifier
                                            (fun name ->
                                              Env.unresolved_declaration_binding
                                                name env)
                                            expr.semantic_expr
                                        then
                                          Deferred_value_binding
                                            { name = ocaml_name;
                                              value_type =
                                                Protocol.refine_deferred_type
                                                  env
                                                  (refine_protocol_implementation_type
                                                     marker.ty expr.ty);
                                              return_param_index =
                                                binding.return_param_index;
                                              expression = expr.semantic_expr;
                                            }
                                        else if
                                          Semantic_ir.exists_identifier
                                            (fun name ->
                                              List.mem name implementation_names)
                                            expr.semantic_expr
                                        then
                                          Recursive_value_binding
                                            { name = ocaml_name;
                                              identity = None;
                                              type_annotation = None;
                                              expression = expr.semantic_expr;
                                            }
                                        else
                                          Value_binding
                                            { pattern = Named ocaml_name;
                                              expression = expr.semantic_expr;
                                            }
                                      in
                                      Ok
                                        ( env,
                                          item )))))
                        | _ -> Error.error ~code:Error_code.Protocol "protocol method did not compile to a function")))))
        | _ -> Error.error ~code:Error_code.Protocol "extend-type methods must be (method-name [params] body)"
      in
      let rec loop implementation_names env items = function
        | [] ->
            let ordinary, recursive =
              List.rev items
              |> List.fold_left
                   (fun (ordinary, recursive) -> function
                     | Recursive_value_binding
                         { name; identity; type_annotation; expression } ->
                         ( ordinary,
                           ({
                              name;
                              identity;
                              type_annotation;
                              expression;
                            }
                             : recursive_value)
                           :: recursive )
                     | item -> (item :: ordinary, recursive))
                   ([], [])
            in
            let items =
              List.rev ordinary
              @
              match List.rev recursive with
              | [] -> []
              | bindings -> [ Recursive_value_bindings bindings ]
            in
            Ok
              ( scope,
                env,
                next_type,
                Group items )
        | method_form :: rest -> (
            match compile_method implementation_names env method_form with
            | Error _ as err -> err
            | Ok (env, item) ->
                loop implementation_names env (item :: items) rest)
      in
      let rec predeclare_declared env names = function
        | [] -> Ok (env, List.sort_uniq String.compare names)
        | FList (FSymbol method_name :: params :: _) :: rest -> (
            match marker scope env protocol_name method_name with
            | Error _ as error -> error
            | Ok protocol_marker -> (
                match Type_annotation.parse_params params with
                | Error _ as error -> error
                | Ok parsed_params ->
                    let argument_count = List.length parsed_params in
                    (match
                       select_method_arity protocol_marker argument_count
                     with
                    | None ->
                        Error.error ~code:Error_code.Unsupported
                          (method_name
                         ^ " called with unsupported protocol method arity "
                         ^ string_of_int argument_count)
                    | Some marker ->
                        let overloaded =
                          match protocol_marker.ty with
                          | TOverloaded_fn _ -> true
                          | _ -> false
                        in
                        let binding =
                          match
                            overloaded_implementation protocol_marker
                              method_name
                          with
                          | Some binding ->
                              { binding with forward_declared = true }
                          | None ->
                              Types.binding ~forward_declared:true
                                (implementation_name method_name argument_count
                                   overloaded)
                                (Types.instantiate_receiver_method_type
                                   receiver_ty marker.ty)
                        in
                        let names =
                          binding.ocaml_name
                          :: binding.overload_targets @ names
                        in
                        (match
                           Protocol.lookup_marker_impl env protocol_marker
                             method_name receiver_ty
                         with
                        | Some _ -> predeclare_declared env names rest
                        | None ->
                            Result.bind
                              (add_implementation env method_name receiver_ty
                                 protocol_marker binding)
                              (fun env ->
                                predeclare_declared env names rest)))))
        | _ :: _ ->
            Error.error ~code:Error_code.Protocol
              "extend-type methods must be (method-name [params] body)"
      in
      let rec predeclare_exact env evidence_env names = function
        | [] -> Ok (env, List.sort_uniq String.compare names)
        | FList (FSymbol method_name :: _params :: _) :: rest -> (
            match marker scope env protocol_name method_name with
            | Error _ as error -> error
            | Ok marker -> (
                match
                  ( marker.protocol_id,
                    Protocol.registry_receiver_id receiver_ty )
                with
                | Some protocol_id, Some receiver_id ->
                    let method_id =
                      Protocol.method_id protocol_id method_name
                    in
                    (match
                       Protocol_registry.find_implementation protocol_id
                         method_id receiver_id (Env.protocols evidence_env)
                     with
                    | None ->
                        Error.error ~code:Error_code.Protocol
                          ("missing inferred protocol implementation for "
                         ^ method_name)
                    | Some binding ->
                        let binding =
                          { binding with forward_declared = true }
                        in
                        (match
                           add_implementation env method_name receiver_ty marker
                             binding
                         with
                        | Error _ as error -> error
                        | Ok env ->
                            predeclare_exact env evidence_env
                              (binding.ocaml_name
                              :: binding.overload_targets @ names)
                              rest))
                | None, _ | _, None ->
                    Error.error ~code:Error_code.Protocol
                      ("protocol implementations do not support receiver type "
                     ^ source_name receiver_ty)))
        | _ :: _ ->
            Error.error ~code:Error_code.Protocol "extend-type methods must be (method-name [params] body)"
      in
      Result.bind (predeclare_declared env [] method_forms)
        (fun (initial_env, initial_implementation_names) ->
          Result.bind
            (loop initial_implementation_names initial_env [] method_forms)
            (fun (_, evidence_env, _, _) ->
              Result.bind
                (predeclare_exact env evidence_env [] method_forms)
                (fun (env, implementation_names) ->
                  loop implementation_names env [] method_forms)))
