open Ast
open Types
open Expression_support
module Env = Compiler_environment

let dissoc_expansion_counter = ref 0
let assoc_expansion_counter = ref 0

type expression_result = (typed_expr, Error.t) result
type call = string -> Env.t -> Ast.form list -> expression_result
type forms = Ast.form list -> expression_result

type t = {
  compile_list : call;
  compile_list_star : call;
  compile_list_of : forms;
  compile_vector_of : forms;
  compile_conj : call;
  compile_cons : call;
  compile_subvec : call;
  compile_nth : call;
  compile_get : call;
  compile_find : call;
  compile_assoc : call;
  compile_dissoc : call;
  compile_merge : call;
  compile_hash_map : call;
  compile_update : call;
  compile_select_keys : call;
  compile_contains : call;
  compile_keys : call;
  compile_vals : call;
}

let compile_args_for compile_expr scope env arg_forms =
  let rec loop acc = function
    | [] -> Ok (List.rev acc)
    | form :: rest -> (
        match compile_expr scope env form with
        | Ok expr -> loop (expr :: acc) rest
        | Error _ as err -> err)
  in
  loop [] arg_forms

let rec dynamicize_unknown = function
  | TUnknown | TMeta _ | TVar _ -> Types.dynamic_constraint TUnknown
  | TNullable ty -> TNullable (dynamicize_unknown ty)
  | TOcaml_app ("option", [ ty ]) ->
      TOcaml_app ("option", [ dynamicize_unknown ty ])
  | TOcaml_app (name, arguments) ->
      TOcaml_app (name, List.map dynamicize_unknown arguments)
  | TTuple items -> TTuple (List.map dynamicize_unknown items)
  | TArray ty -> TArray (dynamicize_unknown ty)
  | TRef ty -> TRef (dynamicize_unknown ty)
  | TList ty -> TList (dynamicize_unknown ty)
  | TVector ty -> TVector (dynamicize_unknown ty)
  | TSet ty -> TSet (dynamicize_unknown ty)
  | TSeq ty -> TSeq (dynamicize_unknown ty)
  | TRecord fields ->
      TRecord
        (List.map
           (fun (field : field) ->
             { field with ty = dynamicize_unknown field.ty })
           fields)
  | TFn (parameters, return_ty) ->
      TFn (List.map dynamicize_unknown parameters, dynamicize_unknown return_ty)
  | ty -> ty

let typed_dynamic_item_pattern env name = function
  | TRecord fields -> (
      match
        Env.find_anonymous_record
          ~owner:(Source_context.anonymous_record_owner "") fields env
      with
      | Some record ->
          Semantic_ir.PConstraint
            ( Semantic_ir.PVar name,
              Structural_map.record_type_application record )
      | None -> Semantic_ir.PTyped (Semantic_ir.PVar name, TRecord fields))
  | TNamed_record record ->
      Semantic_ir.PConstraint
        ( Semantic_ir.PVar name,
          Structural_map.record_type_application record )
  | _ -> Semantic_ir.PVar name

let runtime_map_operation key_ty operation =
  "Lg_runtime.Runtime_map." ^ operation
  ^
  if
    Types.is_dynamic key_ty || Types.equal key_ty TUnknown
  then "_dynamic"
  else if Option.is_some (Types.dynamic_map_types key_ty) then "_map_key"
  else ""

let runtime_map_key_type declared actual =
  if Types.equal actual TNil then TNil
  else if Types.equal declared TUnknown then actual
  else if
    Types.is_dynamic declared || Types.is_dynamic actual
  then
    Types.dynamic_constraint TUnknown
  else declared

let dissoc_map_key declared_ty map (key : typed_expr) =
  let dissoc key_ty key_expr =
    apply
      (runtime_map_operation
         (runtime_map_key_type declared_ty key_ty)
         "dissoc")
      [ map; key_expr ]
  in
  match key.ty with
  | TNullable payload_ty | TOcaml_app ("option", [ payload_ty ]) ->
      let key_name = "__lg_dissoc_key" in
      Semantic_ir.Match
        ( key.semantic_expr,
          [
            (Semantic_ir.PConstructor ("None", None), map);
            ( Semantic_ir.PConstructor
                ("Some", Some (Semantic_ir.PVar key_name)),
              dissoc payload_ty (Semantic_ir.Ident key_name) );
          ] )
  | key_ty -> dissoc key_ty key.semantic_expr

let create ~compile_expr ~pack_dynamic_value ~dynamic_unpack =
  let compile_args_for = compile_args_for compile_expr in
  let pack_dynamic_scalar env value =
    pack_dynamic_value env (Types.dynamic_constraint value.ty) value
  in
  let pack_regex_matcher_default env dynamic value =
    let convert name =
      Ok
        (Semantic_ir.Apply
           ( Semantic_ir.Ident ("Lg_runtime.Runtime_dynamic." ^ name),
             [ value.semantic_expr ] ))
    in
    if Types.is_dynamic value.ty then Ok value.semantic_expr
    else
      match Types.constraint_value_type value.ty with
      | TNil -> Ok (Semantic_ir.Ident "Lg_runtime.Runtime_dynamic.nil")
      | TInt | TOcaml "int" -> convert "int"
      | TFloat -> convert "float"
      | TChar -> convert "char"
      | TString -> convert "string"
      | TRegex -> convert "regex"
      | TSymbol -> convert "symbol"
      | TKeyword -> convert "keyword"
      | TBool -> convert "bool"
      | _ -> pack_dynamic_value env dynamic value
  in
  let rec pack_closed_edn_value value =
    let expression = value.semantic_expr in
    let convert name =
      Ok
        (Semantic_ir.Apply
           ( Semantic_ir.Ident ("Lg_runtime.Runtime_metadata." ^ name),
             [ expression ] ))
    in
    match Types.constraint_value_type value.ty with
    | TOcaml "Lg_edn_backend.t" -> Ok expression
    | TNil ->
        Ok
          (Semantic_ir.Sequence
             [ expression; Semantic_ir.Ident "Lg_runtime.Runtime_metadata.nil" ])
    | TBool -> convert "of_bool"
    | TInt | TOcaml "int" -> convert "of_int"
    | TFloat -> convert "of_float"
    | TChar -> convert "of_char"
    | TString -> convert "of_string"
    | TSymbol -> convert "of_symbol"
    | TKeyword -> convert "of_keyword"
    | TRegex -> convert "of_regex"
    | TVector inner ->
        let value_name = "__lg_contains_edn_vector_value" in
        let item = typed_ir inner (Semantic_ir.Ident value_name) in
        Result.map
          (fun packed ->
            Semantic_ir.Apply
              ( Semantic_ir.Ident "Lg_runtime.Runtime_metadata.of_vector",
                [
                  Semantic_ir.Fun ([ Semantic_ir.PVar value_name ], packed);
                  expression;
                ] ))
          (pack_closed_edn_value item)
    | TNullable inner | TOcaml_app ("option", [ inner ]) ->
        let value_name = "__lg_contains_edn_optional_value" in
        let item = typed_ir inner (Semantic_ir.Ident value_name) in
        Result.map
          (fun packed ->
            Semantic_ir.Match
              ( expression,
                [
                  ( Semantic_ir.PConstructor ("None", None),
                    Semantic_ir.Ident "Lg_runtime.Runtime_metadata.nil" );
                  ( Semantic_ir.PConstructor
                      ("Some", Some (Semantic_ir.PVar value_name)),
                    packed );
                ] ))
          (pack_closed_edn_value item)
    | _ -> Error.error ~code:Error_code.Semantic "contains? EDN key must be closed EDN-compatible"
  in
  let inferred_field_type env keyword =
    let candidates =
      Env.fold
        (fun _ binding candidates ->
          match binding.ty with
          | TNamed_record { fields; _ } -> (
              match find_field keyword fields with
              | Some field
                when not (List.exists (Types.equal field.ty) candidates) ->
                  field.ty :: candidates
              | Some _ | None -> candidates)
          | _ -> candidates)
        env []
    in
    match candidates with [ ty ] -> Some ty | _ -> None
  in
  let inferred_record_type env keyword =
    let candidates =
      Env.fold
        (fun _ binding candidates ->
          match binding.ty with
          | TNamed_record ({ fields; _ } as record) -> (
              match find_field keyword fields with
              | Some _ ->
                  let ty = TNamed_record record in
                  if List.exists (Types.equal ty) candidates then candidates
                  else ty :: candidates
              | None -> candidates)
          | _ -> candidates)
        env []
    in
    match candidates with [ ty ] -> Some ty | _ -> None
  in
  let expected_record_type env keyword =
    match Env.expected_type env with
    | Some expected
      when not
             (Types.equal expected TUnknown
             || match expected with TVar _ -> true | _ -> false) ->
        Some (TRecord [ make_map_field keyword expected ])
    | Some _ | None -> None
  in
  let contextual_field_type env field_ty =
    let field_ty = clj_function_type field_ty in
    match (field_ty, Env.expected_type env) with
    | (TUnknown | TMeta _), Some expected
      when not
             (Types.equal expected TUnknown
             || match expected with TVar _ -> true | _ -> false) ->
        expected
    | _ -> field_ty
  in
  let external_record_type = function
    | TOcaml type_name -> (
        match Ocaml_signature.record_type type_name with
        | Ok (TNamed_record record) -> Some record
        | Ok _ | Error _ -> None)
    | TOcaml_app (type_name, arguments) -> (
        match Ocaml_signature.record_type type_name with
        | Ok (TNamed_record record)
          when List.length record.type_parameters = List.length arguments ->
            Some { record with type_arguments = arguments }
        | Ok _ | Error _ -> None)
    | _ -> None
  in
  let external_field type_name target keyword =
    let field_name = Names.keyword_to_ocaml_name keyword in
    let field_expr = Semantic_ir.Field (target.semantic_expr, field_name) in
    match Ocaml_signature.field_type type_name field_name with
    | Ok (TOcaml "int") ->
        typed_ir TInt field_expr
    | Ok field_ty -> typed_ir (clj_function_type field_ty) field_expr
    | Error _ -> typed_ir TUnknown field_expr
  in
  let instantiated_record_field scope env type_name arguments keyword =
    let type_name =
      let prefixes = [ "__lg_record_app:"; "__lg_record:" ] in
      prefixes
      |> List.find_map (fun prefix ->
             if String.starts_with ~prefix type_name then
               Some
                 (String.sub type_name (String.length prefix)
                    (String.length type_name - String.length prefix))
             else None)
      |> Option.value ~default:type_name
    in
    match Resolver.lookup_record_type scope env type_name with
    | Ok record
      when List.length record.type_parameters = List.length arguments -> (
        match find_field keyword record.fields with
        | None -> None
        | Some field ->
            let substitutions =
              List.combine record.type_parameters arguments
              |> List.map (fun (parameter, argument) ->
                     (Type_solver.Declared parameter, argument))
              |> Type_solver.of_list
            in
            let field =
              {
                field with
                ty = Types.substitute_type_variables substitutions field.ty;
              }
            in
            Some
              ( { record with type_arguments = arguments },
                field ))
    | Ok _ | Error _ -> None
  in
  let resolve_keyword_alias scope env = function
    | FSymbol name as form -> (
        match lookup_binding scope env name with
        | Ok { constant_keyword = Some keyword; _ } -> FKeyword keyword
        | Ok _ | Error _ -> form)
    | form -> form
  in
  let unwrap_protocol_value value =
    let rec unwrap ty expression =
      match Types.contains_constraint_info ty with
      | Some (_, value_ty) ->
          let expression =
            match Semantic_ir.unlocated expression with
            | Semantic_ir.Ident _ -> expression
            | _ ->
                Semantic_ir.Apply (Semantic_ir.Ident "snd", [ expression ])
          in
          unwrap value_ty expression
      | None -> (
          match Types.protocol_constraint_info ty with
          | None -> (ty, expression)
          | Some (_, _, value_ty) ->
              let expression =
                match Semantic_ir.unlocated expression with
                | Semantic_ir.Ident _ -> expression
                | _ ->
                    Semantic_ir.Apply
                      (Semantic_ir.Ident "snd", [ expression ])
              in
              unwrap value_ty expression)
    in
    let ty, semantic_expr = unwrap value.ty value.semantic_expr in
    { value with ty; semantic_expr }
  in
  let unwrap_protocol_constraints value =
    let rec unwrap ty expression =
      match Types.protocol_constraint_info ty with
      | Some (_, _, value_ty) ->
          let expression =
            match Semantic_ir.unlocated expression with
            | Semantic_ir.Ident _ -> expression
            | _ ->
                Semantic_ir.Apply (Semantic_ir.Ident "snd", [ expression ])
          in
          unwrap value_ty expression
      | None -> (ty, expression)
    in
    let ty, semantic_expr = unwrap value.ty value.semantic_expr in
    { value with ty; semantic_expr }
  in
  let dynamic_constraint_value value =
    let rec unwrap ty expression =
      match Types.protocol_constraint_info ty with
      | Some (_, _, value_ty) ->
          unwrap value_ty
            (Semantic_ir.Apply (Semantic_ir.Ident "snd", [ expression ]))
      | None -> (
          match Types.seqable_constraint_info ty with
          | Some (_, _, value_ty) ->
              unwrap value_ty
                (Semantic_ir.Apply (Semantic_ir.Ident "snd", [ expression ]))
          | None -> expression)
    in
    match Semantic_ir.unlocated value.semantic_expr with
    | Semantic_ir.Ident _ -> value.semantic_expr
    | _ -> unwrap value.ty value.semantic_expr
  in
  let special_forms : Special_form_elaborator.t =
    Special_form_elaborator.create ~compile_expr ~dynamic_unpack
      ~pack_dynamic_value
      ~pack_constrained_value:(fun _env _expected argument ->
        Ok argument.semantic_expr)
      ~argument_compatible:(fun expected actual ->
        Types.assignable ~policy:Host_boundary ~expected ~actual)
  in
  let compile_body = special_forms.compile_body in
  let compile_map = special_forms.compile_map in
  let compile_function_arg scope env = function
    | FSymbol name -> lookup_function scope env name
    | form -> compile_expr scope env form
  in
  let updater_value_type target value_ty =
    match Types.dynamic_map_types target.ty with
    | Some _ -> TNullable value_ty
    | None -> value_ty
  in
  let core_function_symbol scope env name member =
    match
      ( lookup_binding scope env name,
        lookup_binding scope env ("clojure.core/" ^ member) )
    with
    | Ok binding, Ok core_binding -> binding.ocaml_name = core_binding.ocaml_name
    | _ -> false
  in
  let compile_function_arg_for_value scope env value_ty extra_tys form =
    let env = Env.with_expected_type None env in
    let parameter_tys = value_ty :: extra_tys in
    let compile_contextual_call () =
      let parameter_names =
        List.mapi
          (fun index _ -> "__lg_update_arg_" ^ string_of_int index)
          parameter_tys
      in
      let params =
        FVector (List.map (fun name -> FSymbol name) parameter_names)
      in
      let body =
        FList (form :: List.map (fun name -> FSymbol name) parameter_names)
      in
      let lookup_function_ty name =
        match lookup_function scope env name with
        | Ok fn -> Ok fn.ty
        | Error _ as error -> error
      in
      let compile_default expected form =
        compile_expr scope (Env.with_expected_type (Some expected) env) form
      in
      Function_elaborator.prepare
        ~param_type_overrides:(List.map (fun ty -> Some ty) parameter_tys)
        ~compile_default ~lookup_function_ty ~compile_body scope env params
        [ body ]
      |> Result.map Function_elaborator.fn_code
    in
    let compile_identity () =
      match extra_tys with
      | [] ->
          let argument = "__lg_update_identity_arg" in
          Ok
            (typed_ir (TFn ([ value_ty ], value_ty))
               (Semantic_ir.Fun
                  ([ Semantic_ir.PVar argument ], Semantic_ir.Ident argument)))
      | _ -> compile_contextual_call ()
    in
    match form with
    | FList (FSymbol "fn" :: (FVector _ as params) :: body_forms) ->
        let lookup_function_ty name =
          match lookup_function scope env name with
          | Ok fn -> Ok fn.ty
          | Error _ as error -> error
        in
        let compile_default expected form =
          compile_expr scope (Env.with_expected_type (Some expected) env) form
        in
        Function_elaborator.prepare
          ~param_type_overrides:(List.map (fun ty -> Some ty) parameter_tys)
          ~compile_default ~lookup_function_ty ~compile_body scope env params
          body_forms
        |> Result.map (fun parts ->
               let fn = Function_elaborator.fn_code parts in
               {
                 fn with
                 semantic_expr =
                   constrain_record_function_argument_expr fn value_ty;
               })
    | FSymbol name when core_function_symbol scope env name "identity" ->
        compile_identity ()
    | FSymbol name
      when core_function_symbol scope env name "transient"
           || core_function_symbol scope env name "persistent!" ->
        compile_contextual_call ()
    | FSymbol _ -> (
        match compile_function_arg scope env form with
        | Ok ({ ty = TFn _; _ } as fn) -> Ok fn
        | Ok _ | Error _ -> compile_contextual_call ())
    | FList _ -> compile_contextual_call ()
    | _ -> compile_function_arg scope env form
  in
  let compile_deftype_method scope env record method_name args =
    match
      lookup_deftype_method scope env record method_name (List.length args)
    with
    | Error _ -> (
        match
          Protocol.lookup_unique_method_impl env method_name
            (TNamed_record record)
        with
        | None -> None
        | Some binding ->
            let binding = Types.instantiate_binding binding in
            let binding =
              match binding.ty with
              | TOverloaded_fn arities ->
                  arities
                  |> List.mapi (fun index arity -> (index, arity))
                  |> List.find_opt (fun (_, arity) ->
                         Option.is_none arity.rest_param
                         && List.length arity.fixed_params = List.length args)
                  |> Option.map (fun (index, arity) ->
                         {
                           binding with
                           ocaml_name =
                             List.nth_opt binding.overload_targets index
                             |> Option.value ~default:binding.ocaml_name;
                           ty = TFn (arity.fixed_params, arity.return_ty);
                         })
                  |> Option.value ~default:binding
              | _ -> binding
            in
            (match binding.ty with
            | TFn (parameter_tys, return_ty)
              when List.length parameter_tys = List.length args ->
                Some
                  (typed_ir return_ty
                     (Semantic_ir.Apply
                        ( Semantic_ir.Ident binding.ocaml_name,
                          List.map (fun arg -> arg.semantic_expr) args )))
            | _ -> None))
    | Ok binding -> (
        match binding.ty with
          | TFn (parameter_tys, return_ty)
            when List.length parameter_tys = List.length args ->
              let rec prepare prepared parameter_tys args =
                match (parameter_tys, args) with
                | [], [] -> Some (List.rev prepared)
                | expected :: parameter_tys, argument :: args ->
                    let prepared_argument =
                      if
                        (Types.equal expected TUnknown
                        || match expected with TVar _ -> true | _ -> false)
                        && Types.equal argument.ty TNil
                        &&
                      match return_ty with
                        | TNullable _ | TOcaml_app ("option", [ _ ]) -> true
                      | _ -> false
                      then Some (argument.semantic_expr, argument.ty)
                      else if
                        Types.is_dynamic expected
                        || Types.equal expected TUnknown
                        || match expected with TVar _ -> true | _ -> false
                      then
                        Option.map
                          (fun expression ->
                          (expression, Types.dynamic_constraint TUnknown))
                          (pack_plain_dynamic_value argument)
                      else Some (argument.semantic_expr, argument.ty)
                    in
                    Option.bind prepared_argument (fun argument ->
                        prepare (argument :: prepared) parameter_tys args)
                | _ -> None
              in
              Option.map
                (fun prepared ->
                  let arguments = List.map fst prepared in
                  let actual_tys = List.map snd prepared in
                  let return_ty =
                    Types.instantiate_type ~templates:parameter_tys
                      ~actuals:actual_tys return_ty
                  in
                  let crossed_dynamic_boundary =
                    List.exists2
                      (fun expected actual ->
                        (Types.equal expected TUnknown
                        || match expected with TVar _ -> true | _ -> false)
                        && Types.is_dynamic actual)
                      parameter_tys actual_tys
                  in
                  let return_ty =
                    if crossed_dynamic_boundary then dynamicize_unknown return_ty
                    else
                      match Types.dynamic_constraint_info return_ty with
                      | Some capability
                        when not (Types.equal capability TUnknown) ->
                          capability
                      | Some _ | None -> return_ty
                  in
                  typed_ir return_ty
                    (Semantic_ir.Apply
                       (Semantic_ir.Ident binding.ocaml_name, arguments)))
                (prepare [] parameter_tys args)
          | _ -> None)
    in
    let rec compile_list scope env forms =
      match forms with
      | [] -> Ok (typed_ir (TList TUnknown) (Semantic_ir.List []))
      | first :: rest -> (
          match compile_expr scope env first with
          | Error _ as err -> err
          | Ok first_expr ->
              let rec loop acc = function
                | [] ->
                    let values = List.rev acc in
                    (match merge_collection_value_types "list" values with
                    | Ok element_ty ->
                        Ok
                          (typed_ir (TList element_ty)
                             (Semantic_ir.List
                                (List.map
                                   (fun value ->
                                     coerce_expression_to_type element_ty
                                       value.ty value.semantic_expr)
                                   values)))
                    | Error _ as error ->
                        let rec pack packed = function
                          | [] ->
                              Ok
                                (typed_ir
                                   (TList Edn_value_elaborator.value_ty)
                                   (Semantic_ir.List (List.rev packed)))
                          | value :: rest ->
                              Result.bind
                                (Edn_value_elaborator.pack_expression value.ty
                                   value.semantic_expr)
                                (fun packed_value ->
                                  pack (packed_value :: packed) rest)
                        in
                        (match pack [] values with
                        | Ok _ as packed -> packed
                        | Error _ -> error))
                | form :: rest -> (
                    match compile_expr scope env form with
                    | Error _ as err -> err
                    | Ok expr -> loop (expr :: acc) rest)
              in
              loop [ first_expr ] rest)
    and compile_list_star scope env arg_forms =
      match compile_args_for scope env arg_forms with
      | Error _ as error -> error
      | Ok [] -> Error.error ~code:Error_code.Arity "list* expects values and final collection"
      | Ok args ->
          let final_index = List.length args - 1 in
          let compiled_args =
            List.mapi
              (fun index arg ->
                let arg =
                  if index <> final_index then arg
                  else
                    match Core_sequence_transform.collection_to_list_expr arg with
                    | Ok _ -> arg
                    | Error _ -> (
                        match Collection_capability.to_seq_expr env arg with
                        | Ok (inner, sequence) -> typed_ir (TSeq inner) sequence
                        | Error _ -> arg)
                in
                let name = "__lg_list_star_argument_" ^ string_of_int index in
                ( Semantic_ir.PVar name,
                  arg.semantic_expr,
                  typed_ir arg.ty (Semantic_ir.Ident name) ))
              args
          in
          let values = List.map (fun (_, _, value) -> value) compiled_args in
          let final, prefix =
            match List.rev values with
            | final :: reversed_prefix -> (final, List.rev reversed_prefix)
            | [] -> assert false
          in
          match Core_sequence_transform.collection_to_list_expr final with
          | Error _ -> Error.error ~code:Error_code.Arity "list* final argument must be a collection"
          | Ok (inner, final_list) ->
              if
                not
                  (List.for_all
                     (fun argument -> Types.equal inner argument.ty)
                     prefix)
              then
                Error.error ~code:Error_code.Semantic
                  ("list* prefix and final collection must have one static element type; tail element is "
                   ^ Types.source_name inner ^ ", prefix elements are "
                   ^ String.concat ", " (List.map (fun arg -> Types.source_name arg.ty) prefix))
              else
                let argument_bindings =
                  List.map
                    (fun (pattern, expression, _) -> (pattern, expression))
                    compiled_args
                in
                match prefix with
                | [] ->
                    let values_name = "__lg_list_star_values" in
                    let result =
                      Semantic_ir.Match
                        ( final_list,
                          [
                            ( Semantic_ir.PList [],
                              Semantic_ir.Constructor ("None", None) );
                            ( Semantic_ir.PVar values_name,
                              Semantic_ir.Constructor
                                ( "Some",
                                  Some (Semantic_ir.Ident values_name) ) );
                          ] )
                    in
                    Ok
                      (typed_ir (TNullable (TList inner))
                         (Semantic_ir.Let (argument_bindings, result)))
                | _ ->
                    let result =
                      Semantic_ir.Infix
                        ( "@",
                          Semantic_ir.List
                            (List.map
                               (fun argument -> argument.semantic_expr)
                               prefix),
                          final_list )
                    in
                    Ok
                      (typed_ir (TList inner)
                         (Semantic_ir.Let (argument_bindings, result)))
    and compile_list_of arg_forms =
      match arg_forms with
      | [ FKeyword keyword ] -> (
          match Type_annotation.of_keyword keyword with
          | Error _ as err -> err
        | Ok element_ty ->
            Ok (typed_ir (TList element_ty) (Semantic_ir.List [])))
      | _ -> Error.error ~code:Error_code.Arity "list-of expects one type keyword"
    and compile_vector_of arg_forms =
      match arg_forms with
      | [ FKeyword keyword ] -> (
          match Type_annotation.of_keyword keyword with
          | Error _ as err -> err
          | Ok element_ty ->
            Ok
              (typed_ir (TVector element_ty) (Semantic_ir.Ident "Rrbvec.empty"))
        )
      | _ -> Error.error ~code:Error_code.Arity "vector-of expects one type keyword"
    and compile_conj scope env arg_forms =
      let map_entry = function
        | FList [ FSymbol "tuple"; key; value ]
        | FList [ FSymbol "__lg_vector"; key; value ]
        | FVector [ key; value ] ->
            Some [ (key, value) ]
        | FMap entries -> Some entries
        | _ -> None
      in
      let expand_map_conj collection entries =
        List.fold_left
          (fun expanded entry ->
            match map_entry entry with
            | Some pairs ->
                List.fold_left
                  (fun expanded (key, value) ->
                    FList [ FSymbol "__lg_assoc"; expanded; key; value ])
                  expanded pairs
            | None -> expanded)
          collection entries
      in
      let expand_protocol_conj collection values =
        List.fold_left
          (fun expanded value ->
            FList [ FSymbol "ICollection/-conj"; expanded; value ])
          collection values
      in
      let compile_builtin () =
        match arg_forms with
        | collection_form :: (_ :: _ as entry_forms)
          when
            List.for_all
              (fun entry -> Option.is_some (map_entry entry))
              entry_forms
          -> (
            match compile_expr scope env collection_form with
            | Ok collection
              when
                (match Types.constraint_value_type collection.ty with
                | TRecord _ | TNamed_record { nominal = false; _ } -> true
                | ty -> Option.is_some (Types.dynamic_map_types ty)) ->
                compile_expr scope env
                  (expand_map_conj collection_form entry_forms)
            | Ok _ | Error _ -> compile_conj_values scope env arg_forms)
        | _ -> compile_conj_values scope env arg_forms
      in
      match arg_forms with
      | collection_form :: (_ :: _ as values) -> (
          match compile_expr scope env collection_form with
          | Ok
              {
                ty = TNamed_record { nominal = true; _ };
                _;
              } ->
              compile_expr scope env
                (expand_protocol_conj collection_form values)
          | Ok _ | Error _ -> compile_builtin ())
      | _ -> compile_builtin ()
    and compile_conj_values scope env arg_forms =
      match
        compile_args_for scope (Env.with_expected_type None env) arg_forms
      with
      | Error _ as err -> err
      | Ok (collection :: values) when values <> [] ->
          let add_value collection value =
            let value = unwrap_protocol_value value in
            match collection.ty with
            | ty when Types.is_dynamic ty ->
                Error.error ~code:Error_code.Semantic
                  "conj requires a statically typed collection; define a sum \
                   type for heterogeneous elements"
            | TNil ->
                Ok
                  (typed_ir (TList value.ty)
                     (Semantic_ir.List [ value.semantic_expr ]))
            | TList (TUnknown | TMeta _ | TVar _) ->
                Ok
                  (typed_ir (TList value.ty)
                     (Semantic_ir.Cons
                        (value.semantic_expr, collection.semantic_expr)))
            | TList inner when Types.equal inner value.ty ->
                Ok
                  (typed_ir collection.ty
                   (Semantic_ir.Cons
                      (value.semantic_expr, collection.semantic_expr)))
            | TList inner when Edn_value_elaborator.is_value_type inner ->
                Result.map
                  (fun packed ->
                    typed_ir collection.ty
                      (Semantic_ir.Cons
                         (packed, collection.semantic_expr)))
                  (Edn_value_elaborator.pack_expression value.ty
                     value.semantic_expr)
            | TList inner -> (
                match
                  ( Edn_value_elaborator.mapper inner,
                    Edn_value_elaborator.pack_expression value.ty
                      value.semantic_expr )
                with
                | Ok pack_existing, Ok packed ->
                    Ok
                      (typed_ir (TList Edn_value_elaborator.value_ty)
                         (Semantic_ir.Cons
                            ( packed,
                              Semantic_ir.Apply
                                ( Semantic_ir.Ident "List.map",
                                  [ pack_existing; collection.semantic_expr ] ) )))
                | Error _, _ | _, Error _ ->
                    heterogeneous_collection_type_error "list"
                      [ inner; value.ty ])
            | TSeq (TUnknown | TMeta _ | TVar _) ->
                Ok
                  (typed_ir (TSeq value.ty)
                     (Semantic_ir.Apply
                        ( Semantic_ir.Ident "Seq.cons",
                          [ value.semantic_expr; collection.semantic_expr ] )))
            | TSeq inner when Types.same_shape inner value.ty ->
                let value = coerce_expression_to_type inner value.ty value.semantic_expr in
                Ok
                  (typed_ir collection.ty
                     (Semantic_ir.Apply
                        ( Semantic_ir.Ident "Seq.cons",
                          [ value; collection.semantic_expr ] )))
            | TSeq inner ->
                heterogeneous_collection_type_error "sequence"
                  [ inner; value.ty ]
            | TOcaml_app (name, [ inner ])
              when Types.is_next_seq_type_name name ->
                if Types.same_shape inner value.ty then
                  let value =
                    coerce_expression_to_type inner value.ty value.semantic_expr
                  in
                  Ok
                    (typed_ir (TSeq inner)
                       (Semantic_ir.Apply
                          ( Semantic_ir.Ident "Seq.cons",
                            [ value; collection.semantic_expr ] )))
                else
                  heterogeneous_collection_type_error "sequence"
                    [ inner; value.ty ]
            | TVector (TUnknown | TMeta _ | TVar _) ->
                Ok
                  (typed_ir (TVector value.ty)
                     (Semantic_ir.Apply
                        ( Semantic_ir.Ident "Rrbvec.push_back",
                          [ collection.semantic_expr; value.semantic_expr ] )))
            | TVector inner when Types.equal inner value.ty ->
                Ok
                  (typed_ir collection.ty
                     (Semantic_ir.Apply
                        ( Semantic_ir.Ident "Rrbvec.push_back",
                          [ collection.semantic_expr; value.semantic_expr ] )))
            | TVector inner when Types.same_shape inner value.ty ->
                let value =
                  coerce_expression_to_type inner value.ty value.semantic_expr
                in
                Ok
                  (typed_ir collection.ty
                     (Semantic_ir.Apply
                        ( Semantic_ir.Ident "Rrbvec.push_back",
                          [ collection.semantic_expr; value ] )))
            | TVector inner when Edn_value_elaborator.is_value_type inner ->
                Result.map
                  (fun packed ->
                    typed_ir collection.ty
                      (Semantic_ir.Apply
                         ( Semantic_ir.Ident "Rrbvec.push_back",
                           [ collection.semantic_expr; packed ] )))
                  (Edn_value_elaborator.pack_expression value.ty
                     value.semantic_expr)
            | TVector
                ((TNullable target_inner
                 | TOcaml_app ("option", [ target_inner ])) as inner)
              when (match value.ty with
                   | TNullable _ | TOcaml_app ("option", [ _ ]) -> false
                   | _ -> true)
                   && (Types.is_dynamic target_inner
                      || Types.assignable ~policy:Host_boundary
                           ~expected:target_inner ~actual:value.ty) ->
                let value =
                  if Types.is_dynamic target_inner then
                    pack_dynamic_value env target_inner value
                  else
                    Ok
                      (coerce_expression_to_type target_inner value.ty
                         value.semantic_expr)
                in
                Result.map
                  (fun value ->
                    typed_ir (TVector inner)
                      (Semantic_ir.Apply
                         ( Semantic_ir.Ident "Rrbvec.push_back",
                           [ collection.semantic_expr;
                             Semantic_ir.Constructor ("Some", Some value);
                           ] )))
                  value
            | TVector inner when Types.equal value.ty TNil ->
                let item_name = "__lg_conj_vector_item" in
                let optionalized =
                  Semantic_ir.Apply
                    ( Semantic_ir.Ident "Rrbvec.map",
                      [
                        Semantic_ir.Fun
                          ( [ Semantic_ir.PVar item_name ],
                            Semantic_ir.Constructor
                              ( "Some",
                                Some (Semantic_ir.Ident item_name) ) );
                        collection.semantic_expr;
                      ] )
                in
                Ok
                  (typed_ir (TVector (TNullable inner))
                     (Semantic_ir.Apply
                        ( Semantic_ir.Ident "Rrbvec.push_back",
                          [
                            optionalized;
                            Semantic_ir.Constructor ("None", None);
                          ] )))
            | TVector inner -> (
                match
                  ( Edn_value_elaborator.mapper inner,
                    Edn_value_elaborator.pack_expression value.ty
                      value.semantic_expr )
                with
                | Ok pack_existing, Ok packed ->
                    Ok
                      (typed_ir (TVector Edn_value_elaborator.value_ty)
                         (Semantic_ir.Apply
                            ( Semantic_ir.Ident "Rrbvec.push_back",
                              [
                                Semantic_ir.Apply
                                  ( Semantic_ir.Ident "Rrbvec.map",
                                    [ pack_existing; collection.semantic_expr ] );
                                packed;
                              ] )))
                | Error _, _ | _, Error _ ->
                    heterogeneous_collection_type_error "vector"
                      [ inner; value.ty ])
            | TSet (TUnknown | TMeta _ | TVar _) ->
                let value_ty = value.ty in
                Result.bind (set_module_name env value_ty) (fun set_module ->
                    Result.map
                      (fun value ->
                        typed_ir (TSet value_ty)
                          (Semantic_ir.Apply
                             ( Semantic_ir.Ident (set_module ^ ".of_list"),
                               [
                                 Semantic_ir.Cons
                                   ( value,
                                     Semantic_ir.Apply
                                       ( Semantic_ir.Ident
                                           "Lg_runtime.Runtime_poly_set.elements",
                                         [ collection.semantic_expr ] ) );
                               ] )))
                      (coerce_set_element value_ty value))
            | TSet inner when Types.same_shape inner value.ty ->
                Result.bind (set_module_name env inner) (fun set_module ->
                       coerce_set_element inner value
                       |> Result.map (fun value ->
                              typed_ir collection.ty
                                (Semantic_ir.Apply
                                   ( Semantic_ir.Ident (set_module ^ ".add"),
                                     [ value; collection.semantic_expr ] ))))
            | TSet inner ->
                heterogeneous_collection_type_error "set" [ inner; value.ty ]
            | TMeta _ | TVar _ ->
                Error.error ~code:Error_code.Semantic
                  "conj cannot infer a concrete static collection element \
                   type; define a closed sum type containing every alternative \
                   when the collection is heterogeneous"
            | _ ->
                Error.error ~code:Error_code.Arity
                  ("conj expects a list, vector, set, or sequence, got "
                 ^ Types.source_name collection.ty)
          in
          values
          |> List.fold_left
               (fun acc value ->
                 match acc with
                 | Error _ as err -> err
                 | Ok collection -> add_value collection value)
               (Ok collection)
      | Ok _ -> Error.error ~code:Error_code.Arity "conj expects collection and values"
    and compile_cons scope env arg_forms =
      match compile_args_for scope env arg_forms with
      | Error _ as err -> err
      | Ok [ value; collection ] -> (
          match Collection_capability.to_seq_expr env collection with
          | Ok (inner, sequence) when Types.same_shape inner value.ty ->
              Ok
                (typed_ir (TSeq inner)
                   (Semantic_ir.Apply
                      ( Semantic_ir.Ident "Seq.cons",
                        [ value.semantic_expr; sequence ] )))
          | Ok (inner, _) ->
              heterogeneous_collection_type_error "sequence"
                [ inner; value.ty ]
          | Error _ ->
              Error.error ~code:Error_code.Arity
                ("cons expects a value and seqable collection, got "
               ^ Types.source_name collection.ty))
      | Ok _ -> Error.error ~code:Error_code.Arity "cons expects a value and seqable collection"
    and compile_subvec scope env arg_forms =
      let host_int expression = expression in
      let uses_dynamic_storage ty =
        Types.is_dynamic ty || Types.equal ty TUnknown
        || match ty with TVar _ -> true | _ -> false
      in
      let dynamic = Types.dynamic_constraint TUnknown in
      match compile_args_for scope env arg_forms with
      | Error _ as err -> err
      | Ok [ vector; start ] -> (
          match (vector.ty, start.ty) with
          | TVector _, TInt ->
              Ok
                (typed_ir vector.ty
                   (Semantic_ir.Apply
                      ( Semantic_ir.Ident "Option.get",
                      [
                        Semantic_ir.Apply
                            ( Semantic_ir.Ident "Rrbvec.subvec",
                            [
                              vector.semantic_expr;
                                host_int start.semantic_expr;
                                Semantic_ir.Apply
                                ( Semantic_ir.Ident "Rrbvec.length",
                                [ vector.semantic_expr ] );
                            ] );
                      ] )))
          | vector_ty, TInt when uses_dynamic_storage vector_ty ->
              Ok
                (typed_ir dynamic
                   (Semantic_ir.Apply
                      ( Semantic_ir.Ident
                          "Lg_runtime.Runtime_dynamic.subvec_value",
                        [ vector.semantic_expr;
                          host_int start.semantic_expr;
                          Semantic_ir.Apply
                            ( Semantic_ir.Ident
                                "Lg_runtime.Runtime_dynamic.count_value",
                              [ vector.semantic_expr ] );
                        ] )))
          | TVector _, _ -> Error.error ~code:Error_code.Semantic "subvec indexes must be int"
          | _ -> Error.error ~code:Error_code.Arity "subvec expects a vector")
      | Ok [ vector; start; stop ] -> (
          match (vector.ty, start.ty, stop.ty) with
          | TVector _, TInt, TInt ->
              Ok
                (typed_ir vector.ty
                   (Semantic_ir.Apply
                      ( Semantic_ir.Ident "Option.get",
                      [
                        Semantic_ir.Apply
                            ( Semantic_ir.Ident "Rrbvec.subvec",
                            [
                              vector.semantic_expr;
                              host_int start.semantic_expr;
                              host_int stop.semantic_expr;
                            ] );
                      ] )))
          | vector_ty, TInt, TInt when uses_dynamic_storage vector_ty ->
              Ok
                (typed_ir dynamic
                   (Semantic_ir.Apply
                      ( Semantic_ir.Ident
                          "Lg_runtime.Runtime_dynamic.subvec_value",
                        [ vector.semantic_expr;
                          host_int start.semantic_expr;
                          host_int stop.semantic_expr;
                        ] )))
          | TVector _, _, _ -> Error.error ~code:Error_code.Semantic "subvec indexes must be int"
          | _ -> Error.error ~code:Error_code.Arity "subvec expects a vector")
      | Ok _ -> Error.error ~code:Error_code.Arity "subvec expects vector, start, and optional stop"
    and compile_nth scope env arg_forms =
      let expected_result = Env.expected_type env in
      let collection_env =
        match expected_result with
        | Some expected ->
            Env.with_expected_type
              (Some (Types.seqable_constraint expected))
              env
        | None -> Env.with_expected_type None env
      in
      let index_env = Env.with_expected_type (Some TInt) env in
      let default_env = Env.with_expected_type expected_result env in
      let compile_nth_args = function
        | [ collection_form; index_form ] ->
            Result.bind
              (compile_expr scope collection_env collection_form)
              (fun collection ->
                Result.map
                  (fun index -> [ collection; index ])
                  (compile_expr scope index_env index_form))
        | [ collection_form; index_form; default_form ] ->
            Result.bind
              (compile_expr scope collection_env collection_form)
              (fun collection ->
                Result.bind
                  (compile_expr scope index_env index_form)
                  (fun index ->
                    Result.map
                      (fun default -> [ collection; index; default ])
                      (compile_expr scope default_env default_form)))
        | forms -> compile_args_for scope env forms
      in
      let int_index index =
        if Types.equal index.ty TInt then Ok index
        else if
          Types.equal index.ty TUnknown
          || match index.ty with TVar _ -> true | _ -> false
        then Ok (typed_ir TInt index.semantic_expr)
        else if Types.is_dynamic index.ty then
          Result.map
            (fun semantic_expr -> typed_ir TInt semantic_expr)
            (dynamic_unpack env TInt index.semantic_expr)
        else
          Error.error ~code:Error_code.Semantic
            ("nth index must be int, got " ^ Types.source_name index.ty)
      in
      match compile_nth_args arg_forms with
      | Error _ as err -> err
      | Ok [ collection; index ] ->
          Result.bind (int_index index) (fun index ->
              match Collection_capability.nth_expr env collection index with
              | Ok _ as result -> result
              | Error _ ->
                  compile_expr scope env
                    (FList (FSymbol "IIndexed/-nth" :: arg_forms)))
      | Ok [ collection; index; default ] ->
          Result.bind (int_index index) (fun index ->
            if
              Types.equal collection.ty
                (TOcaml "Lg_runtime.Runtime_string.regex_matcher")
            then
              let dynamic = Types.dynamic_constraint TUnknown in
              Result.map
                (fun default ->
                  typed_ir dynamic
                    (Semantic_ir.Match
                       ( Semantic_ir.Apply
                           ( Semantic_ir.Ident
                               "Lg_runtime.Runtime_string.regex_matcher_nth_opt",
                             [
                               collection.semantic_expr;
                               index.semantic_expr;
                             ] ),
                         [
                           ( Semantic_ir.PConstructor
                               ( "Some",
                                 Some (Semantic_ir.PVar "__lg_regex_group") ),
                             Semantic_ir.Apply
                               ( Semantic_ir.Ident
                                   "Lg_runtime.Runtime_dynamic.regex_group",
                                 [ Semantic_ir.Ident "__lg_regex_group" ] ) );
                           ( Semantic_ir.PConstructor ("None", None),
                             default );
                         ] )))
                (pack_regex_matcher_default env dynamic default)
            else if match collection.ty with TSet _ -> true | _ -> false then
              compile_expr scope env
                (FList (FSymbol "IIndexed/-nth" :: arg_forms))
            else
              match Collection_capability.to_seq_expr env collection with
              | Error _ ->
                compile_expr scope env
                  (FList (FSymbol "IIndexed/-nth" :: arg_forms))
              | Ok (inner, sequence) ->
                  if not (Types.equal inner default.ty) then
                    if
                      Type_solver.is_open inner
                      && Edn_value_elaborator.is_provably_empty_collection
                           collection.ty collection.semantic_expr
                    then
                      Result.map
                        (fun packed_default ->
                          typed_ir Edn_value_elaborator.value_ty
                            (Semantic_ir.Sequence
                               [
                                 collection.semantic_expr;
                                 index.semantic_expr;
                                 packed_default;
                               ]))
                        (Edn_value_elaborator.pack_expression default.ty
                           default.semantic_expr)
                    else
                      Error.error ~code:Error_code.Semantic
                        "nth default must match collection element type"
                  else
                    Ok
                      (typed_ir inner
                         (Semantic_ir.Match
                            ( apply "Lg_runtime.Runtime_seq.nth_opt"
                                [ index.semantic_expr; sequence ],
                              [
                                ( Semantic_ir.PConstructor
                                    ("Some", Some (Semantic_ir.PVar "value")),
                                  Semantic_ir.Ident "value" );
                                ( Semantic_ir.PConstructor ("None", None),
                                  default.semantic_expr );
                              ] ))))
      | Ok _ -> Error.error ~code:Error_code.Arity "nth expects 2 or 3 arguments"
    and compile_get scope env arg_forms =
      let unresolved = function TUnknown -> true | _ -> false in
      let adapt_transient_value expected (actual : typed_expr) =
        if unresolved expected then Ok actual.semantic_expr
        else if Edn_value_elaborator.is_value_type expected then
          Edn_value_elaborator.pack_expression actual.ty actual.semantic_expr
        else if Types.is_dynamic expected && not (Types.is_dynamic actual.ty)
        then pack_dynamic_value env expected actual
        else if Types.is_dynamic actual.ty && not (Types.is_dynamic expected)
        then dynamic_unpack env expected actual.semantic_expr
        else if
          match (expected, actual.ty) with TSet _, TSet _ -> true | _ -> false
        then
          let expected_element, actual_element =
            match (expected, actual.ty) with
            | TSet expected_element, TSet actual_element ->
                (expected_element, actual_element)
            | _ -> assert false
          in
          Result.bind (Types.set_module_name expected_element)
            (fun expected_module ->
              Result.map
                (fun actual_module ->
                  if String.equal expected_module actual_module then
                    actual.semantic_expr
                  else
                    apply (expected_module ^ ".of_list")
                      [
                        apply (actual_module ^ ".elements")
                          [ actual.semantic_expr ];
                      ])
                (Types.set_module_name actual_element))
        else if
          Types.assignable ~policy:Host_boundary ~expected ~actual:actual.ty
          || Types.defer_to_ocaml ~expected ~actual:actual.ty
        then
          Ok
            (coerce_expression_to_type expected actual.ty actual.semantic_expr)
        else
          Error.error ~code:Error_code.Semantic
            ("get value type " ^ source_name actual.ty ^ " is not compatible with "
           ^ source_name expected)
      in
      let compile_heterogeneous_default get_option target key value_ty default =
        let dynamic = Types.dynamic_constraint TUnknown in
        let value_name = "__lg_get_present_value" in
        let present = typed_ir value_ty (Semantic_ir.Ident value_name) in
        Result.bind (pack_dynamic_value env dynamic present) (fun present ->
            Result.map
              (fun missing ->
                typed_ir dynamic
                  (Semantic_ir.Match
                     ( apply get_option [ target; key ],
                       [
                         ( Semantic_ir.PConstructor
                             ("Some", Some (Semantic_ir.PVar value_name)),
                           present );
                         (Semantic_ir.PConstructor ("None", None), missing);
                       ] )))
              (pack_dynamic_value env dynamic default))
      in
      let result_value_type value_ty default =
        match (value_ty, Env.expected_type env) with
        | TSet _, Some (TSet _ as expected)
          when Type_solver.is_open value_ty
               && not (Type_solver.is_open expected) ->
            expected
        | value_ty, _
          when Types.is_dynamic value_ty -> (
            match Types.dynamic_constraint_info value_ty with
            | Some (TUnknown | TMeta _ | TVar _) | None ->
                Types.dynamic_constraint TUnknown
            | Some constrained -> constrained)
        | _ when unresolved value_ty -> (
            match default with
            | Some (default, _) when not (unresolved default.ty) -> default.ty
            | None | Some _ -> Types.dynamic_constraint TUnknown)
        | _ -> value_ty
      in
      let optional_context_value_type fallback =
        match Env.expected_type env with
        | Some (TNullable value_ty) | Some (TOcaml_app ("option", [ value_ty ]))
          when not (unresolved value_ty) ->
            Some value_ty
        | Some (TNullable _) | Some (TOcaml_app ("option", [ _ ])) ->
            Some fallback
        | Some _ | None -> None
      in
      let compile_transient_get target key default =
        match target.ty with
        | TOcaml_app
            ("Lg_runtime.Runtime_transient.map", [ declared_key_ty; value_ty ]) ->
            let key_ty =
              if unresolved declared_key_ty then
                if unresolved key.ty then Types.dynamic_constraint TUnknown
                else key.ty
              else declared_key_ty
            in
            Result.bind (adapt_transient_value key_ty key) (fun key ->
                let operation name =
                  "Lg_runtime.Runtime_transient." ^ name
                  ^ if Types.is_dynamic key_ty then "_dynamic" else ""
                in
                let result_value_ty = result_value_type value_ty default in
                match default with
                | None
                  when Option.is_some
                         (optional_context_value_type result_value_ty) ->
                    let result_value_ty =
                      Option.get (optional_context_value_type result_value_ty)
                    in
                    Ok
                      (typed_ir (TNullable result_value_ty)
                         (apply (operation "map_get_option")
                            [ target.semantic_expr; key ]))
                | None when Types.is_dynamic result_value_ty ->
                    Ok
                      (typed_ir result_value_ty
                         (apply (operation "map_get_default")
                            [
                              target.semantic_expr;
                              key;
                              Semantic_ir.Ident
                                "Lg_runtime.Runtime_dynamic.nil";
                            ]))
                | None ->
                    Ok
                      (typed_ir (TNullable result_value_ty)
                         (apply (operation "map_get_option")
                            [ target.semantic_expr; key ]))
                | Some (default, default_is_nil) ->
                    let result_ty = result_value_ty in
                    if default_is_nil && not (Types.is_dynamic result_ty) then
                      Ok
                        (typed_ir (TNullable result_ty)
                           (apply (operation "map_get_option")
                              [ target.semantic_expr; key ]))
                    else if
                      not
                        (Types.assignable ~policy:Host_boundary
                           ~expected:result_ty ~actual:default.ty)
                    then
                      compile_heterogeneous_default
                        (operation "map_get_option") target.semantic_expr key
                        result_ty default
                    else
                      Result.map
                        (fun default ->
                          typed_ir result_ty
                            (apply (operation "map_get_default")
                               [ target.semantic_expr; key; default ]))
                        (adapt_transient_value result_ty default))
        | _ -> Error.error ~code:Error_code.Arity "get expects a transient map"
      in
      let compile_runtime_map_get target key default =
        match Types.dynamic_map_types target.ty with
        | None -> Error.error ~code:Error_code.Arity "get expects a map"
        | Some (declared_key_ty, value_ty) ->
            let key_ty =
              if unresolved declared_key_ty then
                if unresolved key.ty then Types.dynamic_constraint TUnknown
                else key.ty
              else declared_key_ty
            in
            Result.bind (adapt_transient_value key_ty key) (fun key ->
                let operation name = runtime_map_operation key_ty name in
                let result_value_ty = result_value_type value_ty default in
                match default with
                | None
                  when Option.is_some
                         (optional_context_value_type result_value_ty) ->
                    let result_value_ty =
                      Option.get (optional_context_value_type result_value_ty)
                    in
                    Ok
                      (typed_ir (TNullable result_value_ty)
                         (apply (operation "get_option")
                            [ target.semantic_expr; key ]))
                | None when Types.is_dynamic result_value_ty ->
                    Ok
                      (typed_ir result_value_ty
                         (apply (operation "get_default")
                            [
                              target.semantic_expr;
                              key;
                              Semantic_ir.Ident
                                "Lg_runtime.Runtime_dynamic.nil";
                            ]))
                | None ->
                    Ok
                      (typed_ir (TNullable result_value_ty)
                         (apply (operation "get_option")
                            [ target.semantic_expr; key ]))
                | Some (default, default_is_nil) ->
                    if
                      default_is_nil
                      && not (Types.is_dynamic result_value_ty)
                    then
                      Ok
                        (typed_ir (TNullable result_value_ty)
                           (apply (operation "get_option")
                              [ target.semantic_expr; key ]))
                    else if
                      not
                        (Types.assignable ~policy:Host_boundary
                           ~expected:result_value_ty ~actual:default.ty)
                    then
                      compile_heterogeneous_default (operation "get_option")
                        target.semantic_expr key result_value_ty default
                    else
                      Result.map
                        (fun default ->
                          typed_ir result_value_ty
                            (apply (operation "get_default")
                               [ target.semantic_expr; key; default ]))
                        (adapt_transient_value result_value_ty default))
      in
      let compile_optional_map_adapter_get target key default =
        match
          Env.find_optional_map_adapter
            (Types.constraint_value_type target.ty) env
        with
        | None -> None
        | Some (key_ty, value_ty, adapter) ->
            let map_name = "__lg_optional_adapter_map" in
            let map =
              typed_ir (Types.dynamic_map key_ty value_ty)
                (Semantic_ir.Ident map_name)
            in
            Some
              (Result.bind (compile_runtime_map_get map key default)
                 (fun lookup ->
                   let missing =
                     match default with
                     | None when Types.is_dynamic lookup.ty ->
                         Ok
                           (Semantic_ir.Ident
                              "Lg_runtime.Runtime_dynamic.nil")
                     | None -> Ok (Semantic_ir.Constructor ("None", None))
                     | Some (_, true)
                       when (match lookup.ty with
                            | TNullable _ | TOcaml_app ("option", [ _ ]) ->
                                true
                            | _ -> false) ->
                         Ok (Semantic_ir.Constructor ("None", None))
                     | Some (default, _) ->
                         adapt_transient_value lookup.ty default
                   in
                   Result.map
                     (fun missing ->
                       typed_ir lookup.ty
                         (Semantic_ir.Match
                            ( Semantic_ir.Apply
                                ( Semantic_ir.Ident adapter,
                                  [ target.semantic_expr ] ),
                              [
                                ( Semantic_ir.PConstructor ("None", None),
                                  missing );
                                ( Semantic_ir.PConstructor
                                    ( "Some",
                                      Some (Semantic_ir.PVar map_name) ),
                                  lookup.semantic_expr );
                              ] )))
                     missing))
      in
      let string_index_is_valid target index =
        Semantic_ir.Infix
          ( "&&",
            Semantic_ir.Infix
              (">=", index.semantic_expr, Semantic_ir.Int 0),
            Semantic_ir.Infix
              ( "<",
                index.semantic_expr,
                apply "String.length" [ target.semantic_expr ] ) )
      in
      let string_get target index =
        apply "String.get" [ target.semantic_expr; index.semantic_expr ]
      in
      let string_get_option target index =
        Semantic_ir.If
          ( string_index_is_valid target index,
            Semantic_ir.Constructor
              ("Some", Some (string_get target index)),
            Semantic_ir.Constructor ("None", None) )
      in
      let arg_forms =
        match arg_forms with
        | [ target; key ] -> [ target; resolve_keyword_alias scope env key ]
        | forms -> forms
      in
      match arg_forms with
      | [ target_form; FKeyword keyword ] -> (
          let dynamic_lookup result_ty target =
            let lookup =
              apply "Lg_runtime.Runtime_dynamic.get"
                [
                  target.semantic_expr;
                  apply "Lg_runtime.Runtime_dynamic.keyword"
                    [ Semantic_ir.String keyword ];
                ]
            in
            match Env.expected_type env with
            | Some expected
              when not (Types.is_dynamic expected)
                   && not (Types.equal expected TUnknown) -> (
                match dynamic_unpack env expected lookup with
                | Ok unpacked -> typed_ir expected unpacked
                | Error _ -> typed_ir result_ty lookup)
            | Some _ | None -> typed_ir result_ty lookup
          in
          let target_env =
            match target_form with
            | FList
                [ FSymbol ("first" | "second" | "last"); _collection ] ->
                Env.with_expected_type (inferred_record_type env keyword) env
            | _ -> Env.with_expected_type (expected_record_type env keyword) env
          in
          match compile_expr scope target_env target_form with
          | Error _ as err -> err
          | Ok target -> (
              let target = unwrap_protocol_value target in
              match target.ty with
              | _
                when Option.is_some
                       (compile_optional_map_adapter_get target
                          (typed_ir TKeyword (Semantic_ir.String keyword))
                          None) ->
                  Option.get
                    (compile_optional_map_adapter_get target
                       (typed_ir TKeyword (Semantic_ir.String keyword))
                       None)
              | TNullable record_ty | TOcaml_app ("option", [ record_ty ]) -> (
                  let record_ty =
                    Collection_capability.resolve_callback_record env record_ty
                  in
                  match record_ty with
                  | TRecord fields | TNamed_record { fields; _ } -> (
                    match find_field keyword fields with
                    | None -> (
                        let record_name = "__lg_optional_record" in
                        let record =
                          typed_ir record_ty (Semantic_ir.Ident record_name)
                        in
                        let protocol_lookup =
                          match record_ty with
                          | TNamed_record named ->
                              let key =
                                typed_ir TKeyword (Semantic_ir.String keyword)
                              in
                              (match
                                 compile_deftype_method scope env named "valAt"
                                   [ record; key ]
                               with
                              | Some _ as result -> result
                              | None ->
                                  compile_deftype_method scope env named
                                    "-lookup" [ record; key ])
                          | _ -> None
                        in
                        match
                          ( Structural_map.extension_get record fields keyword,
                            protocol_lookup )
                        with
                        | None, None -> Error.error ~code:Error_code.Unresolved ("unknown field " ^ keyword)
                        | Some lookup, _ | None, Some lookup ->
                            let result_ty, missing, present =
                              if Types.is_dynamic lookup.ty then
                                ( lookup.ty,
                                  Semantic_ir.Ident
                                    "Lg_runtime.Runtime_dynamic.nil",
                                  lookup.semantic_expr )
                              else
                                match lookup.ty with
                                | TNullable _ | TOcaml_app ("option", [ _ ]) ->
                                    ( lookup.ty,
                                      Semantic_ir.Constructor ("None", None),
                                      lookup.semantic_expr )
                                | ty ->
                                    ( TNullable ty,
                                      Semantic_ir.Constructor ("None", None),
                                      Semantic_ir.Constructor
                                        ("Some", Some lookup.semantic_expr) )
                            in
                            Ok
                              (typed_ir result_ty
                                 (Semantic_ir.Match
                                    ( target.semantic_expr,
                                      [
                                        ( Semantic_ir.PConstructor
                                            ("None", None),
                                          missing );
                                        ( Semantic_ir.PConstructor
                                            ( "Some",
                                              Some
                                                (Semantic_ir.PVar record_name)
                                            ),
                                          present );
                                      ] ))))
                    | Some field ->
                      let record_name = "__lg_optional_record" in
                      let record =
                        typed_ir record_ty (Semantic_ir.Ident record_name)
                      in
                        let field_value =
                          Structural_map.field_expr record field
                        in
                      let field_ty = contextual_field_type env field.ty in
                      let result_ty, missing, present =
                        if Types.is_dynamic field_ty then
                          ( field_ty,
                            Semantic_ir.Ident
                              "Lg_runtime.Runtime_dynamic.nil",
                            field_value )
                        else
                          match field_ty with
                        | TNullable _ | TOcaml_app ("option", _) ->
                            ( field_ty,
                              Semantic_ir.Constructor ("None", None),
                              field_value )
                        | _ ->
                            ( TNullable field_ty,
                              Semantic_ir.Constructor ("None", None),
                              Semantic_ir.Constructor
                                ("Some", Some field_value) )
                      in
                      Ok
                        (typed_ir result_ty
                           (Semantic_ir.Match
                              ( target.semantic_expr,
                                  [
                                    ( Semantic_ir.PConstructor ("None", None),
                                      missing );
                                  ( Semantic_ir.PConstructor
                                      ( "Some",
                                        Some (Semantic_ir.PVar record_name) ),
                                  present );
                                ] ))))
                  | TOcaml_app
                      ("Lg_runtime.Runtime_map.t", [ _; _ ]) as map_ty ->
                      let map_name = "__lg_optional_map" in
                      let map =
                        typed_ir map_ty (Semantic_ir.Ident map_name)
                      in
                      let key =
                        typed_ir TKeyword (Semantic_ir.String keyword)
                      in
                      Result.map
                        (fun lookup ->
                          let missing =
                            if Types.is_dynamic lookup.ty then
                              Semantic_ir.Ident
                                "Lg_runtime.Runtime_dynamic.nil"
                            else Semantic_ir.Constructor ("None", None)
                          in
                          typed_ir lookup.ty
                            (Semantic_ir.Match
                               ( target.semantic_expr,
                                 [
                                   ( Semantic_ir.PConstructor ("None", None),
                                     missing );
                                   ( Semantic_ir.PConstructor
                                       ( "Some",
                                         Some (Semantic_ir.PVar map_name) ),
                                     lookup.semantic_expr );
                                 ] )))
                        (compile_runtime_map_get map key None)
                  | ty when Types.is_dynamic ty ->
                      let value_name = "__lg_optional_value" in
                      Ok
                        (typed_ir ty
                           (Semantic_ir.Match
                              ( target.semantic_expr,
                                [
                                  ( Semantic_ir.PConstructor ("None", None),
                                    Semantic_ir.Ident
                                      "Lg_runtime.Runtime_dynamic.nil" );
                                  ( Semantic_ir.PConstructor
                                      ( "Some",
                                        Some (Semantic_ir.PVar value_name) ),
                                    apply "Lg_runtime.Runtime_dynamic.get"
                                      [
                                        Semantic_ir.Ident value_name;
                                        apply
                                          "Lg_runtime.Runtime_dynamic.keyword"
                                          [ Semantic_ir.String keyword ];
                                      ] );
                                ] )))
                  | _ -> Error.error ~code:Error_code.Arity "get expects a map")
              | TRecord fields -> (
                  match find_field keyword fields with
                  | Some field ->
                      let field_ty = contextual_field_type env field.ty in
                      Ok
                        (typed_ir field_ty
                           (Structural_map.field_expr target field))
                  | None -> (
                      match
                        Structural_map.extension_get target fields keyword
                      with
                      | Some result -> Ok result
                      | None ->
                          Ok
                            (typed_ir (TNullable TUnknown)
                               (Semantic_ir.Constructor ("None", None)))))
              | TNamed_record record -> (
                  let fields =
                    Types.record_fields (TNamed_record record)
                    |> Option.value ~default:record.fields
                  in
                  match find_field keyword fields with
                  | Some field ->
                      let field_ty = contextual_field_type env field.ty in
                      Ok
                        (typed_ir field_ty
                           (Structural_map.field_expr target field))
                  | None -> (
                      match
                        Structural_map.extension_get target fields keyword
                      with
                      | Some result -> Ok result
                      | None -> (
                          match target.ty with
                          | TNamed_record record -> (
                              let key =
                                typed_ir TKeyword
                                  (Semantic_ir.String keyword)
                              in
                              match
                                match
                                  compile_deftype_method scope env record
                                    "valAt" [ target; key ]
                                with
                                | Some _ as result -> result
                                | None ->
                                    compile_deftype_method scope env record
                                      "-lookup" [ target; key ]
                              with
                              | Some result -> Ok result
                              | None when record.nominal ->
                                  Error.error ~code:Error_code.Unresolved
                                    ("unknown record field "
                                   ^ Names.keyword_source_name keyword)
                              | None ->
                                  Ok
                                    (typed_ir (TNullable TUnknown)
                                       (Semantic_ir.Constructor ("None", None))))
                          | _ -> assert false)))
              | ty when Types.is_dynamic ty ->
                  Ok (dynamic_lookup ty target)
              | TUnknown | TMeta _ | TVar _ ->
                  let field_ty =
                    Option.value (inferred_field_type env keyword)
                      ~default:(Types.dynamic_constraint TUnknown)
                    |> contextual_field_type env
                  in
                  if Types.is_dynamic field_ty then
                    Ok (dynamic_lookup field_ty target)
                  else
                    Ok
                      (typed_ir field_ty
                         (Semantic_ir.Field
                            ( target.semantic_expr,
                              Names.keyword_to_ocaml_name keyword )))
              | TOcaml_app ("Lg_runtime.Runtime_map.t", [ _; _ ]) ->
                  compile_runtime_map_get target
                    (typed_ir TKeyword (Semantic_ir.String keyword)) None
              | TOcaml_app
                  ("Lg_runtime.Runtime_transient.map", [ _; _ ]) ->
                  compile_transient_get target
                    (typed_ir TKeyword (Semantic_ir.String keyword)) None
              | TOcaml_app (type_name, arguments) as ty -> (
                  match
                    instantiated_record_field scope env type_name arguments
                      keyword
                  with
                  | Some (record, field) ->
                      let target = { target with ty = TNamed_record record } in
                      let field_ty = contextual_field_type env field.ty in
                      Ok
                        (typed_ir field_ty
                           (Structural_map.field_expr target field))
                  | None when is_ocaml_owned_type ty ->
                      Ok (external_field type_name target keyword)
                  | None -> Error.error ~code:Error_code.Arity "get expects a map")
              | TOcaml type_name as ty -> (
                  match
                    instantiated_record_field scope env type_name [] keyword
                  with
                  | Some (record, field) ->
                      let target = { target with ty = TNamed_record record } in
                      let field_ty = contextual_field_type env field.ty in
                      Ok
                        (typed_ir field_ty
                           (Structural_map.field_expr target field))
                  | None when is_ocaml_owned_type ty ->
                      Ok (external_field type_name target keyword)
                  | None -> Error.error ~code:Error_code.Arity "get expects a map")
              | ty when is_ocaml_owned_type ty ->
                  Ok
                    (typed_ir TUnknown
                       (Semantic_ir.Field
                        ( target.semantic_expr,
                          Names.keyword_to_ocaml_name keyword )))
              | _ -> Error.error ~code:Error_code.Arity "get expects a map"))
      | [ target_form; index_form ] -> (
        let expected_type = Env.expected_type env in
        let env = Env.with_expected_type None env in
        match
          (compile_expr scope env target_form, compile_expr scope env index_form)
        with
          | (Error _ as err), _ -> err
          | _, (Error _ as err) -> err
          | Ok target, Ok index -> (
              let target = unwrap_protocol_value target in
              match (target.ty, index.ty) with
              | _, _
                when Option.is_some
                       (compile_optional_map_adapter_get target index None) ->
                  Option.get
                    (compile_optional_map_adapter_get target index None)
              | TString, TInt ->
                  Ok
                    (typed_ir (TNullable TChar)
                       (string_get_option target index))
              | TString, _ -> Error.error ~code:Error_code.Semantic "get string index must be int"
              | TVector inner, TInt ->
                  Ok
                    (typed_ir inner
                     (apply "Rrbvec.nth"
                        [ target.semantic_expr;
                          index.semantic_expr;
                        ]))
              | TVector _, _ -> Error.error ~code:Error_code.Semantic "get vector index must be int"
              | ( (TNullable (TNamed_record record)
                  | TOcaml_app ("option", [ TNamed_record record ])),
                  _ ) ->
                  let value_name = "__lg_optional_lookup_value" in
                  let value =
                    typed_ir (TNamed_record record)
                      (Semantic_ir.Ident value_name)
                  in
                  let lookup =
                    match
                      compile_deftype_method scope env record "valAt"
                        [ value; index ]
                    with
                    | Some _ as result -> result
                    | None ->
                        compile_deftype_method scope env record "-lookup"
                          [ value; index ]
                  in
                  (match lookup with
                  | None -> Error.error ~code:Error_code.Semantic "get key must be a keyword"
                  | Some lookup ->
                      let result_ty, missing, present =
                        if Types.is_dynamic lookup.ty then
                          ( lookup.ty,
                            Semantic_ir.Ident
                              "Lg_runtime.Runtime_dynamic.nil",
                            lookup.semantic_expr )
                        else
                          match lookup.ty with
                          | TNullable _ | TOcaml_app ("option", [ _ ]) ->
                              ( lookup.ty,
                                Semantic_ir.Constructor ("None", None),
                                lookup.semantic_expr )
                          | ty ->
                              ( TNullable ty,
                                Semantic_ir.Constructor ("None", None),
                                Semantic_ir.Constructor
                                  ("Some", Some lookup.semantic_expr) )
                      in
                      Ok
                        (typed_ir result_ty
                           (Semantic_ir.Match
                              ( target.semantic_expr,
                                [
                                  ( Semantic_ir.PConstructor ("None", None),
                                    missing );
                                  ( Semantic_ir.PConstructor
                                      ( "Some",
                                        Some (Semantic_ir.PVar value_name) ),
                                    present );
                                ] ))))
              | TNamed_record { nominal = true; _ }, _
                when (match index_form with FKeyword _ -> false | _ -> true) ->
                  compile_expr scope env
                    (FList
                       [
                         FSymbol "ILookup/-lookup";
                         target_form;
                         index_form;
                       ])
              | TNamed_record record, _ -> (
                let concrete_fields =
                  record.fields
                  |> List.filter (fun (field : field) ->
                      let unresolved_dynamic =
                        match Types.dynamic_constraint_info field.ty with
                        | Some (TUnknown | TMeta _ | TVar _) -> true
                        | Some _ | None -> false
                      in
                      (not (Types.is_record_extension_field field))
                      && not
                        (unresolved_dynamic
                        || Types.equal field.ty TUnknown
                        || Types.equal field.ty TMap_keys
                        || match field.ty with TVar _ -> true | _ -> false))
                in
                let groups =
                  List.fold_left
                    (fun groups (field : field) ->
                      match
                        List.find_opt
                          (fun (ty, _) -> Types.equal ty field.ty)
                          groups
                      with
                      | None -> (field.ty, [ field ]) :: groups
                      | Some (ty, fields) ->
                          (ty, field :: fields)
                          :: List.filter
                               (fun (candidate, _) ->
                                 not (Types.equal candidate ty))
                               groups)
                    [] concrete_fields
                in
                let keyed_projection =
                  let selected_groups =
                    match expected_type with
                    | None -> groups
                    | Some expected ->
                        groups
                        |> List.filter (fun (result_ty, _) ->
                               Types.assignable ~policy:Host_boundary
                                 ~expected ~actual:result_ty)
                  in
                  match (selected_groups, index.ty) with
                  | [ (result_ty, fields) ], TKeyword ->
                      Some (result_ty, fields, index.semantic_expr)
                  | [ (result_ty, fields) ], ty when Types.is_dynamic ty ->
                      Some
                        ( result_ty,
                          fields,
                          apply "Lg_runtime.Runtime_dynamic.as_keyword"
                            [ index.semantic_expr ] )
                  | _ -> None
                in
                match keyed_projection with
                | Some (result_ty, fields, key) ->
                    let cases =
                      List.map
                        (fun (field : field) ->
                          ( Semantic_ir.PString field.keyword,
                            Semantic_ir.Constructor
                              ( "Some",
                                Some
                                  (Structural_map.field_expr target field) ) ))
                        fields
                      @ [
                          ( Semantic_ir.PAny,
                            Semantic_ir.Constructor ("None", None) );
                        ]
                    in
                    Ok
                      (typed_ir (TNullable result_ty)
                         (Semantic_ir.Match (key, cases)))
                | None -> (
                    match
                  match
                       compile_deftype_method scope env record "valAt"
                         [ target; index ]
                     with
                    | Some _ as result -> result
                    | None ->
                        compile_deftype_method scope env record "-lookup"
                            [ target; index ]
                  with
                  | Some result -> Ok result
                  | None -> Error.error ~code:Error_code.Semantic "get key must be a keyword"))
              | TRecord fields, _
                when Types.is_homogeneous_record fields ->
                  let value_ty =
                    Types.homogeneous_record_value_type fields |> Option.get
                  in
                  compile_runtime_map_get
                    { target with ty = Types.dynamic_map TKeyword value_ty }
                    index None
              | TOcaml_app ("Lg_runtime.Runtime_map.t", [ _; _ ]), _ ->
                  compile_runtime_map_get target index None
              | _ -> (
                  match target.ty with
                  | TOcaml_app
                      ("Lg_runtime.Runtime_transient.map", [ _; _ ]) ->
                      compile_transient_get target index None
                  | _ -> (
                  match Types.dynamic_map_types target.ty with
                  | Some (key_ty, value_ty)
                    when Types.assignable ~policy:Host_boundary ~expected:key_ty
                           ~actual:index.ty ->
                      let key =
                        if
                          Types.is_dynamic key_ty
                          && not (Types.is_dynamic index.ty)
                        then pack_dynamic_value env key_ty index
                        else Ok index.semantic_expr
                      in
                      Result.map
                        (fun key ->
                          typed_ir (TNullable value_ty)
                            (apply
                               (runtime_map_operation
                                  (runtime_map_key_type key_ty index.ty)
                                  "get_option")
                               [ target.semantic_expr; key ]))
                        key
                  | None
                    when Types.equal target.ty TUnknown
                       || match target.ty with TVar _ -> true | _ -> false ->
                      Ok
                        (typed_ir (TNullable TUnknown)
                           (apply "Lg_runtime.Runtime_map.get_option"
                              [ target.semantic_expr; index.semantic_expr ]))
                  | None
                    when Types.is_dynamic
                           (Types.constraint_value_type target.ty) ->
                      let dynamic = Types.dynamic_constraint TUnknown in
                      Result.map
                        (fun key ->
                          let lookup =
                            apply "Lg_runtime.Runtime_dynamic.get"
                              [ dynamic_constraint_value target; key ]
                          in
                          match expected_type with
                          | Some expected
                            when not (Types.is_dynamic expected)
                                 && not (Types.equal expected TUnknown) -> (
                              match dynamic_unpack env expected lookup with
                              | Ok unpacked -> typed_ir expected unpacked
                              | Error _ -> typed_ir dynamic lookup)
                          | Some _ | None -> typed_ir dynamic lookup)
                        (pack_dynamic_value env dynamic index)
                  | _ ->
                      Error.error ~code:Error_code.Unsupported
                        ("get key type " ^ source_name index.ty
                       ^ " is not supported for " ^ source_name target.ty)))))
      | [ target_form; FKeyword keyword; default_form ] -> (
          match
          ( compile_expr scope env target_form,
            compile_expr scope env default_form )
          with
          | (Error _ as err), _ -> err
          | _, (Error _ as err) -> err
          | Ok target, Ok default -> (
              let target = unwrap_protocol_value target in
              match target.ty with
              | _
                when Option.is_some
                       (compile_optional_map_adapter_get target
                          (typed_ir TKeyword (Semantic_ir.String keyword))
                          (Some (default, default_form = FSymbol "nil"))) ->
                  Option.get
                    (compile_optional_map_adapter_get target
                       (typed_ir TKeyword (Semantic_ir.String keyword))
                       (Some (default, default_form = FSymbol "nil")))
              | (TNullable (TNamed_record record)
                | TOcaml_app ("option", [ TNamed_record record ])) ->
                  let value_name = "__lg_optional_lookup_value" in
                  let value =
                    typed_ir (TNamed_record record)
                      (Semantic_ir.Ident value_name)
                  in
                  let key = typed_ir TKeyword (Semantic_ir.String keyword) in
                  let lookup =
                    match
                      compile_deftype_method scope env record "valAt"
                        [ value; key; default ]
                    with
                    | Some _ as result -> result
                    | None ->
                        compile_deftype_method scope env record "-lookup"
                          [ value; key; default ]
                  in
                  (match lookup with
                  | None -> Error.error ~code:Error_code.Arity "get expects a map"
                  | Some lookup ->
                      Result.map
                        (fun missing ->
                          typed_ir lookup.ty
                            (Semantic_ir.Match
                               ( target.semantic_expr,
                                 [
                                   ( Semantic_ir.PConstructor ("None", None),
                                     missing );
                                   ( Semantic_ir.PConstructor
                                       ( "Some",
                                         Some (Semantic_ir.PVar value_name) ),
                                     lookup.semantic_expr );
                                 ] )))
                        (adapt_transient_value lookup.ty default))
              | TRecord fields | TNamed_record { fields; nominal = false; _ } -> (
                  match find_field keyword fields with
                  | Some field when Types.equal field.ty default.ty ->
                      Ok
                        (typed_ir field.ty
                           (Structural_map.field_expr target field))
                  | Some
                      ( {
                          ty =
                            (TNullable inner | TOcaml_app ("option", [ inner ]));
                          _;
                        } as field )
                    when Types.equal inner default.ty ->
                      let value_name = "__lg_lookup_default_value" in
                      Ok
                        (typed_ir inner
                           (Semantic_ir.Match
                              ( Structural_map.field_expr target field,
                                [
                                  ( Semantic_ir.PConstructor ("None", None),
                                    default.semantic_expr );
                                  ( Semantic_ir.PConstructor
                                      ("Some", Some (Semantic_ir.PVar value_name)),
                                    Semantic_ir.Ident value_name );
                                ] )))
                  | Some field ->
                      Error.error ~code:Error_code.Semantic
                      ("get default for " ^ keyword ^ " must be "
                     ^ source_name field.ty)
                  | None -> Ok default)
              | TNamed_record record -> (
                  match find_field keyword record.fields with
                  | Some field when Types.equal field.ty default.ty ->
                      Ok
                        (typed_ir field.ty
                           (Structural_map.field_expr target field))
                  | Some _ ->
                      Error.error ~code:Error_code.Type_mismatch
                        ("get default for " ^ keyword ^ " has incompatible type")
                | None -> (
                      let key = typed_ir TKeyword (Semantic_ir.String keyword) in
                    match
                      match
                            compile_deftype_method scope env record "valAt"
                              [ target; key; default ]
                          with
                          | Some _ as result -> result
                          | None ->
                              compile_deftype_method scope env record "-lookup"
                            [ target; key; default ]
                       with
                      | Some result -> Ok result
                      | None -> Ok default))
              | TOcaml_app
                  ("Lg_runtime.Runtime_transient.map", [ _; _ ]) ->
                  compile_transient_get target
                    (typed_ir TKeyword (Semantic_ir.String keyword))
                    (Some (default, default_form = FSymbol "nil"))
              | TOcaml_app ("Lg_runtime.Runtime_map.t", [ _; _ ]) ->
                  compile_runtime_map_get target
                    (typed_ir TKeyword (Semantic_ir.String keyword))
                    (Some (default, default_form = FSymbol "nil"))
              | _ -> (
                  match Types.dynamic_map_types target.ty with
                  | Some (key_ty, value_ty) when default_form = FSymbol "nil" ->
                      Ok
                        (typed_ir (TNullable value_ty)
                           (apply (runtime_map_operation key_ty "get_option")
                            [ target.semantic_expr; Semantic_ir.String keyword ]))
                  | Some (key_ty, value_ty)
                  when Types.assignable ~policy:Host_boundary ~expected:value_ty
                         ~actual:default.ty ->
                      Ok
                        (typed_ir value_ty
                           (apply (runtime_map_operation key_ty "get_default")
                            [
                              target.semantic_expr;
                                Semantic_ir.String keyword;
                                default.semantic_expr;
                              ]))
                  | _ -> Error.error ~code:Error_code.Arity "get expects a map")))
      | [ target_form; index_form; default_form ] -> (
          match compile_expr scope env target_form with
          | Error _ as err -> err
          | Ok target -> (
              let target = unwrap_protocol_value target in
              match compile_expr scope env index_form with
              | Error _ as err -> err
              | Ok index -> (
                  let default_expected =
                    match Types.dynamic_map_types target.ty with
                    | Some (key_ty, value_ty)
                      when Types.assignable ~policy:Host_boundary
                             ~expected:key_ty ~actual:index.ty ->
                        Some value_ty
                    | _ -> None
                  in
                  match
                    compile_expr scope
                      (Env.with_expected_type default_expected env)
                      default_form
                  with
                  | Error _ as err -> err
                  | Ok default -> (
              match (target.ty, index.ty) with
              | _, _
                when Option.is_some
                       (compile_optional_map_adapter_get target index
                          (Some (default, default_form = FSymbol "nil"))) ->
                  Option.get
                    (compile_optional_map_adapter_get target index
                       (Some (default, default_form = FSymbol "nil")))
              | TString, TInt when Types.equal default.ty TChar ->
                  Ok
                    (typed_ir TChar
                       (Semantic_ir.If
                          ( string_index_is_valid target index,
                            string_get target index,
                            default.semantic_expr )))
              | TString, TInt when Types.equal default.ty TNil ->
                  Ok
                    (typed_ir (TNullable TChar)
                       (string_get_option target index))
              | TString, TInt ->
                  Error.error ~code:Error_code.Semantic "get default for string must be char or nil"
              | TString, _ -> Error.error ~code:Error_code.Semantic "get string index must be int"
              | TVector inner, TInt
                when Types.equal inner default.ty
                     || (Types.equal inner (TOcaml "Lg_edn_backend.t")
                        && Edn_value_elaborator.is_packable default.ty) ->
                  Ok
                    (typed_ir inner
                       (Semantic_ir.Match
                          ( apply "Rrbvec.nth_opt"
                              [ target.semantic_expr; index.semantic_expr ],
                            [
                              ( Semantic_ir.PConstructor
                                  ("Some", Some (Semantic_ir.PVar "value")),
                                Semantic_ir.Ident "value" );
                              ( Semantic_ir.PConstructor ("None", None),
                                coerce_expression_to_type inner default.ty
                                  default.semantic_expr );
                            ] )))
              | TVector _, TInt ->
                  Error.error ~code:Error_code.Semantic "get default for vector must match element type"
              | TVector _, _ -> Error.error ~code:Error_code.Semantic "get vector index must be int"
              | TNamed_record { nominal = true; _ }, _
                when (match index_form with FKeyword _ -> false | _ -> true) ->
                  let lookup_arguments =
                    if default_form = FSymbol "nil" then
                      [ target_form; index_form ]
                    else [ target_form; index_form; default_form ]
                  in
                  compile_expr scope env
                    (FList
                       (FSymbol "ILookup/-lookup" :: lookup_arguments))
              | TNamed_record record, _ -> (
                  match
                  match
                       compile_deftype_method scope env record "valAt"
                         [ target; index; default ]
                     with
                    | Some _ as result -> result
                    | None ->
                        compile_deftype_method scope env record "-lookup"
                        [ target; index; default ]
                  with
                  | Some result -> Ok result
                  | None -> Error.error ~code:Error_code.Semantic "get key must be a keyword")
              | TRecord fields, _
                when Types.is_homogeneous_record fields ->
                  let value_ty =
                    Types.homogeneous_record_value_type fields |> Option.get
                  in
                  compile_runtime_map_get
                    { target with ty = Types.dynamic_map TKeyword value_ty }
                    index (Some (default, default_form = FSymbol "nil"))
              | TOcaml_app ("Lg_runtime.Runtime_map.t", [ _; _ ]), _ ->
                  compile_runtime_map_get target index
                    (Some (default, default_form = FSymbol "nil"))
              | _ -> (
                  match target.ty with
                  | TOcaml_app
                      ("Lg_runtime.Runtime_transient.map", [ _; _ ]) ->
                      compile_transient_get target index
                        (Some (default, default_form = FSymbol "nil"))
                  | _ -> (
                  match Types.dynamic_map_types target.ty with
                  | Some (key_ty, value_ty)
                    when default_form = FSymbol "nil"
                         && Types.assignable ~policy:Host_boundary
                              ~expected:key_ty ~actual:index.ty ->
                      Ok
                        (typed_ir (TNullable value_ty)
                           (apply
                              (runtime_map_operation
                                 (runtime_map_key_type key_ty index.ty)
                                 "get_option")
                              [ target.semantic_expr; index.semantic_expr ]))
                  | Some (key_ty, value_ty)
                    when Types.assignable ~policy:Host_boundary ~expected:key_ty
                           ~actual:index.ty
                         && Types.assignable ~policy:Host_boundary
                              ~expected:value_ty ~actual:default.ty ->
                      Ok
                        (typed_ir value_ty
                           (apply
                              (runtime_map_operation
                                 (runtime_map_key_type key_ty index.ty)
                                 "get_default")
                            [
                              target.semantic_expr;
                                index.semantic_expr;
                                default.semantic_expr;
                              ]))
                  | None
                    when Types.equal target.ty TUnknown
                       || match target.ty with TVar _ -> true | _ -> false ->
                      if default_form = FSymbol "nil" then
                        Ok
                          (typed_ir (TNullable TUnknown)
                             (apply "Lg_runtime.Runtime_map.get_option"
                                [ target.semantic_expr; index.semantic_expr ]))
                      else
                        Ok
                          (typed_ir default.ty
                             (apply "Lg_runtime.Runtime_map.get_default"
                              [
                                target.semantic_expr;
                                  index.semantic_expr;
                                  default.semantic_expr;
                                ]))
                  | _ ->
                      Error.error ~code:Error_code.Unsupported
                        ("get key type " ^ source_name index.ty
                       ^ " is not supported for " ^ source_name target.ty)))))))
      | _ -> Error.error ~code:Error_code.Arity "get expects 2 or 3 arguments"
    and compile_find scope env arg_forms =
      let arg_forms =
        match arg_forms with
        | [ target; key ] -> [ target; resolve_keyword_alias scope env key ]
        | forms -> forms
      in
      match (arg_forms, compile_args_for scope env arg_forms) with
      | _, (Error _ as err) -> err
      | [ _; FKeyword keyword ], Ok [ target; key ]
        when (match target.ty with
             | TRecord _
             | TNamed_record { nominal = false; _ } -> true
             | _ -> false) -> (
          let target = unwrap_protocol_value target in
          match target.ty with
          | TRecord fields
          | TNamed_record { fields; nominal = false; _ } ->
              let target_name = "__lg_find_record" in
              let key_name = "__lg_find_key" in
              let result_ty, result =
                match find_field keyword fields with
                | Some field ->
                    let projected_target =
                      {
                        target with
                        semantic_expr = Semantic_ir.Ident target_name;
                        record_values = None;
                      }
                    in
                    ( TOcaml_app
                        ("option", [ TTuple [ TKeyword; field.ty ] ]),
                      Semantic_ir.Constructor
                        ( "Some",
                          Some
                            (Semantic_ir.Tuple
                               [
                                 Semantic_ir.Ident key_name;
                                 Structural_map.field_expr projected_target field;
                               ]) ) )
                | None ->
                    ( TOcaml_app
                        ("option", [ TTuple [ TKeyword; TUnknown ] ]),
                      Semantic_ir.Constructor ("None", None) )
              in
              Ok
                (typed_ir result_ty
                   (Semantic_ir.Let
                      ( [
                          ( Semantic_ir.PVar target_name,
                            target.semantic_expr );
                          (Semantic_ir.PVar key_name, key.semantic_expr);
                        ],
                        result )))
          | _ -> assert false)
      | _, Ok [ target; key ] -> (
          if Types.is_dynamic target.ty then
            Result.map
              (fun packed_key ->
                typed_ir
                  (TOcaml_app
                     ("option", [ TVector (Types.dynamic_constraint TUnknown) ]))
                  (apply "Lg_runtime.Runtime_dynamic.find"
                     [ target.semantic_expr; packed_key ]))
              (pack_dynamic_value env target.ty key)
          else if Types.equal target.ty TNil then
            Ok
              (typed_ir
                 (TOcaml_app ("option", [ TTuple [ key.ty; TUnknown ] ]))
                 (Semantic_ir.Constructor ("None", None)))
          else
            match (target.ty, key.ty) with
            | TVector value_ty, TInt ->
                Ok
                  (typed_ir
                     (TOcaml_app ("option", [ TTuple [ TInt; value_ty ] ]))
                     (apply "Lg_runtime.Runtime_vector.find_entry"
                        [ target.semantic_expr; key.semantic_expr ]))
            | TVector value_ty, TNil ->
                Ok
                  (typed_ir
                     (TOcaml_app
                        ("option", [ TTuple [ key.ty; value_ty ] ]))
                     (Semantic_ir.Constructor ("None", None)))
            | _ -> (
            match Types.dynamic_map_types target.ty with
            | Some (key_ty, value_ty)
              when Types.assignable ~policy:Host_boundary ~expected:key_ty
                     ~actual:key.ty ->
                let key_expr =
                  coerce_expression_to_type key_ty key.ty key.semantic_expr
                in
                Ok
                  (typed_ir
                     (TOcaml_app ("option", [ TTuple [ key_ty; value_ty ] ]))
                     (apply
                        (runtime_map_operation
                           (runtime_map_key_type key_ty key.ty)
                           "find")
                        [ target.semantic_expr; key_expr ]))
            | None
              when Types.equal target.ty TUnknown
                 || match target.ty with TVar _ -> true | _ -> false ->
                Ok
                  (typed_ir
                     (TOcaml_app
                        ("option", [ TTuple [ key.ty; TUnknown ] ]))
                     (apply "Lg_runtime.Runtime_map.find"
                        [ target.semantic_expr; key.semantic_expr ]))
            | Some _ ->
                Error.error ~code:Error_code.Arity
                  ("find expects a map and key, got "
                 ^ Types.source_name target.ty ^ " and "
                 ^ Types.source_name key.ty)
            | None ->
                compile_expr scope env
                  (FList (FSymbol "IFind/-find" :: arg_forms))))
      | _, Ok _ -> Error.error ~code:Error_code.Arity "find expects 2 arguments"
    and compile_assoc scope env arg_forms =
      let symbol_tail name =
        match List.rev (String.split_on_char '/' name) with
        | tail :: _ -> tail
        | [] -> name
      in
      let rec pure_callback_value = function
        | FList (FSymbol ("fn" | "fn*") :: _) -> true
        | FList [ FSymbol wrapper; value ]
          when List.mem (symbol_tail wrapper) [ "Some"; "Ok"; "Error" ] ->
            pure_callback_value value
        | _ -> false
      in
      let needs_binding form =
        if pure_callback_value form then false
        else match form with
        | FList _ | FMap _ | FVector _ -> true
        | _ -> false
      in
      let rec operands = function
        | _key :: value :: rest -> value :: operands rest
        | _ -> []
      in
      match arg_forms with
      | target :: pairs when List.exists needs_binding (target :: operands pairs) ->
          incr assoc_expansion_counter;
          let prefix = "__lg_assoc_" ^ string_of_int !assoc_expansion_counter ^ "_" in
          let target_name = FSymbol (prefix ^ "target") in
          let rec bind_pairs index bindings args = function
            | key :: value :: rest ->
                if needs_binding value then
                  let name = FSymbol (prefix ^ string_of_int index) in
                  bind_pairs (index + 1) (value :: name :: bindings)
                    (name :: key :: args) rest
                else bind_pairs index bindings (value :: key :: args) rest
            | rest ->
                FList [FSymbol "let";
                       FVector (target_name :: target :: List.rev bindings);
                       FList (FSymbol "__lg_assoc" :: target_name :: List.rev args @ rest)]
          in
          compile_expr scope env (bind_pairs 0 [] [] pairs)
      | _ -> compile_assoc_bound scope env arg_forms
    and compile_assoc_bound scope env arg_forms =
      match arg_forms with
    | target_form :: pair_forms -> (
          let rec resolve_pair_keys = function
            | key :: value :: rest ->
                resolve_keyword_alias scope env key
                :: value :: resolve_pair_keys rest
            | forms -> forms
          in
          let pair_forms = resolve_pair_keys pair_forms in
          let rec compile_record_pairs fields acc = function
            | [] -> Ok (List.rev acc)
            | FKeyword keyword :: value_form :: rest -> (
                let expected =
                  Option.map (fun (field : field) -> field.ty)
                    (find_field keyword fields)
                in
                match
                  compile_expr scope (Env.with_expected_type expected env)
                    value_form
                with
                | Error _ as err -> err
                | Ok value ->
                    compile_record_pairs fields ((keyword, value) :: acc) rest)
            | _ -> Error.error ~code:Error_code.Arity "assoc expects map followed by keyword/value pairs"
          in
          let adapt_dynamic_fields fields pairs =
            let rec adapt adapted = function
              | [] -> Ok (List.rev adapted)
              | (keyword, value) :: rest -> (
                  match find_field keyword fields with
                  | Some field -> (
                      match
                        inject_contextual_closed_sum env ~expected:field.ty value
                      with
                      | Some (Error _ as error) -> error
                      | Some (Ok value) ->
                          adapt ((keyword, value) :: adapted) rest
                      | None
                        when Types.is_dynamic field.ty
                             && not (Types.is_dynamic value.ty) ->
                          Result.bind (pack_dynamic_value env field.ty value)
                            (fun expression ->
                              adapt
                                ((keyword, typed_ir field.ty expression)
                                :: adapted)
                                rest)
                      | None
                        when (match (field.ty, value.ty) with
                             | TSeq _, (TList _ | TVector _ | TSeq _) -> true
                             | TVector expected, (TList actual | TSeq actual) ->
                                 Types.assignable ~policy:Host_boundary
                                   ~expected ~actual
                             | _ -> false) ->
                          let expression =
                            coerce_expression_to_type field.ty value.ty
                              value.semantic_expr
                          in
                          adapt
                            ((keyword, typed_ir field.ty expression) :: adapted)
                            rest
                      | None -> adapt ((keyword, value) :: adapted) rest)
                  | None -> adapt ((keyword, value) :: adapted) rest)
            in
            adapt [] pairs
          in
          let rec assoc_record_pairs target = function
            | [] -> Ok target
            | (keyword, value) :: rest -> (
                let fields =
                  match target.ty with
                  | TRecord fields | TNamed_record { fields; _ } -> fields
                  | _ -> []
                in
                match find_field keyword fields with
                | None
                  when Option.is_some
                         (Types.find_record_extension_field fields) ->
                    let dynamic = Types.dynamic_constraint TUnknown in
                    Result.bind (pack_dynamic_value env dynamic value)
                      (fun value ->
                        match
                          Structural_map.extension_assoc target fields keyword
                            value
                        with
                        | Some target -> assoc_record_pairs target rest
                        | None -> assert false)
                | None
                  when (match target.ty with
                       | TNamed_record { extensible = false; _ } -> true
                       | _ -> false)
                  ->
                    Error.error ~code:Error_code.Unresolved ("unknown record field " ^ keyword)
                | _ ->
                    Result.bind (Structural_map.assoc target fields keyword value)
                      (fun target -> assoc_record_pairs target rest))
          in
          let rec compile_vector_pairs acc = function
            | [] -> Ok (List.rev acc)
            | index_form :: value_form :: rest -> (
                match
                  ( compile_expr scope env index_form,
                    compile_expr scope env value_form )
                with
                | (Error _ as err), _ -> err
                | _, (Error _ as err) -> err
              | Ok index, Ok value ->
                  compile_vector_pairs ((index, value) :: acc) rest)
          | _ ->
              Error.error ~code:Error_code.Arity "assoc expects collection followed by key/value pairs"
        in
        let rec compile_map_pairs key_ty value_ty acc = function
          | [] -> Ok (List.rev acc)
          | key_form :: value_form :: rest -> (
              match
                ( compile_expr scope
                    (Env.with_expected_type (Some key_ty) env)
                    key_form,
                  compile_expr scope
                    (Env.with_expected_type (Some value_ty) env)
                    value_form )
              with
              | (Error _ as error), _ | _, (Error _ as error) -> error
              | Ok key, Ok value ->
                  compile_map_pairs key_ty value_ty ((key, value) :: acc) rest)
          | _ ->
              Error.error ~code:Error_code.Arity "assoc expects collection followed by key/value pairs"
        in
        match compile_expr scope env target_form with
          | Error _ as err -> err
          | Ok target -> (
              let target =
                {
                  target with
                  ty =
                    Function_elaborator.infer_named_record scope env target.ty;
                }
              in
              let target =
                match external_record_type target.ty with
                | Some record -> { target with ty = TNamed_record record }
                | None -> target
              in
              let target = unwrap_protocol_value target in
              if pair_forms = [] || List.length pair_forms mod 2 <> 0 then
                match target.ty with
                | TRecord _ | TNamed_record _ ->
                  Error.error ~code:Error_code.Arity
                    "assoc expects map followed by keyword/value pairs"
              | TVector _ ->
                  Error.error ~code:Error_code.Arity
                    "assoc expects vector followed by index/value pairs"
              | _ ->
                  Error.error ~code:Error_code.Arity
                    "assoc expects collection followed by key/value pairs"
              else
                match target.ty with
                | TNamed_record ({ nominal = true; _ } as record) -> (
                    let rec validate_declared_fields = function
                      | [] -> Ok ()
                      | FKeyword keyword :: _value :: rest -> (
                          match find_field keyword record.fields with
                          | Some _ -> validate_declared_fields rest
                          | None ->
                              Error.error ~code:Error_code.Unresolved ("unknown record field " ^ keyword))
                      | _ ->
                          Error.error ~code:Error_code.Semantic
                            "assoc on a deftype requires declared keyword fields"
                    in
                    let rec protocol_assoc_form current = function
                      | key :: value :: rest ->
                          protocol_assoc_form
                            (FList
                               [
                                 FSymbol "IAssociative/-assoc";
                                 current;
                                 key;
                                 value;
                               ])
                            rest
                      | [] -> current
                      | _ -> assert false
                    in
                    let has_non_keyword_key =
                      pair_forms
                      |> List.filteri (fun index _ -> index mod 2 = 0)
                      |> List.exists (function FKeyword _ -> false | _ -> true)
                    in
                    if has_non_keyword_key then
                      compile_expr scope env
                        (protocol_assoc_form target_form pair_forms)
                    else (
                      match validate_declared_fields pair_forms with
                      | Ok () -> (
                          match compile_record_pairs record.fields [] pair_forms with
                          | Error _ as err -> err
                          | Ok pairs ->
                              Result.bind
                                (adapt_dynamic_fields record.fields pairs)
                                (assoc_record_pairs target))
                      | Error declared_error -> (
                      match compile_vector_pairs [] pair_forms with
                        | Error _ as err -> err
                        | Ok [] -> assert false
                        | Ok ((first_key, first_value) :: remaining_pairs) -> (
                        let lookup_method current key value =
                          match
                            compile_deftype_method scope env record "assoc"
                              [ current; key; value ]
                          with
                          | Some _ as result -> result
                          | None ->
                              compile_deftype_method scope env record "-assoc"
                                [ current; key; value ]
                        in
                        let rec apply_pairs current = function
                          | [] -> Ok current
                          | (key, value) :: rest -> (
                              match lookup_method current key value with
                              | None ->
                                  Error.error ~code:Error_code.Arity
                                    "assoc expects an associative deftype"
                              | Some updated ->
                                apply_pairs { updated with ty = target.ty } rest
                            )
                        in
                      match lookup_method target first_key first_value with
                        | Some updated ->
                          apply_pairs
                            { updated with ty = target.ty }
                              remaining_pairs
                        | None -> (
                            Error declared_error)
                      ))))
                | TRecord fields | TNamed_record { fields; _ } -> (
                    match compile_record_pairs fields [] pair_forms with
                    | Error _ as err -> err
                    | Ok pairs ->
                        Result.bind (adapt_dynamic_fields fields pairs)
                          (assoc_record_pairs target))
                | TNil -> (
                    let has_non_keyword_key =
                      pair_forms
                      |> List.filteri (fun index _ -> index mod 2 = 0)
                      |> List.exists (function FKeyword _ -> false | _ -> true)
                    in
                    if not has_non_keyword_key then
                      match compile_record_pairs [] [] pair_forms with
                      | Error _ as err -> err
                      | Ok pairs ->
                          assoc_record_pairs (Structural_map.record_expr [] [])
                            pairs
                    else
                      match compile_vector_pairs [] pair_forms with
                      | Error _ as err -> err
                      | Ok [] -> assert false
                      | Ok pairs ->
                          Result.bind
                            (merge_collection_types "map keys"
                               (List.map (fun (key, _) -> key.ty) pairs))
                            (fun key_ty ->
                              Result.map
                                (fun value_ty ->
                                  let expression =
                                    List.fold_left
                                      (fun map (key, value) ->
                                        apply
                                          (runtime_map_operation
                                             (runtime_map_key_type key_ty key.ty)
                                             "assoc")
                                          [
                                            map;
                                            key.semantic_expr;
                                            value.semantic_expr;
                                          ])
                                      (Semantic_ir.Ident
                                         "Lg_runtime.Runtime_map.empty")
                                      pairs
                                  in
                                  typed_ir
                                    (Types.dynamic_map key_ty value_ty)
                                    expression)
                                (merge_collection_types "map values"
                                   (List.map
                                      (fun (_, value) -> value.ty)
                                      pairs))))
                | TVector _ -> (
                    match compile_vector_pairs [] pair_forms with
                    | Error _ as err -> err
                  | Ok pairs -> (
                        let rec apply_pairs vector_ty expr = function
                          | [] -> Ok (vector_ty, expr)
                          | (index, value) :: rest ->
                              let inner =
                                match vector_ty with
                                | TVector inner -> inner
                                | _ -> assert false
                              in
                              if not (Types.equal index.ty TInt) then
                                Error.error ~code:Error_code.Semantic "assoc vector index must be int"
                              else if Types.equal value.ty TNil then
                                let item_name = "__lg_assoc_vector_item" in
                                let optionalized =
                                  apply "Rrbvec.map"
                                    [
                                      Semantic_ir.Fun
                                        ( [ Semantic_ir.PVar item_name ],
                                          Semantic_ir.Constructor
                                            ( "Some",
                                              Some (Semantic_ir.Ident item_name)
                                            ) );
                                      expr;
                                    ]
                                in
                                apply_pairs (TVector (TNullable inner))
                                  (apply "Lg_runtime.Runtime_vector.assoc"
                                     [
                                       optionalized;
                                       index.semantic_expr;
                                       Semantic_ir.Constructor ("None", None);
                                     ])
                                  rest
                              else if
                                not
                                  (Types.assignable ~policy:Host_boundary
                                     ~expected:inner ~actual:value.ty)
                              then
                                Error.error ~code:Error_code.Semantic
                                  "assoc vector value must match element type"
                              else
                                let vector_ty =
                                  if Types.equal inner value.ty then vector_ty
                                  else TVector value.ty
                                in
                                apply_pairs vector_ty
                                  (apply "Lg_runtime.Runtime_vector.assoc"
                                   [
                                     expr;
                                     index.semantic_expr;
                                     value.semantic_expr;
                                   ])
                                  rest
                        in
                      match apply_pairs target.ty target.semantic_expr pairs with
                        | Error _ as err -> err
                        | Ok (result_ty, expr) -> Ok (typed_ir result_ty expr)))
              | target_ty
                when Types.is_dynamic target_ty
                     ->
                  Error.error ~code:Error_code.Semantic
                    ("assoc requires a statically typed map, vector, or record; \
                      add a concrete type annotation; got "
                   ^ Types.source_name target_ty
                   ^ " while compiling "
                   ^ Macro_expander.string_of_form target_form)
              | (TUnknown | TMeta _ | TVar _) -> (
                  match compile_vector_pairs [] pair_forms with
                  | Error _ as err -> err
                  | Ok [] -> assert false
                  | Ok pairs ->
                      Result.bind
                        (merge_collection_types "map keys"
                           (List.map (fun (key, _) -> key.ty) pairs))
                        (fun key_ty ->
                          Result.map
                            (fun value_ty ->
                              let expression =
                                List.fold_left
                                  (fun map (key, value) ->
                                    apply "Lg_runtime.Runtime_map.assoc"
                                      [
                                        map;
                                        key.semantic_expr;
                                        value.semantic_expr;
                                      ])
                                  target.semantic_expr pairs
                              in
                              typed_ir (Types.dynamic_map key_ty value_ty)
                                expression)
                            (merge_collection_types "map values"
                               (List.map (fun (_, value) -> value.ty) pairs))))
              | ( TNullable
                    (((TRecord fields | TNamed_record { fields; _ }) as inner))
                | TOcaml_app
                    ( "option",
                      [
                        ((TRecord fields | TNamed_record { fields; _ }) as inner);
                      ] ) ) -> (
                  match compile_record_pairs fields [] pair_forms with
                  | Error _ as err -> err
                  | Ok pairs ->
                      Result.bind (adapt_dynamic_fields fields pairs)
                        (fun pairs ->
                          let initial_fields =
                            fields
                            |> List.map (fun (field : field) ->
                                   Option.map
                                     (fun (_, value) ->
                                       (field.ocaml_name, value.semantic_expr))
                                     (List.find_opt
                                        (fun (keyword, _) ->
                                          keyword = field.keyword)
                                        pairs))
                          in
                          if List.exists Option.is_none initial_fields then
                            Error.error ~code:Error_code.Semantic
                              "assoc on an optional record requires every field \
                               when the value is None"
                          else
                            let initial =
                              initial_fields |> List.filter_map Fun.id
                            in
                            let type_name =
                              match inner with
                              | TNamed_record record ->
                                  Some
                                    (Structural_map.record_type_application
                                       record)
                              | TRecord _ -> None
                              | _ -> assert false
                            in
                            let value_name = "__lg_assoc_record" in
                            let target =
                              typed_ir inner
                                (Semantic_ir.Match
                                   ( target.semantic_expr,
                                     [
                                       ( Semantic_ir.PConstructor
                                           ("None", None),
                                         Semantic_ir.Record
                                           (initial, type_name) );
                                       ( Semantic_ir.PConstructor
                                           ( "Some",
                                             Some
                                               (Semantic_ir.PVar value_name) ),
                                         Semantic_ir.Ident value_name );
                                     ] ))
                            in
                            Structural_map.assoc_many target pairs))
              | (TNullable inner | TOcaml_app ("option", [ inner ]))
                when Option.is_some (Types.dynamic_map_types inner) -> (
                  match
                    ( Types.dynamic_map_types inner,
                      compile_vector_pairs [] pair_forms )
                  with
                  | _, (Error _ as err) -> err
                  | _, Ok [] -> assert false
                  | None, Ok _ -> assert false
                  | Some (key_ty, value_ty), Ok pairs ->
                      if
                        not
                          (List.for_all
                             (fun (key, value) ->
                               Types.assignable ~policy:Host_boundary
                                 ~expected:key_ty ~actual:key.ty
                               && Types.assignable ~policy:Host_boundary
                                    ~expected:value_ty ~actual:value.ty)
                             pairs)
                      then
                        Error.error ~code:Error_code.Semantic
                          "assoc key/value types do not match the nullable map"
                      else
                        let value_name = "__lg_assoc_map" in
                        let map =
                          Semantic_ir.Match
                            ( target.semantic_expr,
                              [
                                ( Semantic_ir.PConstructor ("None", None),
                                  Semantic_ir.Ident
                                    "Lg_runtime.Runtime_map.empty" );
                                ( Semantic_ir.PConstructor
                                    ("Some", Some (Semantic_ir.PVar value_name)),
                                  Semantic_ir.Ident value_name );
                              ] )
                        in
                        let expression =
                          List.fold_left
                            (fun map (key, value) ->
                              apply
                                (runtime_map_operation
                                   (runtime_map_key_type key_ty key.ty)
                                   "assoc")
                                [ map; key.semantic_expr; value.semantic_expr ])
                            map pairs
                        in
                        Ok (typed_ir inner expression))
              | (TNullable inner | TOcaml_app ("option", [ inner ]))
                when Types.is_dynamic inner || Types.equal inner TUnknown
                     || match inner with TVar _ -> true | _ -> false ->
                  Error.error ~code:Error_code.Semantic
                    "assoc requires an optional value with a concrete static \
                     map or record type"
                | target_ty -> (
                    match Types.dynamic_map_types target_ty with
                    | None ->
                        Error.error ~code:Error_code.Arity
                          ("assoc expects a map or vector, got "
                          ^ Types.source_name target_ty)
                    | Some (declared_key_ty, declared_value_ty) -> (
                      match
                        compile_map_pairs declared_key_ty declared_value_ty []
                          pair_forms
                      with
                      | Error _ as err -> err
                      | Ok [] -> assert false
                      | Ok pairs ->
                          let unresolved_component ty =
                            Type_solver.is_open ty
                            ||
                            match Types.dynamic_constraint_info ty with
                            | Some capability -> Type_solver.is_open capability
                            | None -> false
                          in
                          let specialize label declared select =
                            if unresolved_component declared then
                              merge_collection_types label
                                (List.map select pairs)
                            else Ok declared
                          in
                          let specialize_values declared =
                            if unresolved_component declared then
                              merge_collection_types "map values"
                                (List.map (fun (_, value) -> value.ty) pairs)
                            else
                              let actuals =
                                List.map (fun (_, value) -> value.ty) pairs
                              in
                              if
                                List.exists
                                  (fun actual ->
                                    not
                                      (Types.assignable
                                         ~policy:Host_boundary ~expected:declared
                                         ~actual))
                                  actuals
                              then
                                merge_collection_types "map values"
                                  (declared :: actuals)
                              else Ok declared
                          in
                          Result.bind
                            (specialize "map keys" declared_key_ty
                               (fun (key, _) -> key.ty))
                            (fun key_ty ->
                              Result.bind
                                (specialize_values declared_value_ty)
                                (fun value_ty ->
                                  let rec validate = function
                                    | [] -> Ok ()
                                    | (key, value) :: rest ->
                                        if
                                          not
                                            (Types.assignable
                                               ~policy:Host_boundary
                                               ~expected:key_ty ~actual:key.ty)
                                        then
                                          heterogeneous_collection_type_error
                                            "map keys" [ key_ty; key.ty ]
                                        else if
                                          not
                                            (Types.assignable
                                               ~policy:Host_boundary
                                               ~expected:value_ty
                                               ~actual:value.ty)
                                        then
                                          heterogeneous_collection_type_error
                                            "map values"
                                            [ value_ty; value.ty ]
                                        else validate rest
                                  in
                                  Result.map
                                    (fun () ->
                                      let initial_map =
                                        if
                                          Types.equal value_ty declared_value_ty
                                          || unresolved_component
                                               declared_value_ty
                                        then target.semantic_expr
                                        else
                                          apply
                                            "Lg_runtime.Runtime_map.map_values"
                                            [
                                              Semantic_ir.Fun
                                                ( [
                                                    Semantic_ir.PVar
                                                      "__lg_assoc_existing_value";
                                                  ],
                                                  coerce_expression_to_type
                                                    value_ty declared_value_ty
                                                    (Semantic_ir.Ident
                                                       "__lg_assoc_existing_value")
                                                );
                                              target.semantic_expr;
                                            ]
                                      in
                                      let expression =
                                        List.fold_left
                                          (fun map (key, value) ->
                                            apply
                                              (runtime_map_operation
                                                 (runtime_map_key_type key_ty
                                                    key.ty)
                                                 "assoc")
                                              [
                                                map;
                                                coerce_expression_to_type key_ty
                                                  key.ty key.semantic_expr;
                                                coerce_expression_to_type
                                                  value_ty value.ty
                                                  value.semantic_expr;
                                              ])
                                          initial_map pairs
                                      in
                                      typed_ir
                                        (Types.dynamic_map key_ty value_ty)
                                        expression)
                                    (validate pairs)))
                          ))))
      | _ -> Error.error ~code:Error_code.Arity "assoc expects collection followed by key/value pairs"
    and compile_dissoc scope env arg_forms =
      match arg_forms with
      | target_form :: key_forms -> (
          match compile_expr scope env target_form with
          | Error _ as err -> err
          | Ok target -> (
              match target.ty with
              | TNamed_record { nominal = true; _ }
                when Protocol.type_satisfies env Core_protocols.map_id target.ty ->
                  Result.bind (compile_args_for scope env key_forms) (fun keys ->
                      let form =
                        List.fold_left2
                          (fun current key_form (key : typed_expr) ->
                            match key.ty with
                            | TNullable _ | TOcaml_app ("option", [ _ ]) ->
                                incr dissoc_expansion_counter;
                                let suffix =
                                  string_of_int !dissoc_expansion_counter
                                in
                                let target_name =
                                  "__lg_dissoc_target_" ^ suffix
                                in
                                let option_name =
                                  "__lg_dissoc_option_" ^ suffix
                                in
                                let payload_name =
                                  "__lg_dissoc_payload_" ^ suffix
                                in
                                FList
                                  [ FSymbol "let";
                                    FVector
                                      [ FSymbol target_name;
                                        current;
                                        FSymbol option_name;
                                        key_form;
                                      ];
                                    FList
                                      [ FSymbol "match";
                                        FSymbol option_name;
                                        FList
                                          [ FSymbol "Some";
                                            FSymbol payload_name;
                                          ];
                                        FList
                                          [ FSymbol "IMap/-dissoc";
                                            FSymbol target_name;
                                            FSymbol payload_name;
                                          ];
                                        FSymbol "None";
                                        FSymbol target_name;
                                      ];
                                  ]
                            | _ ->
                                FList
                                  [ FSymbol "IMap/-dissoc";
                                    current;
                                    key_form;
                                  ])
                          target_form key_forms keys
                      in
                      compile_expr scope env form)
              | TRecord _ | TNamed_record _ ->
                  let rec parse_keywords acc = function
                    | [] -> Ok (List.rev acc)
                    | FKeyword keyword :: rest ->
                        parse_keywords (keyword :: acc) rest
                  | _ -> Error.error ~code:Error_code.Arity "dissoc expects map followed by keywords"
                  in
                  let rec dissoc_keywords target = function
                    | [] -> Ok target
                    | keyword :: rest ->
                        let fields =
                          match target.ty with
                          | TRecord fields | TNamed_record { fields; _ } -> fields
                          | _ -> []
                        in
                        let result =
                          match find_field keyword fields with
                          | None -> (
                              match
                                Structural_map.extension_dissoc target fields
                                  keyword
                              with
                              | Some target -> Ok target
                              | None -> (
                                  match target.ty with
                                  | TRecord _
                                  | TNamed_record { nominal = false; _ } ->
                                      Ok target
                                  | _ ->
                                      Error.error ~code:Error_code.Unresolved
                                        ("cannot dissoc unknown field " ^ keyword)))
                          | Some _ -> Structural_map.dissoc target fields keyword
                        in
                        Result.bind result (fun target ->
                            dissoc_keywords target rest)
                  in
                  Result.bind (parse_keywords [] key_forms)
                    (dissoc_keywords target)
              | target_ty
                when Option.is_some (Types.dynamic_map_types target_ty) ->
                  let key_ty, _ =
                    Option.get (Types.dynamic_map_types target_ty)
                  in
                  Result.bind (compile_args_for scope env key_forms) (fun keys ->
                    let rec prepare_keys prepared = function
                      | [] -> Ok (List.rev prepared)
                      | key :: rest ->
                          let expected_ty =
                            runtime_map_key_type key_ty key.ty
                          in
                          let key =
                            if Types.is_dynamic expected_ty then
                              Result.map
                                (fun semantic_expr ->
                                  { key with ty = expected_ty; semantic_expr })
                                (pack_dynamic_value env expected_ty key)
                            else Ok key
                          in
                          Result.bind key (fun key ->
                              prepare_keys (key :: prepared) rest)
                    in
                    Result.map
                      (fun keys ->
                        typed_ir target.ty
                          (List.fold_left (dissoc_map_key key_ty)
                             target.semantic_expr keys))
                      (prepare_keys [] keys))
              | TNil ->
                  Result.map
                    (fun keys ->
                      typed_ir TNil
                        (Semantic_ir.Sequence
                           (target.semantic_expr
                           :: List.map
                                (fun key -> key.semantic_expr)
                                keys
                           @ [ Semantic_ir.Constructor ("None", None) ])))
                    (compile_args_for scope env key_forms)
              | target_ty
                when Types.is_dynamic target_ty
                     || Types.equal target_ty TUnknown
                     || match target_ty with TVar _ -> true | _ -> false ->
                Result.bind (compile_args_for scope env key_forms) (fun keys ->
                      let rec pack packed = function
                        | [] -> Ok (List.rev packed)
                        | key :: rest -> (
                            match pack_dynamic_scalar env key with
                            | Error _ as error -> error
                            | Ok key -> pack (key :: packed) rest)
                      in
                      Result.map
                        (fun keys ->
                          let result_ty =
                            if Types.is_dynamic target.ty then target.ty
                            else Types.dynamic_constraint TUnknown
                          in
                          typed_ir result_ty
                            (List.fold_left
                               (fun map key ->
                                 apply "Lg_runtime.Runtime_dynamic.dissoc"
                                   [ map; key ])
                               target.semantic_expr keys))
                        (pack [] keys))
              | TNullable inner
                when Types.is_dynamic inner
                     || Types.equal inner TUnknown
                     || match inner with TVar _ -> true | _ -> false ->
                (* (dissoc nil k) => nil, so map over the option *)
                Result.bind (compile_args_for scope env key_forms) (fun keys ->
                    let rec pack packed = function
                      | [] -> Ok (List.rev packed)
                      | key :: rest -> (
                          match pack_dynamic_scalar env key with
                          | Error _ as error -> error
                          | Ok key -> pack (key :: packed) rest)
                    in
                    Result.map
                      (fun keys ->
                        let result_ty =
                          if Types.is_dynamic inner then target.ty
                          else TNullable (Types.dynamic_constraint TUnknown)
                        in
                        typed_ir result_ty
                          (Semantic_ir.Match
                             ( target.semantic_expr,
                               [ ( Semantic_ir.PConstructor ("None", None),
                                   Semantic_ir.Constructor ("None", None) );
                                 ( Semantic_ir.PConstructor
                                     ("Some", Some (Semantic_ir.PVar "map")),
                                   Semantic_ir.Constructor
                                     ( "Some",
                                       Some
                                         (List.fold_left
                                            (fun map key ->
                                              apply
                                                "Lg_runtime.Runtime_dynamic.\
                                                 dissoc"
                                                [ map; key ])
                                            (Semantic_ir.Ident "map")
                                            keys)) ) ] )))
                      (pack [] keys))
              | _ -> Error.error ~code:Error_code.Arity "dissoc expects a map"))
      | _ -> Error.error ~code:Error_code.Arity "dissoc expects map followed by keywords"
    and compile_merge scope env arg_forms =
      match compile_args_for scope env arg_forms with
      | Error _ as err -> err
      | Ok maps
        when List.for_all
               (fun map ->
                 match map.ty with
                 | TRecord _ | TNamed_record _ -> true
                 | _ -> false)
               maps ->
          Structural_map.merge maps
      | Ok maps ->
          let map_types =
            List.map (fun map -> Types.dynamic_map_types map.ty) maps
          in
          if List.exists Option.is_none map_types then
            Error.error ~code:Error_code.Arity
              ("merge expects statically typed maps, got "
              ^ String.concat ", "
                  (List.map
                     (fun map -> Types.source_name map.ty)
                     maps))
          else
            let map_types = List.map Option.get map_types in
            let key_types = List.map fst map_types in
            let value_types = List.map snd map_types in
            Result.bind (merge_collection_types "map keys" key_types)
              (fun key_ty ->
                Result.map
                  (fun value_ty ->
                    let expression =
                      List.fold_left
                        (fun merged map ->
                          apply "Lg_runtime.Runtime_map.merge"
                            [ merged; map.semantic_expr ])
                        (Semantic_ir.Ident "Lg_runtime.Runtime_map.empty")
                        maps
                    in
                    typed_ir (Types.dynamic_map key_ty value_ty) expression)
                  (merge_collection_types "map values" value_types))
    and compile_hash_map scope env arg_forms =
      let rec closed_edn_literal = function
        | FKeyword _ | FString _ | FRegex _ | FInt _ | FFloat _ | FDecimal _
        | FChar _ | FBool _ | FSymbol "nil" ->
            true
        | FVector values -> List.for_all closed_edn_literal values
        | FMap entries ->
            List.for_all
              (fun (key, value) ->
                closed_edn_literal key && closed_edn_literal value)
              entries
        | FSymbol _ | FCoreSymbol _ | FList _ -> false
      in
      let rec parse_pairs acc = function
        | [] -> Ok (List.rev acc)
      | key_form :: value_form :: rest ->
          parse_pairs ((key_form, value_form) :: acc) rest
        | key_form :: [] -> (
            match key_form with
            | FKeyword keyword ->
                Error.error ~code:Error_code.Semantic ("No value supplied for key: " ^ keyword)
            | _ -> Error.error ~code:Error_code.Semantic "No value supplied for key")
      in
      if arg_forms = [] then
        Ok
        (typed_ir
           (Types.dynamic_map (Type_solver.fresh ()) (Type_solver.fresh ()))
             (Semantic_ir.Ident "Lg_runtime.Runtime_map.empty"))
      else if List.length arg_forms mod 2 <> 0 then
        let key = List.hd (List.rev arg_forms) in
        (match key with
        | FKeyword keyword ->
            Error.error ~code:Error_code.Semantic ("No value supplied for key: " ^ keyword)
        | _ -> Error.error ~code:Error_code.Semantic "No value supplied for key")
      else
        match parse_pairs [] arg_forms with
        | Error _ as err -> err
      | Ok pairs
        when List.for_all
               (fun (key, _value) ->
                 match key with FKeyword _ -> true | _ -> false)
               pairs
             && (let rec has_duplicate seen = function
                   | [] -> false
                   | (FKeyword keyword, _) :: rest ->
                       List.mem keyword seen
                       || has_duplicate (keyword :: seen) rest
                   | _ -> false
                 in
                 not (has_duplicate [] pairs)) ->
          compile_map scope env pairs
      | Ok _ ->
          Result.bind (compile_args_for scope env arg_forms) (fun arguments ->
              let rec split keys values = function
                | [] -> (List.rev keys, List.rev values)
                | key :: value :: rest ->
                    split (key :: keys) (value :: values) rest
                | [ _ ] -> assert false
              in
              let keys, values = split [] [] arguments in
              let compile_map key_ty value_ty adapt_key adapt_value =
                let entries =
                  List.map2
                    (fun key value ->
                      Semantic_ir.Tuple [ adapt_key key; adapt_value value ])
                    keys values
                in
                let expression =
                  Semantic_ir.Apply
                    ( Semantic_ir.Ident "Lg_runtime.Runtime_map.of_list",
                      [ Semantic_ir.List entries ] )
                in
                typed_ir (Types.dynamic_map key_ty value_ty) expression
              in
              match
                ( merge_collection_value_types "map keys" keys,
                  merge_collection_value_types "map values" values )
              with
              | Ok key_ty, Ok value_ty ->
                  Ok
                    (compile_map key_ty value_ty
                       (fun key ->
                         coerce_expression_to_type key_ty key.ty
                           key.semantic_expr)
                       (fun value ->
                         coerce_expression_to_type value_ty value.ty
                           value.semantic_expr))
              | (Error _ as error), _
                when not (List.for_all closed_edn_literal arg_forms) ->
                  error
              | _, (Error _ as error)
                when not (List.for_all closed_edn_literal arg_forms) ->
                  error
              | Error _, _ | _, Error _ ->
                  let rec pack_values packed = function
                    | [] -> Ok (List.rev packed)
                    | value :: rest ->
                        Result.bind
                          (Edn_value_elaborator.pack_expression value.ty
                             value.semantic_expr)
                          (fun packed_value ->
                            pack_values (packed_value :: packed) rest)
                  in
                  (match (pack_values [] keys, pack_values [] values) with
                  | Ok packed_keys, Ok packed_values ->
                      let entries =
                        List.map2
                          (fun key value -> Semantic_ir.Tuple [ key; value ])
                          packed_keys packed_values
                      in
                      Ok
                        (typed_ir
                           (Types.dynamic_map Edn_value_elaborator.value_ty
                              Edn_value_elaborator.value_ty)
                           (Semantic_ir.Apply
                              ( Semantic_ir.Ident
                                  "Lg_runtime.Runtime_map.of_list",
                                [ Semantic_ir.List entries ] )))
                  | Error error, _ -> Error error
                  | _, Error error -> Error error))
    and compile_update scope env arg_forms =
    let nested_update_value = "__lg_nested_update_value" in
    let arg_forms =
      match arg_forms with
      | target :: key
        :: (FSymbol "__lg_update" | FCoreSymbol Core_update)
        :: nested_args ->
          let updater =
            FList
              [
                FSymbol "fn";
                FVector [ FSymbol nested_update_value ];
                FList
                  (FSymbol "__lg_update" :: FSymbol nested_update_value
                 :: nested_args);
              ]
          in
          [ target; key; updater ]
      | _ -> arg_forms
    in
    let dynamic = Types.dynamic_constraint TUnknown in
    let nil_predicate_witness value_ty =
      let witness_argument = "__lg_update_nil_predicate_value" in
      let witness_value = Semantic_ir.Ident witness_argument in
      Semantic_ir.Fun
        ( [ Semantic_ir.PVar witness_argument ],
          Expression_support.nil_predicate_expression value_ty witness_value )
    in
    let rec prepare expected argument =
      if Types.is_dynamic expected then pack_dynamic_value env expected argument
      else if Types.is_dynamic argument.ty then
        dynamic_unpack env expected argument.semantic_expr
      else
        match
          ( Types.nil_predicate_constraint_info expected,
            Types.nil_predicate_constraint_info argument.ty )
        with
        | Some value_ty, None ->
            Result.bind (prepare value_ty argument) (fun value ->
                Ok
                  (Semantic_ir.Tuple
                     [ nil_predicate_witness value_ty; value ]))
        | _ ->
            if
              Types.assignable ~policy:Host_boundary ~expected
                ~actual:argument.ty
            then Ok argument.semantic_expr
            else
              Error.error ~code:Error_code.Type_mismatch
                ("update called with incompatible arguments: expected "
               ^ Types.source_name expected ^ ", got "
                ^ Types.source_name argument.ty)
    in
    let instantiate_updater param_tys return_ty extra_args =
      let templates = drop 1 param_tys in
      let actuals = List.map (fun argument -> argument.ty) extra_args in
      let instantiate ty = Types.instantiate_type ~templates ~actuals ty in
      (List.map instantiate param_tys, instantiate return_ty)
    in
    let update_call_signature param_tys return_ty extra_args =
      let call_extra_args =
        if
          Env.target env = Target.Melange
          && extra_args <> []
          && List.length param_tys = 1
        then []
        else extra_args
      in
      if List.length param_tys = List.length call_extra_args + 1 then
        let param_tys, return_ty =
          instantiate_updater param_tys return_ty call_extra_args
        in
        Some (param_tys, return_ty, call_extra_args)
      else None
    in
    let rec prepare_updater_arguments prepared expected arguments =
      match (expected, arguments) with
      | [], [] -> Ok (List.rev prepared)
      | expected :: expected_rest, argument :: argument_rest ->
          Result.bind (prepare expected argument) (fun argument ->
              prepare_updater_arguments (argument :: prepared) expected_rest
                argument_rest)
      | _ -> Error.error ~code:Error_code.Type_mismatch "update function argument count mismatch"
    in
    let compile_static_map target key fn extra_args =
      match Types.dynamic_map_types target.ty with
      | None -> Error.error ~code:Error_code.Arity "update expects a map"
      | Some (key_ty, value_ty) -> (
          let resolved_key_ty =
            match key_ty with TUnknown | TMeta _ | TVar _ -> key.ty | _ -> key_ty
          in
          if
            not
              (Types.assignable ~policy:Host_boundary
                 ~expected:resolved_key_ty ~actual:key.ty)
          then
            Error.error ~code:Error_code.Semantic
              ("update map key must be " ^ Types.source_name resolved_key_ty)
          else
            match fn.ty with
          | TFn (parameter_tys, return_ty) -> (
              match
                update_call_signature parameter_tys return_ty extra_args
              with
              | Some (parameter_tys, return_ty, extra_args) ->
                let key_expression =
                  coerce_expression_to_type resolved_key_ty key.ty
                    key.semantic_expr
                in
                let first_parameter_ty = List.hd parameter_tys in
                let lookup =
                  apply "Lg_runtime.Runtime_map.get_option"
                    [ target.semantic_expr; key_expression ]
                in
                let old_value =
                  match first_parameter_ty with
                  | TNullable constrained
                  | TOcaml_app ("option", [ constrained ]) ->
                      let expression =
                        match Types.nil_predicate_constraint_info constrained with
                        | None -> lookup
                        | Some witness_value_ty ->
                            let found = "__lg_update_present_value" in
                            let witness_argument =
                              "__lg_update_nil_predicate_value"
                            in
                            let witness_value =
                              Semantic_ir.Ident witness_argument
                            in
                            let witness =
                              Semantic_ir.Fun
                                ( [ Semantic_ir.PVar witness_argument ],
                                  Expression_support.nil_predicate_expression
                                    witness_value_ty witness_value )
                            in
                            Semantic_ir.Match
                              ( lookup,
                                [
                                  ( Semantic_ir.PConstructor ("None", None),
                                    Semantic_ir.Constructor ("None", None) );
                                  ( Semantic_ir.PConstructor
                                      ("Some", Some (Semantic_ir.PVar found)),
                                    Semantic_ir.Constructor
                                      ( "Some",
                                        Some
                                          (Semantic_ir.Tuple
                                             [
                                               witness;
                                               Semantic_ir.Ident found;
                                             ]) ) );
                                ] )
                      in
                      typed_ir first_parameter_ty expression
                  | _ ->
                      typed_ir value_ty
                        (apply "Lg_runtime.Runtime_map.get_exn"
                           [ target.semantic_expr; key_expression ])
                in
                Result.bind
                  (prepare_updater_arguments [] parameter_tys
                     (old_value :: extra_args))
                  (fun arguments ->
                    let resolved_value_ty =
                      match value_ty with
                      | TUnknown | TMeta _ | TVar _ -> return_ty
                      | _ -> value_ty
                    in
                    if
                      not
                        (Types.assignable ~policy:Host_boundary
                           ~expected:resolved_value_ty ~actual:return_ty)
                    then
                      Error.error ~code:Error_code.Semantic
                        ("update map value must remain "
                       ^ Types.source_name resolved_value_ty)
                    else
                      let value =
                        Semantic_ir.Apply (fn.semantic_expr, arguments)
                      in
                      Ok
                        (typed_ir
                           (Types.dynamic_map resolved_key_ty resolved_value_ty)
                           (apply "Lg_runtime.Runtime_map.assoc"
                              [
                                target.semantic_expr;
                                key_expression;
                                coerce_expression_to_type resolved_value_ty
                                  return_ty value;
                              ])))
              | None -> Error.error ~code:Error_code.Type_mismatch "update function argument count mismatch")
            | _ -> Error.error ~code:Error_code.Arity "update expects a function")
    in
    let compile_extension target fields keyword fn extra_args =
      match Types.find_record_extension_field fields with
      | None -> Error.error ~code:Error_code.Unresolved ("cannot update unknown field " ^ keyword)
      | Some extension_field -> (
          let old_value =
            typed_ir dynamic
              (apply "Lg_runtime.Runtime_map.get_default"
                 [
                   Structural_map.field_expr target extension_field;
                   Semantic_ir.String keyword;
                   Semantic_ir.Ident "Lg_runtime.Runtime_dynamic.nil";
                 ])
          in
          match fn.ty with
          | TFn (parameter_tys, return_ty) -> (
              match
                update_call_signature parameter_tys return_ty extra_args
              with
              | Some (parameter_tys, return_ty, extra_args) ->
              Result.bind
                (prepare_updater_arguments [] parameter_tys
                   (old_value :: extra_args))
                (fun arguments ->
                  let result =
                    typed_ir return_ty
                      (Semantic_ir.Apply (fn.semantic_expr, arguments))
                  in
                  Result.bind (pack_dynamic_value env dynamic result)
                    (fun result ->
                      match
                        Structural_map.extension_assoc target fields keyword
                          result
                      with
                      | Some target -> Ok target
                      | None -> assert false))
              | None -> Error.error ~code:Error_code.Type_mismatch "update function argument count mismatch")
          | _ -> Error.error ~code:Error_code.Arity "update expects a function")
    in
    let compile_missing_homogeneous_field target fields keyword fn_form fn
        extra_args ~static_ifn_nil =
      let core_unary_updater member =
        match (fn_form, extra_args) with
        | FSymbol name, [] -> core_function_symbol scope env name member
        | _ -> false
      in
      match fn.ty with
      | TFn (parameter_tys, return_ty) -> (
          match update_call_signature parameter_tys return_ty extra_args with
          | Some (parameter_tys, return_ty, extra_args) ->
          let first_parameter_ty = List.hd parameter_tys in
          let accepts_missing =
            match first_parameter_ty with
            | TNullable _ | TOcaml_app ("option", [ _ ]) -> true
            | _ -> false
          in
          if not accepts_missing then
            if static_ifn_nil || core_unary_updater "identity" then
              let result =
                typed_ir TNil (Semantic_ir.Constructor ("None", None))
              in
              Structural_map.assoc target fields keyword result
            else if core_unary_updater "nil?" then
              Structural_map.assoc target fields keyword
                (typed_ir TBool (Semantic_ir.Bool true))
            else
              Error.error ~code:Error_code.Arity
                "update of a missing key requires a nullable updater"
          else
            let old_value =
              typed_ir first_parameter_ty
                (Semantic_ir.Constructor ("None", None))
            in
            Result.bind
              (prepare_updater_arguments [] parameter_tys
                 (old_value :: extra_args))
              (fun arguments ->
                let result =
                  typed_ir return_ty
                    (Semantic_ir.Apply (fn.semantic_expr, arguments))
                in
                Structural_map.assoc target fields keyword result)
          | None -> Error.error ~code:Error_code.Type_mismatch "update function argument count mismatch")
      | _ -> Error.error ~code:Error_code.Arity "update expects a function"
    in
    let static_ifn_nil_updater = function
      | FKeyword _, []
      | FMap [], []
      | FList [ FSymbol "__lg_hash-map" ], []
      | FList [ FSymbol "__lg_hash-set" ], [] ->
          true
      | _ -> false
    in
      match arg_forms with
      | target_form :: FKeyword keyword :: fn_form :: extra_forms -> (
          let static_ifn_nil =
            static_ifn_nil_updater (fn_form, extra_forms)
          in
          let fn_form =
            if static_ifn_nil then
              FList
                [
                  FSymbol "fn";
                  FVector [ FSymbol "__lg_update_static_ifn_arg" ];
                  FSymbol "nil";
                ]
            else fn_form
          in
          let with_context context = function
            | Ok _ as result -> result
            | Error (error : Error.t) ->
                Error { error with message = error.message ^ " " ^ context }
          in
          let target_and_fn =
            Result.bind
              (compile_args_for scope env extra_forms
              |> with_context ("while compiling update arguments for " ^ keyword))
              (fun extra_args ->
                Result.bind
                  (compile_expr scope env target_form
                  |> with_context ("while compiling update target " ^ keyword))
                  (fun target ->
                    let target = unwrap_protocol_value target in
                    let value_ty =
                      match target.ty with
                      | TRecord fields | TNamed_record { fields; _ } -> (
                          match find_field keyword fields with
                          | Some field -> field.ty
                          | None -> dynamic)
                      | target_ty -> (
                          match Types.dynamic_map_types target_ty with
                          | Some (_, value_ty) -> value_ty
                          | None when Types.is_dynamic target_ty -> dynamic
                          | None -> TUnknown)
                    in
                    Result.map
                      (fun fn -> (target, fn, extra_args))
                      (compile_function_arg_for_value scope env
                         (updater_value_type target value_ty)
                         (List.map (fun argument -> argument.ty) extra_args)
                         fn_form
                      |> with_context
                           ("while compiling updater for " ^ keyword))))
          in
          match target_and_fn with
          | Error _ as err -> err
          | Ok (target, fn, extra_args) -> (
            let updater_source_return_ty =
              match fn_form with
              | FSymbol name -> (
                  match lookup_function scope env name with
                  | Ok { ty = TFn (_, return_ty); _ } -> Some return_ty
                  | Ok _ | Error _ -> None)
              | _ -> None
            in
            let updater_row_type =
              match fn_form with
              | FSymbol name -> (
                  match lookup_binding scope env name with
                  | Ok binding ->
                      List.nth_opt binding.row_param_types 0 |> Option.join
                  | Error _ -> None)
              | _ -> None
            in
              match target.ty with
              | TNil ->
                  let empty = Structural_map.record_expr [] [] in
                  compile_missing_homogeneous_field empty [] keyword fn_form fn
                    extra_args ~static_ifn_nil
              | TRecord fields | TNamed_record { fields; _ } -> (
                  match find_field keyword fields with
                  | None
                    when (match target.ty with
                         | TRecord fields ->
                             Types.is_homogeneous_record fields
                      | _ -> false) ->
                      compile_missing_homogeneous_field target fields keyword
                        fn_form fn extra_args ~static_ifn_nil
                  | None ->
                      compile_extension target fields keyword fn extra_args
                  | Some field -> (
                      match fn.ty with
                      | TFn (param_tys, declared_ret) -> (
                        match update_call_signature param_tys declared_ret extra_args with
                        | Some (param_tys, ret, extra_args) ->
                        let param_tys, ret =
                          match param_tys with
                          | value_param :: _ ->
                              let instantiate ty =
                                Types.instantiate_type
                                  ~templates:[ value_param ]
                                  ~actuals:[ field.ty ] ty
                              in
                              (List.map instantiate param_tys, instantiate ret)
                          | [] -> (param_tys, ret)
                        in
                        let param_tys, ret =
                          if Types.is_dynamic field.ty
                          then
                            ( List.map dynamicize_unknown param_tys,
                              dynamicize_unknown ret )
                          else (param_tys, ret)
                          in
                        let type_change =
                          (not (Types.is_dynamic field.ty))
                          && not (Types.equal ret field.ty)
                        in
                        if type_change && Types.equal ret TNil then
                          Structural_map.update_value_as target fields keyword
                            (TNullable field.ty)
                            (Semantic_ir.Constructor ("None", None))
                        else if type_change then
                          Error.error ~code:Error_code.Type_mismatch
                            (Printf.sprintf
                               "cannot update %s as %s because it is already %s"
                               keyword (source_name ret) (source_name field.ty))
                        else
                          let old_value =
                            typed_ir field.ty
                              (Structural_map.field_expr target field)
                          in
                          let prepare_old expected argument =
                            match (expected, argument.ty, updater_row_type) with
                            | ( TRecord row_fields,
                                (TRecord actual_fields
                                | TNamed_record { fields = actual_fields; _ }),
                                Some type_name ) ->
                                let rec project projected = function
                                  | [] ->
                                      Ok
                                        (Semantic_ir.Record
                                           (List.rev projected, Some type_name))
                                  | (row_field : field) :: rest -> (
                                      match
                                        find_field row_field.keyword actual_fields
                                      with
                                      | None ->
                                          Error.error ~code:Error_code.Arity
                                            ("record argument is missing field "
                                           ^ row_field.keyword)
                                      | Some actual_field ->
                                          let value =
                                            typed_ir actual_field.ty
                                              (Structural_map.field_expr argument
                                                 actual_field)
                                          in
                                          Result.bind
                                            (prepare row_field.ty value)
                                            (fun value ->
                                              project
                                                ((row_field.ocaml_name, value)
                                                :: projected)
                                                rest))
                                in
                                project [] row_fields
                            | TRecord row_fields, dynamic_ty, Some type_name
                              when Types.is_dynamic dynamic_ty ->
                                let rec unpack_fields unpacked = function
                                  | [] -> Ok (List.rev unpacked)
                                  | (row_field : field) :: rest ->
                                      let value =
                                        apply "Lg_runtime.Runtime_dynamic.get"
                                          [
                                            argument.semantic_expr;
                                            apply
                                              "Lg_runtime.Runtime_dynamic.keyword"
                                              [
                                                Semantic_ir.String
                                                  row_field.keyword;
                                              ];
                                          ]
                                      in
                                      Result.bind
                                        (dynamic_unpack env row_field.ty value)
                                        (fun value ->
                                          unpack_fields
                                            ((row_field.ocaml_name, value)
                                            :: unpacked)
                                            rest)
                                in
                                Result.map
                                  (fun fields ->
                                    Semantic_ir.Record (fields, Some type_name))
                                  (unpack_fields [] row_fields)
                            | _ -> prepare expected argument
                          in
                          let rec prepare_all prepared expected arguments =
                            match (expected, arguments) with
                            | [], [] -> Ok (List.rev prepared)
                            | ( expected :: expected_rest,
                                argument :: argument_rest ) -> (
                                let prepare_argument =
                                  if prepared = [] then prepare_old else prepare
                                in
                                match prepare_argument expected argument with
                                | Error _ when prepared <> [] ->
                          Error.error ~code:Error_code.Semantic
                                      "update function arguments do not match \
                                       field and extra arguments"
                                | Error _ as error -> error
                                | Ok argument ->
                                    prepare_all (argument :: prepared)
                                      expected_rest argument_rest)
                            | _ ->
                                Error.error ~code:Error_code.Type_mismatch
                                  "update function argument count mismatch"
                          in
                          Result.bind
                            (prepare_all [] param_tys (old_value :: extra_args))
                            (fun arguments ->
                              let result_ty =
                                match updater_source_return_ty with
                                | Some (TNamed_record record)
                                  when not record.nominal ->
                                    TNamed_record record
                                | _ -> (
                                match declared_ret with
                                | TNamed_record record when not record.nominal ->
                                    declared_ret
                                | _ -> ret)
                              in
                              let result =
                                typed_ir result_ty
                                  (Semantic_ir.Apply
                                     (fn.semantic_expr, arguments))
                              in
                              let result =
                                match (field.ty, result.ty) with
                                | TNamed_record target_record,
                                  TNamed_record source_record
                                  when (not target_record.nominal)
                                       && (not source_record.nominal)
                                       && Types.row_compatible
                                            ~expected:field.ty
                                            ~actual:result.ty ->
                                    {
                                      result with
                                      ty = field.ty;
                                      record_values = None;
                                      semantic_expr =
                                        (Structural_map.as_named_record
                                           target_record
                                           { result with record_values = None })
                                          .semantic_expr;
                                    }
                                | TRecord target_fields, TRecord _
                                  when Types.row_compatible
                                         ~expected:field.ty
                                         ~actual:result.ty
                                       &&
                                       (match
                                          Semantic_ir.unlocated
                                            result.semantic_expr
                                        with
                                       | Semantic_ir.Apply _
                                       | Semantic_ir.Uncurried_apply _ ->
                                           true
                                       | _ -> false) ->
                                    {
                                      result with
                                      ty = field.ty;
                                      record_values = None;
                                      semantic_expr =
                                        (Structural_map.record_expr
                                           target_fields
                                           (Structural_map.values_for result
                                              target_fields))
                                          .semantic_expr;
                                    }
                                | _ -> result
                              in
                              let stored =
                                if Types.is_dynamic field.ty then
                                  pack_dynamic_value env field.ty result
                                else
                                  Ok result.semantic_expr
                              in
                              Result.bind stored (fun stored ->
                                  Structural_map.update_value target fields
                                    keyword field.ty stored))
                        | None ->
                            Error.error ~code:Error_code.Type_mismatch "update function argument count mismatch")
                      | _ -> Error.error ~code:Error_code.Arity "update expects a function"))
            | target_ty
              when Option.is_some (Types.dynamic_map_types target_ty) ->
                compile_static_map target
                  (typed_ir TKeyword (Semantic_ir.String keyword))
                  fn extra_args
            | target_ty when Types.is_dynamic target_ty ->
                Error.error ~code:Error_code.Semantic
                  "update requires a statically typed map or record; add a \
                   concrete type annotation"
              | _ -> Error.error ~code:Error_code.Arity "update expects a map"))
      | target_form :: index_form :: fn_form :: extra_forms -> (
          let static_ifn_nil =
            static_ifn_nil_updater (fn_form, extra_forms)
          in
          let vector_index_may_be_missing =
            match (target_form, index_form) with
            | FVector items, FInt index ->
                index < 0 || index >= List.length items
            | _ -> true
          in
          let nil_aware_vector_updater =
            vector_index_may_be_missing
            &&
            (static_ifn_nil
            ||
            match fn_form with
            | FSymbol name when extra_forms = [] ->
                core_function_symbol scope env name "identity"
                || core_function_symbol scope env name "nil?"
            | _ -> false)
          in
          let fn_form =
            if static_ifn_nil then
              FList
                [
                  FSymbol "fn";
                  FVector [ FSymbol "__lg_update_static_ifn_arg" ];
                  FSymbol "nil";
                ]
            else fn_form
          in
          let target_and_fn =
            Result.bind (compile_args_for scope env extra_forms) (fun extra_args ->
                Result.bind (compile_expr scope env target_form) (fun target ->
                    let target = unwrap_protocol_value target in
                    let value_ty =
                      match target.ty with
                      | TVector element_ty ->
                          if nil_aware_vector_updater then
                            TNullable element_ty
                          else element_ty
                      | target_ty -> (
                          match Types.dynamic_map_types target_ty with
                          | Some (_, value_ty) -> value_ty
                          | None when Types.is_dynamic target_ty -> dynamic
                          | None -> TUnknown)
                    in
                    Result.map
                      (fun fn -> (target, fn, extra_args))
                      (compile_function_arg_for_value scope env
                         (updater_value_type target value_ty)
                         (List.map (fun argument -> argument.ty) extra_args)
                         fn_form)))
          in
          match (target_and_fn, compile_expr scope env index_form) with
          | (Error _ as err), _ -> err
          | _, (Error _ as err) -> err
          | Ok (target, fn, extra_args), Ok index -> (
              match (target.ty, index.ty) with
              | TVector inner, TInt -> (
                  match fn.ty with
                  | TFn (param_tys, ret) -> (
                    match update_call_signature param_tys ret extra_args with
                    | Some (param_tys, ret, extra_args) ->
                    if
                      Types.assignable ~policy:Host_boundary
                        ~expected:(List.hd param_tys) ~actual:inner
                         && List.for_all2
                           (fun expected arg ->
                             Types.assignable ~policy:Host_boundary ~expected
                               ~actual:arg.ty)
                              (drop 1 param_tys) extra_args
                    then
                      let first_param_ty = List.hd param_tys in
                      let old_value =
                        match first_param_ty with
                        | TNullable _ | TOcaml_app ("option", [ _ ]) ->
                            typed_ir first_param_ty
                              (Semantic_ir.Match
                                 ( apply "Rrbvec.nth_opt"
                                     [
                                       target.semantic_expr;
                                       index.semantic_expr;
                                     ],
                                   [
                                     ( Semantic_ir.PConstructor
                                         ( "Some",
                                           Some
                                             (Semantic_ir.PVar
                                                "__lg_update_vector_value") ),
                                       Semantic_ir.Constructor
                                         ( "Some",
                                           Some
                                             (Semantic_ir.Ident
                                                "__lg_update_vector_value") )
                                     );
                                     ( Semantic_ir.PConstructor ("None", None),
                                       Semantic_ir.Constructor ("None", None) );
                                   ] ))
                        | _ ->
                            typed_ir inner
                              (apply "Rrbvec.nth"
                                 [
                                   target.semantic_expr;
                                   index.semantic_expr;
                                 ])
                      in
                      let arguments = old_value :: extra_args in
                      Result.bind
                        (prepare_updater_arguments [] param_tys arguments)
                        (fun arguments ->
                          let value_expr =
                            Semantic_ir.Apply (fn.semantic_expr, arguments)
                          in
                          let index_at_end =
                            Semantic_ir.Infix
                              ( "=",
                                index.semantic_expr,
                                apply "Rrbvec.length" [ target.semantic_expr ]
                              )
                          in
                          let set_or_append vector value =
                            Semantic_ir.If
                              ( index_at_end,
                                apply "Rrbvec.push_back" [ vector; value ],
                                apply "Rrbvec.set"
                                  [ vector; index.semantic_expr; value ] )
                          in
                          let nullable_vector_update value_ty value =
                            let item_name = "__lg_update_vector_item" in
                            let lifted_target =
                              apply "Rrbvec.of_list"
                                [
                                  apply "List.map"
                                    [
                                      Semantic_ir.Fun
                                        ( [ Semantic_ir.PVar item_name ],
                                          Semantic_ir.Constructor
                                            ( "Some",
                                              Some
                                                (Semantic_ir.Ident item_name) )
                                        );
                                      apply "Rrbvec.to_list"
                                        [ target.semantic_expr ];
                                    ];
                                ]
                            in
                            Ok
                              (typed_ir (TVector value_ty)
                                 (set_or_append lifted_target value))
                          in
                          let rec pack_edn_value ty expression =
                            match Types.constraint_value_type ty with
                            | TOcaml "Lg_edn_backend.t" -> Ok expression
                            | TNil ->
                                Ok
                                  (Semantic_ir.Sequence
                                     [
                                       expression;
                                       Semantic_ir.Ident
                                         "Lg_runtime.Runtime_metadata.nil";
                                     ])
                            | TBool ->
                                Ok
                                  (apply
                                     "Lg_runtime.Runtime_metadata.of_bool"
                                     [ expression ])
                            | TInt | TOcaml "int" ->
                                Ok
                                  (apply "Lg_runtime.Runtime_metadata.of_int"
                                     [ expression ])
                            | TNullable inner
                            | TOcaml_app ("option", [ inner ]) ->
                                let value_name = "__lg_update_edn_value" in
                                Result.map
                                  (fun packed ->
                                    Semantic_ir.Match
                                      ( expression,
                                        [
                                          ( Semantic_ir.PConstructor
                                              ("None", None),
                                            Semantic_ir.Ident
                                              "Lg_runtime.Runtime_metadata.nil"
                                          );
                                          ( Semantic_ir.PConstructor
                                              ( "Some",
                                                Some
                                                  (Semantic_ir.PVar value_name)
                                              ),
                                            packed );
                                        ] ))
                                  (pack_edn_value inner
                                     (Semantic_ir.Ident value_name))
                            | _ ->
                                Error.error ~code:Error_code.Semantic
                                  "vector update result requires a closed sum \
                                   element type"
                          in
                          let edn_vector_update () =
                            let item_name = "__lg_update_edn_item" in
                            match
                              ( pack_edn_value inner
                                  (Semantic_ir.Ident item_name),
                                pack_edn_value ret value_expr )
                            with
                            | (Error _ as error), _ | _, (Error _ as error) ->
                                error
                            | Ok packed_item, Ok packed_value ->
                                let edn_target =
                                  apply "Rrbvec.of_list"
                                    [
                                      apply "List.map"
                                        [
                                          Semantic_ir.Fun
                                            ( [ Semantic_ir.PVar item_name ],
                                              packed_item );
                                          apply "Rrbvec.to_list"
                                            [ target.semantic_expr ];
                                        ];
                                    ]
                                in
                                Ok
                                  (typed_ir
                                     (TVector (TOcaml "Lg_edn_backend.t"))
                                     (set_or_append edn_target packed_value))
                          in
                          if Types.equal ret inner then
                            Ok
                              (typed_ir target.ty
                                 (set_or_append target.semantic_expr value_expr))
                          else if
                            match inner with
                            | TUnknown | TMeta _ | TVar _ -> true
                            | _ -> false
                          then
                            Ok
                              (typed_ir (TVector ret)
                                 (set_or_append target.semantic_expr value_expr))
                          else if Types.equal ret TNil then
                            nullable_vector_update (TNullable inner)
                              (Semantic_ir.Constructor ("None", None))
                          else if
                            match ret with
                            | TNullable ret_inner
                            | TOcaml_app ("option", [ ret_inner ]) ->
                                Types.assignable ~policy:Host_boundary
                                  ~expected:inner ~actual:ret_inner
                            | _ -> false
                          then
                            nullable_vector_update ret value_expr
                          else
                            match edn_vector_update () with
                            | Ok _ as result -> result
                            | Error _ ->
                            (* Clojure update may change the element type;
                               repack the whole vector as dynamic *)
                            let dynamic = Types.dynamic_constraint TUnknown in
                            let item_name = "__lg_update_item" in
                            let item =
                              typed_ir inner (Semantic_ir.Ident item_name)
                            in
                            match
                              ( pack_dynamic_value env dynamic
                                  (typed_ir ret value_expr),
                                pack_dynamic_value env dynamic item )
                            with
                            | (Error _ as error), _ -> error
                            | _, (Error _ as error) -> error
                            | Ok packed_value, Ok packed_item ->
                                Ok
                                  (typed_ir (TVector dynamic)
                                     (apply "Rrbvec.set"
                                        [
                                          apply "Rrbvec.of_list"
                                            [
                                              apply "List.map"
                                                [
                                                  Semantic_ir.Fun
                                                    ( [
                                                        typed_dynamic_item_pattern
                                                          env item_name inner;
                                                      ],
                                                      packed_item );
                                                  apply "Rrbvec.to_list"
                                                    [ target.semantic_expr ];
                                                ];
                                            ];
                                          index.semantic_expr;
                                          packed_value;
                                        ])))
                    else
                      Error.error ~code:Error_code.Semantic
                        "update function arguments do not match vector element \
                         and extra arguments"
                    | None ->
                        Error.error ~code:Error_code.Semantic
                          "update function arguments do not match vector element \
                           and extra arguments")
                  | _ -> Error.error ~code:Error_code.Arity "update expects a function")
              | TVector _, _ -> Error.error ~code:Error_code.Semantic "update vector index must be int"
            | target_ty, _
              when Option.is_some (Types.dynamic_map_types target_ty) ->
                compile_static_map target index fn extra_args
            | target_ty, _ when Types.is_dynamic target_ty ->
                Error.error ~code:Error_code.Semantic
                  "update requires a statically typed map or vector; add a \
                   concrete type annotation"
              | _ -> Error.error ~code:Error_code.Arity "update expects a map or vector"))
    | _ ->
        Error.error ~code:Error_code.Semantic
          "update expects collection, key/index, function, and optional \
           arguments"
    and compile_select_keys scope env arg_forms =
      let parse_keywords key_forms =
        let rec parse acc = function
          | [] -> Ok (List.rev acc)
          | FKeyword keyword :: rest -> parse (keyword :: acc) rest
          | _ -> Error.error ~code:Error_code.Arity "select-keys expects a vector of keywords"
        in
        parse [] key_forms
      in
      let adapt_key_sequence key_ty actual_ty sequence =
        if Types.is_dynamic key_ty && Types.is_dynamic actual_ty then
          Ok sequence
        else if Types.is_dynamic key_ty then
          let item_name = "__lg_select_keys_item" in
          let item = typed_ir actual_ty (Semantic_ir.Ident item_name) in
          Result.map
            (fun item ->
              apply "Lg_runtime.Runtime_seq.map"
                [ Semantic_ir.Fun ([ Semantic_ir.PVar item_name ], item); sequence ])
            (pack_dynamic_value env key_ty item)
        else if Types.is_dynamic actual_ty then
          let item_name = "__lg_select_keys_item" in
          Result.map
            (fun item ->
              apply "Lg_runtime.Runtime_seq.map"
                [ Semantic_ir.Fun ([ Semantic_ir.PVar item_name ], item); sequence ])
            (dynamic_unpack env key_ty (Semantic_ir.Ident item_name))
        else if
          Result.is_ok (Type_solver.unify Type_solver.empty key_ty actual_ty)
        then
          Ok sequence
        else Error.error ~code:Error_code.Semantic "select-keys key type must match map key type"
      in
      let select_open_record target fields keywords extension_field =
        let dynamic = Types.dynamic_constraint TUnknown in
        let selected =
          apply "Lg_runtime.Runtime_map.select_keys"
            [
              Structural_map.field_expr target extension_field;
              apply "List.to_seq"
                [ Semantic_ir.List (List.map (fun key -> Semantic_ir.String key) keywords) ];
            ]
        in
        let rec add_known selected = function
          | [] -> Ok selected
          | keyword :: rest -> (
              match find_field keyword fields with
              | None -> add_known selected rest
              | Some field when Types.is_record_extension_field field ->
                  add_known selected rest
              | Some field -> (
                  let value = Structural_map.field_expr target field in
                  match field.ty with
                  | TNullable payload_ty
                  | TOcaml_app ("option", [ payload_ty ]) ->
                      let value_name = "__lg_select_keys_optional_field" in
                      let payload =
                        typed_ir payload_ty (Semantic_ir.Ident value_name)
                      in
                      Result.bind (pack_dynamic_value env dynamic payload)
                        (fun packed ->
                          let selected =
                            Semantic_ir.Match
                              ( value,
                                [
                                  ( Semantic_ir.PConstructor ("None", None),
                                    selected );
                                  ( Semantic_ir.PConstructor
                                      ("Some", Some (Semantic_ir.PVar value_name)),
                                    apply "Lg_runtime.Runtime_map.assoc"
                                      [ selected; Semantic_ir.String keyword; packed ] );
                                ] )
                          in
                          add_known selected rest)
                  | value_ty ->
                      Result.bind
                        (pack_dynamic_value env dynamic (typed_ir value_ty value))
                        (fun packed ->
                          add_known
                            (apply "Lg_runtime.Runtime_map.assoc"
                               [ selected; Semantic_ir.String keyword; packed ])
                            rest)))
        in
        Result.map
          (fun selected ->
            typed_ir (Types.dynamic_map TKeyword dynamic) selected)
          (add_known selected keywords)
      in
      let select_lookup_record target record keywords =
        let key_name = "__lg_select_keys_lookup_key" in
        let key = typed_ir TKeyword (Semantic_ir.Ident key_name) in
        let lookup =
          match
            compile_deftype_method scope env record "valAt" [ target; key ]
          with
          | Some _ as result -> result
          | None ->
              compile_deftype_method scope env record "-lookup" [ target; key ]
        in
        Option.map
          (fun lookup ->
            match lookup.ty with
            | TNullable value_ty
            | TOcaml_app ("option", [ value_ty ]) ->
                Ok
                  (typed_ir
                     (Types.dynamic_map TKeyword value_ty)
                     (apply "Lg_runtime.Runtime_map.select_options"
                        [
                          Semantic_ir.Fun
                            ([ Semantic_ir.PVar key_name ], lookup.semantic_expr);
                          apply "List.to_seq"
                            [
                              Semantic_ir.List
                                (List.map
                                   (fun keyword ->
                                     Semantic_ir.String keyword)
                                   keywords);
                            ];
                        ]))
            | _ ->
                Error.error ~code:Error_code.Semantic
                  "select-keys requires ILookup to return an option")
          lookup
      in
      match arg_forms with
      | [ target_form; keys_form ] -> (
          match compile_expr scope env target_form with
          | Error _ as error -> error
          | Ok target -> (
              match (target.ty, keys_form) with
              | TNamed_record ({ fields; _ } as record), FVector key_forms ->
                  Result.bind (parse_keywords key_forms) (fun keywords ->
                      match Types.find_record_extension_field fields with
                      | Some extension_field ->
                          select_open_record target fields keywords
                            extension_field
                      | None
                        when List.exists
                               (fun keyword ->
                                 Option.is_none (find_field keyword fields))
                               keywords -> (
                          match
                            select_lookup_record target record keywords
                          with
                          | Some result -> result
                          | None ->
                              Structural_map.select_keys target fields keywords)
                      | None ->
                          Structural_map.select_keys target fields keywords)
              | TRecord fields, FVector key_forms ->
                  Result.bind (parse_keywords key_forms) (fun keywords ->
                      Structural_map.select_keys target fields keywords)
              | (TRecord _ | TNamed_record _), _ ->
                  Error.error ~code:Error_code.Arity "select-keys expects a vector of keywords"
              | target_ty, _ -> (
                  match Types.dynamic_map_types target_ty with
                  | None when Types.is_dynamic target_ty -> (
                      match compile_expr scope env keys_form with
                      | Error _ as error -> error
                      | Ok keys -> (
                          match Collection_capability.to_seq_expr env keys with
                          | Error _ ->
                              Error.error ~code:Error_code.Arity
                                "select-keys expects a Seqable key collection"
                          | Ok (actual_ty, sequence) ->
                              Result.map
                                (fun sequence ->
                                  typed_ir target_ty
                                    (apply
                                       "Lg_runtime.Runtime_dynamic.select_keys"
                                       [ target.semantic_expr; sequence ]))
                                (adapt_key_sequence
                                   (Types.dynamic_constraint TUnknown)
                                   actual_ty sequence)))
                  | None -> Error.error ~code:Error_code.Arity "select-keys expects a map"
                  | Some (key_ty, _value_ty) -> (
                      match compile_expr scope env keys_form with
                      | Error _ as error -> error
                      | Ok keys -> (
                          match Collection_capability.to_seq_expr env keys with
                          | Error _ ->
                              Error.error ~code:Error_code.Arity
                                "select-keys expects a Seqable key collection"
                          | Ok (actual_ty, sequence) ->
                              Result.map
                                (fun sequence ->
                                  typed_ir target_ty
                                    (apply
                                       (if Types.is_dynamic key_ty then
                                          "Lg_runtime.Runtime_map.select_keys_dynamic"
                                        else
                                          "Lg_runtime.Runtime_map.select_keys")
                                       [ target.semantic_expr; sequence ]))
                                (adapt_key_sequence key_ty actual_ty sequence))))))
      | _ -> Error.error ~code:Error_code.Arity "select-keys expects map and key collection"
    and compile_contains scope env arg_forms =
      let env = Env.with_expected_type None env in
      let compile_deftype_contains target key =
        let record_target =
          match target.ty with
          | TNamed_record record -> Some (record, target.semantic_expr)
          | TNullable (TNamed_record record)
          | TOcaml_app ("option", [ TNamed_record record ]) ->
              Some
                ( record,
                  Semantic_ir.Apply
                    ( Semantic_ir.Ident "Option.get",
                      [ target.semantic_expr ] ) )
          | _ -> None
        in
        Option.bind record_target (fun (record, semantic_expr) ->
            let method_scope =
              String.concat "/" (Type_id.owner record.type_id)
            in
            let receiver = typed_ir (TNamed_record record) semantic_expr in
            match
              compile_deftype_method method_scope env record "-contains-key?"
                [ receiver; key ]
            with
            | Some result -> Some result
            | None ->
                compile_deftype_method method_scope env record "-lookup"
                  [ receiver; key ]
                |> Option.map (fun found ->
                       typed_ir TBool
                         (Semantic_ir.Apply
                            ( Semantic_ir.Ident "Option.is_some",
                              [ found.semantic_expr ] ))))
      in
      let compile_dynamic_set_contains target element_ty candidate =
        let scalar_conversion =
          match element_ty with
          | TInt -> Some ("is_int", "as_int")
          | TFloat -> Some ("is_float", "as_float")
          | TString -> Some ("is_string", "as_string")
          | TSymbol -> Some ("is_symbol", "as_symbol")
          | TKeyword -> Some ("is_keyword", "as_keyword")
          | TBool -> Some ("is_bool", "as_bool")
          | _ -> None
        in
        match scalar_conversion with
        | Some (predicate, conversion) ->
            Result.map
              (fun set_module ->
                let set_name = "__lg_static_set" in
                let candidate_name = "__lg_erased_set_candidate" in
                let candidate_value = Semantic_ir.Ident candidate_name in
                typed_ir TBool
                  (Semantic_ir.Let
                     ( [
                         ( Semantic_ir.PVar set_name,
                           target.semantic_expr );
                         ( Semantic_ir.PVar candidate_name,
                           candidate.semantic_expr );
                       ],
                       Semantic_ir.If
                         ( Semantic_ir.Apply
                             ( Semantic_ir.Ident
                                 ("Lg_runtime.Runtime_dynamic." ^ predicate),
                               [ candidate_value ] ),
                           Semantic_ir.Apply
                             ( Semantic_ir.Ident (set_module ^ ".mem"),
                               [
                                 Semantic_ir.Apply
                                   ( Semantic_ir.Ident
                                       ("Lg_runtime.Runtime_dynamic."
                                      ^ conversion),
                                     [ candidate_value ] );
                                 Semantic_ir.Ident set_name;
                               ] ),
                           Semantic_ir.Bool false ) )))
              (set_module_name env element_ty)
        | None ->
            let dynamic = Types.dynamic_constraint TUnknown in
            Result.map
              (fun target ->
                typed_ir TBool
                  (Semantic_ir.Apply
                     ( Semantic_ir.Ident
                         "Lg_runtime.Runtime_dynamic.contains",
                       [ target; candidate.semantic_expr ] )))
              (pack_dynamic_value env dynamic target)
      in
      let compile_collection_contains target value =
        let target = unwrap_protocol_constraints target in
        match (target.ty, value.ty) with
        | target_ty, _
          when Option.is_some (Types.contains_constraint_info target_ty) ->
            Collection_capability.contains_expr target value
            |> Option.value
                 ~default:
                   (Error.error ~code:Error_code.Arity
                      "contains? expects a static membership witness")
        | TNil, _ -> Ok (typed_ir TBool (Semantic_ir.Bool false))
        | _, _
          when Option.is_some
                 (Env.find_optional_map_adapter
                    (Types.constraint_value_type target.ty) env) ->
            let key_ty, _, adapter =
              Option.get
                (Env.find_optional_map_adapter
                   (Types.constraint_value_type target.ty) env)
            in
            if
              not
                (Types.assignable ~policy:Host_boundary ~expected:key_ty
                   ~actual:value.ty)
            then
              Error.error ~code:Error_code.Semantic
                ("contains? value type must match map key type: expected "
               ^ source_name key_ty ^ ", got " ^ source_name value.ty)
            else
              let key =
                if Types.is_dynamic key_ty && not (Types.is_dynamic value.ty)
                then pack_dynamic_value env key_ty value
                else Ok value.semantic_expr
              in
              Result.map
                (fun key ->
                  let map_name = "__lg_optional_adapter_map" in
                  typed_ir TBool
                    (Semantic_ir.Match
                       ( Semantic_ir.Apply
                           ( Semantic_ir.Ident adapter,
                             [ target.semantic_expr ] ),
                         [
                           ( Semantic_ir.PConstructor ("None", None),
                             Semantic_ir.Bool false );
                           ( Semantic_ir.PConstructor
                               ("Some", Some (Semantic_ir.PVar map_name)),
                             Semantic_ir.Apply
                               ( Semantic_ir.Ident
                                   (runtime_map_operation
                                      (runtime_map_key_type key_ty value.ty)
                                      "mem"),
                                 [ Semantic_ir.Ident map_name; key ] ) );
                         ] )))
                key
        | TOcaml_app ("Lg_runtime.Runtime_transient.set", [ element_type ]), _
          when Types.equal element_type TUnknown
               || Types.same_shape element_type value.ty ->
            let contains =
              if Types.is_dynamic element_type || Types.is_dynamic value.ty then
                "Lg_runtime.Runtime_transient.set_mem_dynamic"
              else "Lg_runtime.Runtime_transient.set_mem"
            in
            Ok
              (typed_ir TBool
                 (Semantic_ir.Apply
                  ( Semantic_ir.Ident contains,
                      [ target.semantic_expr; value.semantic_expr ] )))
        | TOcaml_app ("Lg_runtime.Runtime_transient.set", _), _ ->
            Error.error ~code:Error_code.Semantic
              "contains? value type must match transient set element type"
        | TSet (TUnknown | TMeta _), _ when not (Types.is_dynamic value.ty) ->
            Ok
              (typed_ir TBool
                 (Semantic_ir.Apply
                    ( Semantic_ir.Ident "Lg_runtime.Runtime_poly_set.mem",
                      [ value.semantic_expr; target.semantic_expr ] )))
        | TSet inner, _ when Types.is_dynamic value.ty ->
            compile_dynamic_set_contains target inner value
        | TSet inner, _
          when Types.same_shape inner value.ty
               || Types.assignable ~policy:Host_boundary ~expected:inner
                    ~actual:value.ty ->
            Result.bind (set_module_name env inner) (fun set_module ->
                   (if Types.equal inner value.ty then Ok value.semantic_expr
                    else
                      match inner with
                      | TNullable _ | TOcaml_app ("option", [ _ ]) ->
                          Ok
                            (coerce_expression_to_type inner value.ty
                               value.semantic_expr)
                      | _ -> coerce_set_element inner value)
                   |> Result.map (fun value ->
                          typed_ir TBool
                            (Semantic_ir.Apply
                               (Semantic_ir.Ident (set_module ^ ".mem"),
                                [ value; target.semantic_expr ]))))
        | TSet inner, _ ->
            Error.error ~code:Error_code.Semantic
              (Printf.sprintf
                 "contains? value type must match set element type: expected %s, got %s"
                 (Types.source_name inner) (Types.source_name value.ty))
        | TVector _, TInt ->
            Ok
              (typed_ir TBool
                 (Semantic_ir.Infix
                    ( "&&",
                      Semantic_ir.Infix
                        (">=", value.semantic_expr, Semantic_ir.Int 0),
                      Semantic_ir.Infix
                        ( "<",
                          value.semantic_expr,
                          apply "Rrbvec.length" [ target.semantic_expr ] ) )))
        | TVector _, _ -> Error.error ~code:Error_code.Semantic "contains? vector index must be int"
        | TArray _, TInt ->
            Ok
              (typed_ir TBool
                 (Semantic_ir.Infix
                    ( "&&",
                      Semantic_ir.Infix
                        (">=", value.semantic_expr, Semantic_ir.Int 0),
                      Semantic_ir.Infix
                        ( "<",
                          value.semantic_expr,
                          apply "Array.length" [ target.semantic_expr ] ) )))
        | TArray _, _ -> Ok (typed_ir TBool (Semantic_ir.Bool false))
        | TString, TInt ->
            Ok
              (typed_ir TBool
                 (Semantic_ir.Infix
                    ( "&&",
                      Semantic_ir.Infix
                        (">=", value.semantic_expr, Semantic_ir.Int 0),
                      Semantic_ir.Infix
                        ( "<",
                          value.semantic_expr,
                          apply "String.length" [ target.semantic_expr ] ) )))
        | TString, _ -> Ok (typed_ir TBool (Semantic_ir.Bool false))
        | (TList _ | TSeq _), _ -> Ok (typed_ir TBool (Semantic_ir.Bool false))
        | TOcaml "Lg_edn_backend.t", _ ->
            Result.map
              (fun value ->
                typed_ir TBool
                  (Semantic_ir.Apply
                     ( Semantic_ir.Ident "Lg_runtime.Runtime_edn.contains",
                       [ target.semantic_expr; value ] )))
              (pack_closed_edn_value value)
        | (TInt | TFloat | TBool | TChar | TKeyword | TSymbol), _ ->
            Ok (typed_ir TBool (Semantic_ir.Bool false))
        | TMap_keys, TKeyword ->
            Ok
              (typed_ir TBool
                 (Semantic_ir.Apply
                    ( Semantic_ir.Ident "Lg_runtime.Core_set.String_set.mem",
                      [ value.semantic_expr; target.semantic_expr ] )))
        | TMap_keys, _ -> Error.error ~code:Error_code.Semantic "contains? map key must be a keyword"
        | (TRecord _ | TNamed_record _), TKeyword ->
            Result.map
              (fun adapter ->
                typed_ir TBool
                  (Semantic_ir.Apply (adapter, [ value.semantic_expr ])))
              (Collection_capability.contains_adapter target)
        | (TRecord _ | TNamed_record _), _ ->
            Ok (typed_ir TBool (Semantic_ir.Bool false))
        | target_ty, _ when Types.is_dynamic target_ty ->
            Result.map
              (fun value ->
                typed_ir TBool
                  (Semantic_ir.Apply
                   ( Semantic_ir.Ident "Lg_runtime.Runtime_dynamic.contains",
                       [ target.semantic_expr; value ] )))
              (Multimethod_dynamic_boundary.convert_typed_value value)
        | target_ty, _ -> (
            match Types.dynamic_map_types target_ty with
            | Some (key_ty, _)
              when Types.assignable ~policy:Host_boundary ~expected:key_ty
                     ~actual:value.ty ->
                Ok
                  (typed_ir TBool
                     (Semantic_ir.Apply
                        ( Semantic_ir.Ident
                            (runtime_map_operation
                               (runtime_map_key_type key_ty value.ty)
                               "mem"),
                          [ target.semantic_expr; value.semantic_expr ] )))
            | None
              when Types.equal target_ty TUnknown
                 || match target_ty with TVar _ -> true | _ -> false ->
                Ok
                  (typed_ir TBool
                     (Semantic_ir.Apply
                        ( Semantic_ir.Ident "Lg_runtime.Runtime_map.mem",
                          [ target.semantic_expr; value.semantic_expr ] )))
            | _ ->
                Error.error ~code:Error_code.Arity
                  ("contains? expects a map, set, or vector, got "
                 ^ source_name target.ty))
      in
      match arg_forms with
    | [ target_form; FKeyword keyword ] -> (
          match compile_expr scope env target_form with
          | Error _ as err -> err
          | Ok target -> (
              let key =
                typed_ir TKeyword (Semantic_ir.String keyword)
              in
              match compile_deftype_contains target key with
              | Some result -> Ok result
              | None -> (
                  match target.ty with
                  | TNamed_record { nominal = true; _ }
                    when Protocol.type_satisfies env Core_protocols.lookup_id
                           target.ty ->
                      compile_expr scope env
                        (FList
                           [
                             FSymbol "some?";
                             FList
                               [
                                 FSymbol "ILookup/-lookup";
                                 target_form;
                                 FKeyword keyword;
                               ];
                           ])
                  | TRecord fields | TNamed_record { fields; _ } ->
                      if Option.is_some (find_field keyword fields) then
                        Ok (typed_ir TBool (Semantic_ir.Bool true))
                      else (
                        match
                          Structural_map.extension_contains target fields
                            keyword
                        with
                        | Some result -> Ok result
                        | None ->
                            Ok (typed_ir TBool (Semantic_ir.Bool false)))
                  | _ -> compile_collection_contains target key)))
    | [ target_form; value_form ] -> (
        match
          (compile_expr scope env target_form, compile_expr scope env value_form)
        with
          | (Error _ as err), _ -> err
          | _, (Error _ as err) -> err
          | Ok target, Ok value -> (
              match compile_deftype_contains target value with
              | Some result -> Ok result
              | None -> (
                  match target.ty with
                  | TNamed_record { nominal = true; _ }
                    when Protocol.type_satisfies env Core_protocols.lookup_id
                           target.ty ->
                      compile_expr scope env
                        (FList
                           [
                             FSymbol "some?";
                             FList
                               [
                                 FSymbol "ILookup/-lookup";
                                 target_form;
                                 value_form;
                               ];
                           ])
                  | TNamed_record { nominal = true; _ } ->
                      compile_expr scope env
                        (FList
                           [
                             FSymbol "IAssociative/-contains-key?";
                             target_form;
                             value_form;
                           ])
                  | _ -> compile_collection_contains target value)))
      | _ -> Error.error ~code:Error_code.Arity "contains? expects collection and key"
    and compile_keys scope env arg_forms =
      match compile_args_for scope env arg_forms with
      | Error _ as err -> err
      | Ok [ target ] -> (
          let seq_of_mapped_entries projector element_ty expression =
            typed_ir (Types.next_seq element_ty)
              (Semantic_ir.Apply
                 ( Semantic_ir.Ident "Seq.map",
                   [
                     Semantic_ir.Ident projector;
                     Semantic_ir.Apply
                       ( Semantic_ir.Ident "Lg_runtime.Runtime_map.to_seq",
                         [ expression ] );
                   ] ))
          in
          let map_keys key_type expression =
            seq_of_mapped_entries "fst" key_type expression
          in
          match target.ty with
          | target_ty when Types.is_dynamic target_ty ->
              Ok
                (typed_ir target_ty
                   (Semantic_ir.Apply
                      ( Semantic_ir.Ident "Lg_runtime.Runtime_dynamic.keys",
                        [ target.semantic_expr ] )))
          | target_ty -> (
              match
                Types.dynamic_map_types (Types.constraint_value_type target_ty)
              with
              | Some (key_type, _) ->
                  Ok (map_keys key_type target.semantic_expr)
              | None
                when Types.equal target_ty TUnknown
                     || match target_ty with TVar _ -> true | _ -> false ->
                  let dynamic = Types.dynamic_constraint TUnknown in
                  Result.map
                    (fun target ->
                      typed_ir dynamic
                        (Semantic_ir.Apply
                           ( Semantic_ir.Ident "Lg_runtime.Runtime_dynamic.keys",
                             [ target ] )))
                    (pack_dynamic_value env dynamic target)
              | None -> (
                  match target_ty with
                  | TNamed_record { nominal = true; _ }
                    when Protocol.type_satisfies env Core_protocols.map_id
                           target_ty ->
                      let target_form = List.hd arg_forms in
                      Result.bind
                        (compile_expr scope env
                           (FList
                              [ FSymbol "ISeqable/-seq"; target_form ]))
                        (fun entries ->
                          match Collection_capability.element_type env entries with
                          | Some (TTuple [ key_ty; _ ]) ->
                              Ok
                                (typed_ir (TSeq key_ty)
                                   (Semantic_ir.Apply
                                      ( Semantic_ir.Ident "Seq.map",
                                        [ Semantic_ir.Ident "fst";
                                          entries.semantic_expr;
                                        ] )))
                          | Some entry_ty ->
                              Error.error ~code:Error_code.Arity
                                ("keys expects map entries, got "
                               ^ source_name entry_ty)
                          | None ->
                              Error.error ~code:Error_code.Arity
                                "keys requires a statically typed map entry sequence")
                  | TRecord fields | TNamed_record { fields; _ } ->
              let visible_fields = Types.record_constructor_fields fields in
              let declared_keys =
                Semantic_ir.List
                  (List.map
                     (fun (field : field) ->
                       Semantic_ir.String field.keyword)
                     visible_fields)
              in
              let keys =
                match Types.find_record_extension_field fields with
                | None -> declared_keys
                | Some extension_field ->
                    Semantic_ir.Apply
                      ( Semantic_ir.Ident "List.append",
                        [
                          declared_keys;
                          Semantic_ir.Apply
                            ( Semantic_ir.Ident "List.map",
                              [
                                Semantic_ir.Ident "fst";
                                Semantic_ir.Apply
                                  ( Semantic_ir.Ident
                                      "Lg_runtime.Runtime_map.to_list",
                                    [
                                      Structural_map.field_expr target
                                        extension_field;
                                    ] );
                              ] );
                        ] )
              in
              Ok
                (typed_ir (Types.next_seq TKeyword)
                   (Semantic_ir.Apply
                      ( Semantic_ir.Ident "List.to_seq", [ keys ] )))
                  | _ -> Error.error ~code:Error_code.Arity "keys expects a map")))
      | Ok _ -> Error.error ~code:Error_code.Arity "keys expects 1 arguments"
    and compile_vals scope env arg_forms =
      match compile_args_for scope env arg_forms with
      | Error _ as err -> err
      | Ok [ target ] ->
          if Types.is_dynamic target.ty then
            Ok
              (typed_ir target.ty
                 (Semantic_ir.Apply
                    ( Semantic_ir.Ident "Lg_runtime.Runtime_dynamic.vals",
                      [ target.semantic_expr ] )))
          else if
            Types.equal target.ty TUnknown
            || match target.ty with TVar _ -> true | _ -> false
          then
            let dynamic = Types.dynamic_constraint TUnknown in
            Result.map
              (fun target ->
                typed_ir dynamic
                  (Semantic_ir.Apply
                     ( Semantic_ir.Ident "Lg_runtime.Runtime_dynamic.vals",
                       [ target ] )))
              (pack_dynamic_value env dynamic target)
          else (
            match Types.dynamic_map_types target.ty with
            | Some (_key_type, value_type) ->
                Ok
                  (typed_ir (Types.next_seq value_type)
                     (Semantic_ir.Apply
                        ( Semantic_ir.Ident "List.to_seq",
                          [
                            Semantic_ir.Apply
                              ( Semantic_ir.Ident "List.map",
                                [
                                  Semantic_ir.Ident "snd";
                                  Semantic_ir.Apply
                                    ( Semantic_ir.Ident
                                        "Lg_runtime.Runtime_map.to_list",
                                      [ target.semantic_expr ] );
                                ] );
                          ] )))
            | None -> (
                match target.ty with
                | TRecord [] | TNamed_record { fields = []; _ } ->
                    Ok
                      (typed_ir (Types.next_seq TUnknown)
                         (Semantic_ir.Ident "Seq.empty"))
                | TRecord (first :: rest)
                | TNamed_record { fields = first :: rest; _ } ->
                    if
                      List.for_all
                        (fun (field : field) -> Types.equal first.ty field.ty)
                        rest
                    then
                      Ok
                        (typed_ir (Types.next_seq first.ty)
                           (Semantic_ir.Apply
                              ( Semantic_ir.Ident "List.to_seq",
                                [
                                  Semantic_ir.List
                                    (first :: rest
                                    |> List.map (fun (field : field) ->
                                           Structural_map.field_expr target
                                             field));
                                ] )))
                    else
                      Error.error ~code:Error_code.Semantic
                        "vals requires all map values to have the same type"
                | _ ->
                    Error.error ~code:Error_code.Arity
                      ("vals expects a map, got " ^ Types.source_name target.ty)))
      | Ok _ -> Error.error ~code:Error_code.Arity "vals expects 1 arguments"
  in
  {
    compile_list;
    compile_list_star;
    compile_list_of;
    compile_vector_of;
    compile_conj;
    compile_cons;
    compile_subvec;
    compile_nth;
    compile_get;
    compile_find;
    compile_assoc;
    compile_dissoc;
    compile_merge;
    compile_hash_map;
    compile_update;
    compile_select_keys;
    compile_contains;
    compile_keys;
    compile_vals;
  }
