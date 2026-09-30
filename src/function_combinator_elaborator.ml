open Ast
open Types
open Expression_support
module Env = Compiler_environment

type expression_result = (typed_expr, Error.t) result
type call = string -> Env.t -> Ast.form list -> expression_result

type t = {
  compile_apply : call;
  compile_static_fnil : call;
  compile_static_comp : call;
  compile_static_partial : call;
  compile_static_juxt : call;
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

let create ~compile_expr ~dynamic_unpack ~pack_dynamic_value
    ~pack_constrained_value ~plan_and_emit_argument =
  let compile_args_for = compile_args_for compile_expr in
  let overloaded_apply_counter = ref 0 in
  let rec require_callable_value expression =
    match expression.ty with
    | TNullable inner | TOcaml_app ("option", [ inner ]) ->
        require_callable_value
          {
            expression with
            ty = inner;
            semantic_expr =
              apply "Option.get" [ expression.semantic_expr ];
          }
    | _ -> expression
  in
  let collection_to_list_expr env collection =
    Collection_capability.to_seq_expr env collection
    |> Result.map (fun (element_type, sequence) ->
        (element_type, apply "List.of_seq" [ sequence ]))
  in
  let rec concrete_sequence_element = function
    | TVector element | TList element | TSet element | TSeq element
    | TArray element ->
        Some element
    | TString -> Some TChar
    | TNullable inner | TOcaml_app ("option", [ inner ]) ->
        concrete_sequence_element inner
    | ty -> Types.seqable_constraint_element ty
  in
  let sequence_concat_element = function
    | TOverloaded_fn ({ return_ty = TSeq element_ty; _ } :: _ as arities)
      when List.for_all
             (fun (arity : fn_arity) ->
               Types.equal arity.return_ty (TSeq element_ty)
               && List.for_all
                    (fun parameter_ty ->
                      match Types.seqable_constraint_element parameter_ty with
                      | Some actual -> Types.equal actual element_ty
                      | None -> false)
                    arity.fixed_params
               &&
               match arity.rest_param with
               | None -> true
               | Some rest_ty -> (
                   match Types.seqable_constraint_element rest_ty with
                   | Some actual -> Types.equal actual element_ty
                   | None -> false))
             arities ->
        Some element_ty
    | TOverloaded_fn _ | TFn _ | _ -> None
  in
  let refine_sequence_concat_function fn fixed_args rest_item_ty =
    match sequence_concat_element fn.ty with
    | None -> fn
    | Some element_ty ->
        let actual_elements =
          List.filter_map
            (fun argument -> concrete_sequence_element argument.ty)
            fixed_args
          @ Option.to_list (concrete_sequence_element rest_item_ty)
        in
        let substitutions =
          List.fold_left
            (fun result actual ->
              Result.bind result (fun substitutions ->
                  Type_solver.unify substitutions element_ty actual))
            (Ok Type_solver.empty) actual_elements
        in
        (match substitutions with
        | Ok substitutions ->
            { fn with ty = Type_solver.apply substitutions fn.ty }
        | Error _ -> fn)
  in
  let compile_function_arg scope env = function
    | FSymbol name -> (
        match lookup_binding scope env name with
        | Ok binding ->
            let binding = Types.instantiate_binding binding in
            Ok
              (typed_ir binding.ty (binding_value_expression binding)
              |> require_callable_value)
        | Error _ ->
            lookup_function scope env name |> Result.map require_callable_value)
    | FKeyword keyword ->
        let dynamic = Types.dynamic_constraint TUnknown in
        let target_name = "__lg_keyword_function_target" in
        Ok
          (typed_ir (TFn ([ dynamic ], dynamic))
             (Semantic_ir.Fun
                ( [ Semantic_ir.PVar target_name ],
                  apply "Lg_runtime.Runtime_dynamic.get"
                    [ Semantic_ir.Ident target_name;
                      apply "Lg_runtime.Runtime_dynamic.keyword"
                        [ Semantic_ir.String keyword ];
                    ] )))
    | form ->
        compile_expr scope env form |> Result.map require_callable_value
  in
  let rec overloaded_projection expression index =
    if index = 0 then apply "fst" [ expression ]
    else overloaded_projection (apply "snd" [ expression ]) (index - 1)
  in
  let capture_bindings bindings body =
    List.fold_right
      (fun binding body -> Semantic_ir.Let ([ binding ], body))
      bindings body
  in
  let overloaded_functions functions =
    List.fold_right
      (fun function_ rest -> Semantic_ir.Tuple [ function_; rest ])
      functions Semantic_ir.Unit
  in
  let rec irrefutable_pattern = function
    | Semantic_ir.PAny | Semantic_ir.PVar _ -> true
    | Semantic_ir.PLocated (_, _, pattern)
    | Semantic_ir.PAlias (pattern, _)
    | Semantic_ir.PConstraint (pattern, _)
    | Semantic_ir.PTyped (pattern, _) ->
        irrefutable_pattern pattern
    | _ -> false
  in
  let rec list_pattern_coverage consumed = function
    | Semantic_ir.PLocated (_, _, pattern)
    | Semantic_ir.PAlias (pattern, _)
    | Semantic_ir.PConstraint (pattern, _)
    | Semantic_ir.PTyped (pattern, _) ->
        list_pattern_coverage consumed pattern
    | Semantic_ir.PList items -> Some (`Exact (consumed + List.length items))
    | Semantic_ir.PCons (_, tail) -> list_pattern_coverage (consumed + 1) tail
    | Semantic_ir.PAny | Semantic_ir.PVar _ -> Some (`At_least consumed)
    | _ -> None
  in
  let list_patterns_are_exhaustive cases =
    let coverages =
      List.filter_map
        (fun (pattern, _) -> list_pattern_coverage 0 pattern)
        cases
    in
    List.exists
      (function
        | `At_least minimum ->
            List.init minimum Fun.id
            |> List.for_all (fun length ->
                   List.exists
                     (function
                       | `Exact actual -> actual = length
                       | `At_least _ -> false)
                     coverages)
        | `Exact _ -> false)
      coverages
  in
  let apply_arity_match list_expr cases =
    match cases with
    | [ (pattern, expression) ] when irrefutable_pattern pattern -> expression
    | _ ->
        let cases =
          if
            List.exists (fun (pattern, _) -> irrefutable_pattern pattern) cases
            || list_patterns_are_exhaustive cases
          then cases
          else
            cases
            @ [
                ( Semantic_ir.PAny,
                  apply "invalid_arg"
                    [ Semantic_ir.String "wrong apply argument count" ] );
              ]
        in
        Semantic_ir.Match (list_expr, cases)
  in
  let variadic_function_matches expected_params expected_return rest_param
      actual_return =
    let unified =
      List.fold_left
        (fun result expected_param ->
          Result.bind result (fun substitutions ->
              Type_solver.unify substitutions rest_param expected_param))
        (Ok Type_solver.empty) expected_params
    in
    Result.is_ok
      (Result.bind unified (fun substitutions ->
           Type_solver.unify substitutions actual_return expected_return))
  in
  let prepare_apply_argument env ~expected_ty argument =
    match (expected_ty, argument.ty) with
    | ( TFn (expected_params, expected_return),
        TOverloaded_fn
          [
            {
              fixed_params = [];
              rest_param = Some rest_param;
              return_ty = actual_return;
            };
          ] )
      when variadic_function_matches expected_params expected_return rest_param
             actual_return ->
        let function_name = "__lg_apply_variadic_adapter_function" in
        let parameter_names =
          List.mapi
            (fun index _ ->
              "__lg_apply_variadic_adapter_argument_" ^ string_of_int index)
            expected_params
        in
        Ok
          (Semantic_ir.Let
             ( [ (Semantic_ir.PVar function_name, argument.semantic_expr) ],
               Semantic_ir.Fun
                 ( List.map
                     (fun name -> Semantic_ir.PVar name)
                     parameter_names,
                   Semantic_ir.Apply
                     ( overloaded_projection
                         (Semantic_ir.Ident function_name) 0,
                       [
                         apply "Lg_runtime.Runtime_seq.of_list"
                           [
                             Semantic_ir.List
                               (List.map
                                  (fun name -> Semantic_ir.Ident name)
                                  parameter_names);
                           ];
                       ] ) ) ))
    | ( TOverloaded_fn
          [
            {
              fixed_params = expected_fixed;
              rest_param = Some expected_rest;
              return_ty = expected_return;
            };
          ],
        TOverloaded_fn
          [
            {
              fixed_params = [];
              rest_param = Some actual_rest;
              return_ty = actual_return;
            };
          ] )
      when variadic_function_matches
             (expected_fixed @ [ expected_rest ])
             expected_return actual_rest actual_return ->
        let function_name = "__lg_apply_variadic_adapter_function" in
        let fixed_names =
          List.mapi
            (fun index _ ->
              "__lg_apply_variadic_adapter_argument_" ^ string_of_int index)
            expected_fixed
        in
        let rest_name = "__lg_apply_variadic_adapter_rest" in
        let all_arguments =
          Semantic_ir.Infix
            ( "@",
              Semantic_ir.List
                (List.map (fun name -> Semantic_ir.Ident name) fixed_names),
              apply "Lg_runtime.Runtime_seq.to_list"
                [ Semantic_ir.Ident rest_name ] )
        in
        Ok
          (Semantic_ir.Let
             ( [ (Semantic_ir.PVar function_name, argument.semantic_expr) ],
               Semantic_ir.Tuple
                 [
                   Semantic_ir.Fun
                     ( List.map
                         (fun name -> Semantic_ir.PVar name)
                         fixed_names
                       @ [ Semantic_ir.PVar rest_name ],
                       Semantic_ir.Apply
                         ( overloaded_projection
                             (Semantic_ir.Ident function_name) 0,
                           [
                             apply "Lg_runtime.Runtime_seq.of_list"
                               [ all_arguments ];
                           ] ) );
                   Semantic_ir.Unit;
                 ] ))
    | _ ->
    if
      Option.is_some (Types.protocol_constraint_info expected_ty)
      || Option.is_some (Types.seqable_constraint_info expected_ty)
    then pack_constrained_value env expected_ty argument
    else if Types.is_dynamic expected_ty then
      if
        Types.is_dynamic argument.ty
        || match argument.ty with TUnknown | TMeta _ | TVar _ -> true | _ -> false
      then Ok argument.semantic_expr
      else
        pack_dynamic_value env expected_ty argument
    else if Types.is_dynamic argument.ty then
      dynamic_unpack env expected_ty argument.semantic_expr
    else if
      Types.assignable ~policy:Host_boundary ~expected:expected_ty
        ~actual:argument.ty
    then Ok argument.semantic_expr
    else
      Error.error ~code:Error_code.Type_mismatch
        ("apply argument type mismatch: expected "
        ^ Types.source_name expected_ty
        ^ ", got "
        ^ Types.source_name argument.ty)
  in
  let rec infer_apply_type substitutions template actual =
    match
      ( Types.seqable_constraint_element template,
        concrete_sequence_element actual )
    with
    | Some template_element, Some actual_element ->
        Type_solver.infer substitutions ~template:template_element
          ~actual:actual_element
        |> Result.value ~default:substitutions
    | _ -> (
        match (template, actual) with
        | TOverloaded_fn [ template_arity ],
          TOverloaded_fn [ actual_arity ] ->
            infer_variadic_callback substitutions template_arity actual_arity
        | TFn (template_params, template_return),
          TOverloaded_fn [ actual_arity ] -> (
            match actual_arity.rest_param with
            | Some actual_rest ->
                let substitutions =
                  List.fold_left
                    (fun substitutions template_parameter ->
                      infer_apply_type substitutions template_parameter
                        actual_rest)
                    substitutions template_params
                in
                infer_apply_type substitutions template_return
                  actual_arity.return_ty
            | None -> substitutions)
        | _ ->
            Type_solver.infer substitutions ~template ~actual
            |> Result.value ~default:substitutions)
  and infer_variadic_callback substitutions template_arity actual_arity =
    let substitutions =
      match actual_arity.rest_param with
      | Some actual_rest ->
          let template_parameters =
            template_arity.fixed_params
            @ Option.to_list template_arity.rest_param
          in
          List.fold_left
            (fun substitutions template_parameter ->
              infer_apply_type substitutions template_parameter actual_rest)
            substitutions template_parameters
      | None -> substitutions
    in
    infer_apply_type substitutions template_arity.return_ty
      actual_arity.return_ty
  in
  let instantiate_apply_return templates actuals return_ty =
    let substitutions =
      List.fold_left2 infer_apply_type Type_solver.empty templates actuals
    in
    Type_solver.apply substitutions return_ty
  in
  let compile_exact_apply env ~fn ~target ~fixed_args ~inner ~parameter_tys
      ~return_ty =
    let fixed_count = List.length fixed_args in
    if fixed_count > List.length parameter_tys then None
    else
      let fixed_parameter_tys =
        List.filteri (fun index _ -> index < fixed_count) parameter_tys
      in
      let remaining_parameter_tys = drop fixed_count parameter_tys in
      let return_ty =
        instantiate_apply_return parameter_tys
          (List.map (fun argument -> argument.ty) fixed_args
          @ List.init (List.length remaining_parameter_tys) (fun _ -> inner))
          return_ty
      in
      let argument_names =
        List.mapi
          (fun index _ -> "__lg_apply_argument_" ^ string_of_int index)
          remaining_parameter_tys
      in
      let rec prepare_fixed prepared expected arguments =
        match (expected, arguments) with
        | [], [] -> Ok (List.rev prepared)
        | expected_ty :: expected, argument :: arguments ->
            Result.bind
              (prepare_apply_argument env ~expected_ty argument)
              (fun expression ->
                prepare_fixed (expression :: prepared) expected arguments)
        | _ -> Error.error ~code:Error_code.Type_mismatch "internal apply argument mismatch"
      in
      let rec prepare_remaining prepared expected names =
        match (expected, names) with
        | [], [] -> Ok (List.rev prepared)
        | expected_ty :: expected, name :: names ->
            Result.bind
              (prepare_apply_argument env ~expected_ty
                 (typed_ir inner (Semantic_ir.Ident name)))
              (fun expression ->
                prepare_remaining (expression :: prepared) expected names)
        | _ -> Error.error ~code:Error_code.Type_mismatch "internal apply argument mismatch"
      in
      Some
        (Result.bind (prepare_fixed [] fixed_parameter_tys fixed_args)
           (fun fixed_arguments ->
             Result.map
               (fun remaining_arguments ->
                 ( Semantic_ir.PList
                     (List.map
                        (fun name -> Semantic_ir.PVar name)
                        argument_names),
                   typed_ir return_ty
                     (Semantic_ir.Apply
                        ( target fn.semantic_expr,
                          fixed_arguments @ remaining_arguments )) ))
               (prepare_remaining [] remaining_parameter_tys argument_names)))
  in
  let compile_variadic_apply env ~fn ~target ~fixed_args ~inner ~list_expr
      ~(arity : fn_arity) =
    match arity.rest_param with
    | None -> None
    | Some rest_ty ->
        let fixed_count = List.length arity.fixed_params in
        let given = List.length fixed_args in
        let inference_actuals =
          if given >= fixed_count then
            fixed_args
            |> List.filteri (fun index _ -> index < fixed_count)
            |> List.map (fun argument -> argument.ty)
          else
            List.map (fun argument -> argument.ty) fixed_args
            @ List.init (fixed_count - given) (fun _ -> inner)
        in
        let return_ty =
          instantiate_apply_return (arity.fixed_params @ [ rest_ty ])
            (inference_actuals @ [ inner ])
            arity.return_ty
        in
        let rec prepare_fixed prepared expected arguments =
          match (expected, arguments) with
          | [], [] -> Ok (List.rev prepared)
          | expected_ty :: expected, argument :: arguments ->
              Result.bind
                (prepare_apply_argument env ~expected_ty argument)
                (fun expression ->
                  prepare_fixed (expression :: prepared) expected arguments)
          | _ -> Error.error ~code:Error_code.Type_mismatch "internal apply argument mismatch"
        in
        let adapt_rest_list list_expr =
          if Types.equal inner rest_ty then Ok list_expr
          else
            let item_name = "__lg_apply_rest_item" in
            match
              prepare_apply_argument env ~expected_ty:rest_ty
                (typed_ir inner (Semantic_ir.Ident item_name))
            with
            | Error _ as error -> error
            | Ok adapted -> (
                match Semantic_ir.unlocated adapted with
                | Semantic_ir.Ident name when String.equal name item_name ->
                    Ok list_expr
                | _ ->
                    Ok
                      (apply "List.map"
                         [
                           Semantic_ir.Fun
                             ([ Semantic_ir.PVar item_name ], adapted);
                           list_expr;
                         ]))
        in
        let rest_seq rest_list =
          apply "Lg_runtime.Runtime_seq.of_list" [ rest_list ]
        in
        let compiled =
          if given >= fixed_count then
            let direct_args =
              List.filteri (fun index _ -> index < fixed_count) fixed_args
            in
            let extra_args = drop fixed_count fixed_args in
            Result.bind
              (prepare_fixed [] arity.fixed_params direct_args)
              (fun fixed_arguments ->
                Result.bind
                  (prepare_fixed []
                     (List.init (List.length extra_args) (fun _ -> rest_ty))
                     extra_args)
                  (fun extra_arguments ->
                    Result.map
                      (fun rest_list ->
                        ( Semantic_ir.PAny,
                          typed_ir return_ty
                            (Semantic_ir.Apply
                               ( target fn.semantic_expr,
                                 fixed_arguments
                                 @ [
                                     rest_seq
                                       (match extra_arguments with
                                       | [] -> rest_list
                                       | _ ->
                                           Semantic_ir.Infix
                                             ( "@",
                                               Semantic_ir.List extra_arguments,
                                               rest_list ));
                                   ] )) ))
                      (adapt_rest_list list_expr)))
          else
            let needed = fixed_count - given in
            let head_names =
              List.init needed (fun i -> "__lg_apply_head_" ^ string_of_int i)
            in
            let rest_name = "__lg_apply_rest" in
            let pattern =
              List.fold_right
                (fun name tail -> Semantic_ir.PCons (Semantic_ir.PVar name, tail))
                head_names (Semantic_ir.PVar rest_name)
            in
            Result.bind
              (prepare_fixed []
                 (List.filteri (fun index _ -> index < given)
                    arity.fixed_params)
                 fixed_args)
              (fun fixed_arguments ->
                Result.bind
                  (prepare_fixed []
                     (drop given arity.fixed_params)
                     (List.map
                        (fun name -> typed_ir inner (Semantic_ir.Ident name))
                        head_names))
                  (fun head_arguments ->
                    Result.map
                      (fun rest_list ->
                        ( pattern,
                          typed_ir return_ty
                            (Semantic_ir.Apply
                               ( target fn.semantic_expr,
                                 fixed_arguments @ head_arguments
                                 @ [ rest_seq rest_list ] )) ))
                      (adapt_rest_list (Semantic_ir.Ident rest_name))))
        in
        Some compiled
  in
  let pack_apply_record_entry_value ty expression =
    let convert name =
      Ok
        (Semantic_ir.Apply
           ( Semantic_ir.Ident ("Lg_runtime.Runtime_metadata." ^ name),
             [ expression ] ))
    in
    match Types.constraint_value_type ty with
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
    | ty ->
        Error.error ~code:Error_code.Semantic
          ("apply conj over a static map cannot pack "
         ^ Types.source_name ty ^ " as an EDN map entry value")
  in
  let compile_apply_conj_static_record target fields record_expr =
    let edn_ty = TOcaml "Lg_edn_backend.t" in
    let entry_ty = TVector edn_ty in
    let set_ty = TSet entry_ty in
    let target_expr =
      match target.ty with
      | TSet (TUnknown | TMeta _ | TVar _)
      | TSet (TVector (TUnknown | TMeta _ | TVar _)) ->
          target.semantic_expr
      | TSet actual when Types.equal actual entry_ty -> target.semantic_expr
      | _ -> Semantic_ir.Ident "Lg_runtime.Runtime_poly_set.empty"
    in
    let record = typed_ir (TRecord fields) record_expr in
    let rec build_entries acc = function
      | [] -> Ok (List.rev acc)
      | (field : field) :: rest ->
          let key =
            Semantic_ir.Apply
              ( Semantic_ir.Ident "Lg_runtime.Runtime_metadata.of_keyword",
                [ Semantic_ir.String field.keyword ] )
          in
          let value = Structural_map.field_expr record field in
          Result.bind
            (pack_apply_record_entry_value field.ty value)
            (fun value ->
              let entry =
                Semantic_ir.Apply
                  ( Semantic_ir.Ident "Rrbvec.of_list",
                    [ Semantic_ir.List [ key; value ] ] )
              in
              build_entries (entry :: acc) rest)
    in
    Result.map
      (fun entries ->
        typed_ir set_ty
          (List.fold_left
             (fun set entry ->
               Semantic_ir.Apply
                 ( Semantic_ir.Ident "Lg_runtime.Runtime_poly_set.add",
                   [ entry; set ] ))
             target_expr entries))
      (build_entries [] fields)
  in
  let compile_apply scope env arg_forms =
      let rec split_last acc = function
        | [] -> None
        | [ last ] -> Some (List.rev acc, last)
        | item :: rest -> split_last (item :: acc) rest
      in
      match arg_forms with
      | fn_form :: rest -> (
          match split_last [] rest with
          | None -> Error.error ~code:Error_code.Arity "apply expects function and collection"
          | Some
              ( fixed_forms,
                FList
                  [ FSymbol
                      ( "conj" | "clojure.core/conj" | "cljs.core/conj"
                      | "__lg_conj" );
                    FVector spread_forms;
                    appended;
                  ] ) ->
              compile_expr scope env
                (FList (fn_form :: (fixed_forms @ spread_forms @ [ appended ])))
          | Some (fixed_forms, FVector spread_forms) ->
              let spread_forms =
                match (Env.target env, fn_form, fixed_forms) with
                | Target.Melange, FSymbol ("assoc" | "clojure.core/assoc" | "cljs.core/assoc"), _ :: _
                  when List.length spread_forms mod 2 = 1 ->
                    spread_forms @ [ FSymbol "nil" ]
                | _ -> spread_forms
              in
              (match (fixed_forms, spread_forms, fn_form) with
              | [], [ key ], (FMap _ | FList (FSymbol "__lg_hash-map" :: _))
              | [], [ key ], FVector _ ->
                  compile_expr scope env
                    (FList [ FSymbol "__lg_get"; fn_form; key ])
              | [], [ candidate ], FKeyword _ -> (
                  match compile_expr scope env candidate with
                  | Ok { ty = TSet _; _ } ->
                      compile_expr scope env
                        (FList
                           [
                             FSymbol "if";
                             FList
                               [ FSymbol "contains?"; candidate; fn_form ];
                             fn_form;
                             FSymbol "nil";
                           ])
                  | Ok _ | Error _ ->
                      compile_expr scope env
                        (FList (fn_form :: (fixed_forms @ spread_forms))))
              | _ ->
                  compile_expr scope env
                    (FList (fn_form :: (fixed_forms @ spread_forms))))
          | Some (fixed_forms, collection_form) -> (
              match
                ( compile_args_for scope env fixed_forms,
                  compile_expr scope env collection_form )
              with
              | (Error _ as err), _ -> err
              | _, (Error _ as err) -> err
              | Ok fixed_args, Ok collection -> (
                  if
                    Edn_value_elaborator.is_literal_empty_collection
                      collection.ty collection.semantic_expr
                  then
                    Result.map
                      (fun direct_call ->
                        {
                          direct_call with
                          semantic_expr =
                            Semantic_ir.Sequence
                              [ collection.semantic_expr; direct_call.semantic_expr ];
                        })
                      (compile_expr scope env (FList (fn_form :: fixed_forms)))
                  else
                    match (fn_form, fixed_args, collection.ty) with
                  | ( FSymbol
                        ("conj" | "clojure.core/conj" | "cljs.core/conj"),
                      [ target ],
                      TRecord fields ) ->
                      compile_apply_conj_static_record target fields
                        collection.semantic_expr
                  | _ -> (
                  match collection_to_list_expr env collection with
                  | Error _ ->
                      Error.error ~code:Error_code.Arity
                        ("apply expects a seqable value, got "
                        ^ Types.source_name collection.ty)
                  | Ok (inner, list_expr) -> (
                      let empty_string_rest =
                        Types.equal collection.ty TString
                        &&
                        match
                          Semantic_ir.unlocated collection.semantic_expr
                        with
                        | Semantic_ir.String "" -> true
                        | _ -> false
                      in
                      let inner, list_expr =
                        match (empty_string_rest, fn_form, fixed_args) with
                        | true, FSymbol "+", _ -> (TInt, Semantic_ir.List [])
                        | true, _, first :: _ ->
                            (first.ty, Semantic_ir.List [])
                        | _ -> (inner, list_expr)
                      in
                      match fn_form with
                      | FSymbol "str" ->
                          let value_name = "__lg_apply_str_value" in
                          let stringify_value =
                            Semantic_ir.Fun
                              ( [ Semantic_ir.PVar value_name ],
                                Codegen.stringify_expr_ir ~pr:false
                                (typed_ir inner (Semantic_ir.Ident value_name))
                            )
                          in
                          let collection_text =
                            apply "String.concat"
                            [
                              Semantic_ir.String "";
                                apply "List.map" [ stringify_value; list_expr ];
                              ]
                          in
                          let parts =
                          List.map
                            (Codegen.stringify_expr_ir ~pr:false)
                            fixed_args
                            @ [ collection_text ]
                          in
                          Ok (typed_ir TString (Codegen.concat_expr parts))
                    | FSymbol "+"
                      when Types.equal inner TInt
                           && List.for_all
                                (fun argument -> Types.equal argument.ty TInt)
                                fixed_args ->
                        let values =
                          match fixed_args with
                          | [] -> list_expr
                          | _ ->
                              Semantic_ir.Infix
                                ( "@",
                                  Semantic_ir.List
                                    (List.map
                                       (fun argument -> argument.semantic_expr)
                                       fixed_args),
                                  list_expr )
                        in
                        Ok
                          (typed_ir TInt
                             (apply "List.fold_left"
                                [
                                  Semantic_ir.Fun
                                    ( [ Semantic_ir.PVar "left";
                                        Semantic_ir.PVar "right";
                                      ],
                                      Semantic_ir.Infix
                                        ( "+",
                                          Semantic_ir.Ident "left",
                                          Semantic_ir.Ident "right" ) );
                                  Semantic_ir.Int 0;
                                  values;
                                ]))
                    | FSymbol ("conj" | "clojure.core/conj" | "cljs.core/conj")
                      -> (
                        match fixed_args with
                        | [ target ] -> (
                            let target_element_ty =
                              match target.ty with
                              | TVector element_ty -> Some element_ty
                              | _ -> None
                            in
                            match target_element_ty with
                            | Some element_ty ->
                                let resolved_element_ty =
                                  match element_ty with
                                  | TUnknown | TMeta _ | TVar _ -> inner
                                  | _ -> element_ty
                                in
                                let item_name = "__lg_apply_conj_item" in
                                let item =
                                  typed_ir inner
                                    (Semantic_ir.Ident item_name)
                                in
                                Result.map
                                  (fun item_expr ->
                                    typed_ir (TVector resolved_element_ty)
                                      (apply "List.fold_left"
                                         [
                                           Semantic_ir.Fun
                                             ( [
                                                 Semantic_ir.PVar
                                                   "__lg_apply_conj_vector";
                                                 Semantic_ir.PVar item_name;
                                               ],
                                               apply "Rrbvec.push_back"
                                                 [
                                                   Semantic_ir.Ident
                                                     "__lg_apply_conj_vector";
                                                   item_expr;
                                                 ] );
                                           target.semantic_expr;
                                           list_expr;
                                         ]))
                                  (plan_and_emit_argument env
                                     ~expected:resolved_element_ty item)
                            | None ->
                                Error.error ~code:Error_code.Arity
                                  "apply conj expects a vector target")
                        | _ ->
                            Error.error ~code:Error_code.Semantic
                              "apply conj expects one fixed collection \
                               argument")
                    | FSymbol "__lg_pr" -> (
                        match lookup_binding scope env "*out*" with
                        | writer ->
                            let value_name = "__lg_apply_pr_value" in
                            let render_value =
                              Semantic_ir.Fun
                                ( [ Semantic_ir.PVar value_name ],
                                  Codegen.stringify_expr_ir ~pr:true
                                    (typed_ir inner
                                       (Semantic_ir.Ident value_name)) )
                            in
                            let collection_texts =
                              apply "List.map" [ render_value; list_expr ]
                            in
                            let fixed_texts =
                              Semantic_ir.List
                                (List.map
                                   (Codegen.stringify_expr_ir ~pr:true)
                                   fixed_args)
                            in
                            let texts =
                              match fixed_args with
                              | [] -> collection_texts
                              | _ ->
                                  Semantic_ir.Infix
                                    ("@", fixed_texts, collection_texts)
                            in
                            let text =
                              apply "String.concat"
                                [ Semantic_ir.String " "; texts ]
                            in
                            let output =
                              match writer with
                              | Ok writer ->
                                  apply "Lg_runtime.Runtime_print.write"
                                    [ Semantic_ir.Ident writer.ocaml_name; text ]
                              | Error _ -> apply "print_string" [ text ]
                            in
                            Ok (typed_ir TUnit output))
                      | _ -> (
                        match compile_function_arg scope env fn_form with
                        | Error _ as err -> err
                        | Ok fn -> (
                          let fn =
                            refine_sequence_concat_function fn fixed_args inner
                          in
                          match fn.ty with
                          | ty
                            when Option.is_some
                                   (Types.constant_function_result ty) ->
                              let return_ty =
                                Types.constant_function_result ty |> Option.get
                              in
                              let result_name =
                                "__lg_apply_constant_function_result"
                              in
                              Ok
                                (typed_ir return_ty
                                   (Semantic_ir.Let
                                      ( [
                                          ( Semantic_ir.PVar result_name,
                                            fn.semantic_expr );
                                        ],
                                        Semantic_ir.Sequence
                                          (List.map
                                             (fun argument ->
                                               Semantic_ir.evaluate_for_effect
                                                 argument.semantic_expr)
                                             fixed_args
                                          @ [
                                              Semantic_ir.evaluate_for_effect
                                                list_expr;
                                              Semantic_ir.Ident result_name;
                                            ]) )))
                          | TFn ([ TInt; TInt ], TInt)
                            when Types.equal inner TInt
                                   && List.for_all
                                        (fun arg -> Types.equal arg.ty TInt)
                                        fixed_args ->
                          let values_expr =
                            match fixed_args with
                            | [] -> list_expr
                            | _ ->
                                Semantic_ir.Infix
                                  ( "@",
                                    Semantic_ir.List
                                            (List.map
                                               (fun arg -> arg.semantic_expr)
                                               fixed_args),
                                    list_expr )
                          in
                          Ok
                            (typed_ir TInt
                               (apply "List.fold_left"
                                        [
                                          fn.semantic_expr;
                                          Semantic_ir.Int 0;
                                          values_expr;
                                        ]))
                          | TFn ([ TInt; TInt ], TInt) ->
                                Error.error ~code:Error_code.Semantic
                                  "apply currently supports int binary reducers"
                          | TFn (parameter_tys, return_ty) -> (
                              match
                                compile_exact_apply env ~fn
                                  ~target:(fun expression -> expression)
                                    ~fixed_args ~inner ~parameter_tys ~return_ty
                              with
                                | None ->
                                    Error.error ~code:Error_code.Arity
                                      "apply has too many fixed arguments"
                              | Some result ->
                                  Result.map
                                    (fun (pattern, result) ->
                                      typed_ir return_ty
                                        (Semantic_ir.Match
                                           ( list_expr,
                                               [
                                                 (pattern, result.semantic_expr);
                                               ( Semantic_ir.PAny,
                                                 apply "invalid_arg"
                                                     [
                                                       Semantic_ir.String
                                                         "wrong apply argument \
                                                          count";
                                                     ] );
                                             ] )))
                                    result)
                          | TOverloaded_fn arities ->
                              incr overloaded_apply_counter;
                              let function_name =
                                "__lg_apply_overloaded_function_"
                                ^ string_of_int !overloaded_apply_counter
                              in
                              let stable_fn =
                                {
                                  fn with
                                  semantic_expr =
                                    Semantic_ir.Ident function_name;
                                }
                              in
                              let compiled =
                                arities
                                |> List.mapi (fun index arity ->
                                       match arity.rest_param with
                                       | Some _ ->
                                           compile_variadic_apply env
                                             ~fn:stable_fn
                                             ~target:(fun expression ->
                                               overloaded_projection expression
                                                 index)
                                             ~fixed_args ~inner ~list_expr
                                             ~arity
                                       | None ->
                                           compile_exact_apply env ~fn:stable_fn
                                             ~target:(fun expression ->
                                              overloaded_projection expression
                                                index)
                                             ~fixed_args ~inner
                                             ~parameter_tys:arity.fixed_params
                                             ~return_ty:arity.return_ty)
                                |> List.filter_map Fun.id
                              in
                              let rec collect cases return_ty = function
                                | [] -> Ok (List.rev cases, return_ty)
                                | result :: rest -> (
                                    match result with
                                    | Error _ as error -> error
                                    | Ok (pattern, expression) -> (
                                        match return_ty with
                                          | None ->
                                              collect
                                                [ (pattern, expression) ]
                                                (Some expression.ty) rest
                                          | Some ty
                                            when Types.equal ty expression.ty ->
                                              collect
                                                ((pattern, expression) :: cases)
                                                return_ty rest
                                        | Some ty -> (
                                            match
                                              Type_solver.unify
                                                Type_solver.empty ty
                                                expression.ty
                                            with
                                            | Ok substitutions ->
                                                collect
                                                  ((pattern, expression)
                                                  :: cases)
                                                  (Some
                                                     (Type_solver.apply
                                                        substitutions ty))
                                                  rest
                                            | Error _ ->
                                                Error.error ~code:Error_code.Semantic
                                                  ("apply overloads must return the same type, got "
                                                  ^ Types.source_name ty
                                                  ^ " and "
                                                  ^ Types.source_name
                                                      expression.ty))))
                              in
                              Result.bind (collect [] None compiled)
                                (fun (cases, return_ty) ->
                                  match (cases, return_ty) with
                                    | [], _ ->
                                        Error.error ~code:Error_code.Arity
                                          "apply has no matching function arity"
                                    | _, None ->
                                        Error.error ~code:Error_code.Arity
                                          "apply has no matching function arity"
                                  | cases, Some return_ty ->
                                      Ok
                                        (typed_ir return_ty
                                           (Semantic_ir.Let
                                              ( [
                                                  ( Semantic_ir.PVar
                                                      function_name,
                                                    fn.semantic_expr );
                                                ],
                                                apply_arity_match list_expr
                                                  (List.map
                                                     (fun (pattern, expression) ->
                                                       ( pattern,
                                                         expression.semantic_expr
                                                       ))
                                                     cases) ))))
                          | fn_type
                            when Types.is_dynamic fn_type
                                 || (match fn_type with
                                    | TUnknown | TMeta _ | TVar _ -> true
                                    | _ -> false) ->
                              Error.error ~code:Error_code.Semantic
                                "apply requires a statically typed function; \
                                 define a closed sum type for multiple function \
                                 shapes"
                          | _ -> Error.error ~code:Error_code.Arity "apply expects a function")))))))
      | _ -> Error.error ~code:Error_code.Arity "apply expects function and collection"
    and compile_static_comp scope env arg_forms =
      match arg_forms with
      | [] ->
          let value_ty = Type_solver.fresh () in
          Ok
            (typed_ir (TFn ([ value_ty ], value_ty))
               (Semantic_ir.Fun
                  ([ Semantic_ir.PVar "value" ], Semantic_ir.Ident "value")))
      | _ -> (
          let compiled =
            arg_forms
            |> List.fold_left
                 (fun acc form ->
                   match acc with
                   | Error _ as err -> err
                   | Ok fns -> (
                       match compile_function_arg scope env form with
                       | Error _ as err -> err
                       | Ok fn -> Ok (fn :: fns)))
                 (Ok [])
            |> Result.map List.rev
          in
          match compiled with
          | Error _ as err -> err
          | Ok fns -> (
              let select_unary fn =
                match fn.ty with
                | TFn ([ _ ], _) -> Ok fn
                | TFn _ -> Error.error ~code:Error_code.Arity "comp expects unary functions"
                | TOverloaded_fn arities -> (
                    match
                      arities
                      |> List.mapi (fun index arity -> (index, arity))
                      |> List.find_map (fun (index, arity) ->
                             match (arity.fixed_params, arity.rest_param) with
                             | [ parameter ], None ->
                                 Some
                                   (typed_ir
                                      (TFn ([ parameter ], arity.return_ty))
                                      (overloaded_projection fn.semantic_expr
                                         index))
                             | _ -> None)
                    with
                    | Some fn -> Ok fn
                    | None -> Error.error ~code:Error_code.Arity "comp expects unary functions")
                | _ -> Error.error ~code:Error_code.Arity "comp expects functions"
              in
              let rec select_unary_functions selected = function
                | [] -> Ok (List.rev selected)
                | fn :: rest ->
                    Result.bind (select_unary fn) (fun unary_fn ->
                        select_unary_functions (unary_fn :: selected) rest)
              in
              Result.bind (select_unary_functions [] fns) (fun fns ->
              let nil_predicate_form = function
                | FSymbol ("nil?" | "clojure.core/nil?" | "cljs.core/nil?") ->
                    true
                | _ -> false
              in
              let seq_form = function
                | FSymbol ("seq" | "clojure.core/seq" | "cljs.core/seq") ->
                    true
                | _ -> false
              in
              let seq_empty_predicate () =
                let element_ty = Type_solver.fresh () in
                let value_name = "__lg_comp_seq_value" in
                typed_ir
                  (TFn ([ TSeq element_ty ], TBool))
                  (Semantic_ir.Fun
                     ( [ Semantic_ir.PVar value_name ],
                       Semantic_ir.Apply
                         ( Semantic_ir.Ident
                             "Lg_runtime.Runtime_seq.is_empty",
                           [ Semantic_ir.Ident value_name ] ) ))
              in
              let rec adapt_nil_after_seq forms fns =
                match (forms, fns) with
                | left_form :: right_form :: rest_forms, _left_fn :: rest_fns
                  when nil_predicate_form left_form && seq_form right_form ->
                    seq_empty_predicate ()
                    :: adapt_nil_after_seq (right_form :: rest_forms) rest_fns
                | _form :: rest_forms, fn :: rest_fns ->
                    fn :: adapt_nil_after_seq rest_forms rest_fns
                | [], [] -> []
                | _ -> fns
              in
              let fns = adapt_nil_after_seq arg_forms fns in
              let concrete_seqable_element = function
                | TArray element | TList element | TVector element
                | TSet element | TSeq element ->
                    Some element
                | ty -> Types.next_seq_element ty
              in
              let rec unify_assignable substitutions ~expected ~actual =
                let expected = Type_solver.apply substitutions expected in
                let actual = Type_solver.apply substitutions actual in
                match Type_solver.unify substitutions expected actual with
                | Ok substitutions -> Ok substitutions
                | Error _ -> (
                    match (expected, actual) with
                    | expected, actual -> (
                        match
                          ( concrete_seqable_element expected,
                            concrete_seqable_element actual )
                        with
                        | Some expected_element, Some actual_element ->
                            (match
                               Type_solver.unify substitutions expected_element
                                 actual_element
                             with
                            | Ok substitutions -> Ok substitutions
                            | Error _ ->
                                Error.error ~code:Error_code.Type_mismatch "incompatible sequence elements")
                        | _ -> (
                        match
                          ( Types.seqable_constraint_info expected,
                            concrete_seqable_element actual )
                        with
                        | Some (_, expected_element, _), Some actual_element ->
                            (match
                               Type_solver.unify substitutions expected_element
                                 actual_element
                             with
                            | Ok substitutions -> Ok substitutions
                            | Error _ ->
                                Error.error ~code:Error_code.Type_mismatch "incompatible sequence elements")
                        | _ -> (
                            match (expected, actual) with
                            | TFn (expected_params, expected_return),
                              TFn (actual_params, actual_return)
                              when List.length expected_params
                                   = List.length actual_params ->
                                Result.bind
                                  (unify_function_parameters substitutions
                                     expected_params actual_params)
                                  (fun substitutions ->
                                    unify_assignable substitutions
                                      ~expected:expected_return
                                      ~actual:actual_return)
                            | TOverloaded_fn expected_arities,
                              TOverloaded_fn actual_arities
                              when List.length expected_arities
                                   = List.length actual_arities ->
                                List.fold_left2
                                  (fun result expected_arity actual_arity ->
                                    Result.bind result (fun substitutions ->
                                        unify_assignable_arity substitutions
                                          expected_arity actual_arity))
                                  (Ok substitutions) expected_arities
                                  actual_arities
                            | _ -> Error.error ~code:Error_code.Type_mismatch "incompatible function types"))))
              and unify_function_parameters substitutions expected actual =
                List.fold_left2
                  (fun result expected_parameter actual_parameter ->
                    Result.bind result (fun substitutions ->
                        unify_assignable substitutions
                          ~expected:actual_parameter
                          ~actual:expected_parameter))
                  (Ok substitutions) expected actual
              and unify_assignable_arity substitutions expected actual =
                if
                  List.length expected.fixed_params
                  <> List.length actual.fixed_params
                then Error.error ~code:Error_code.Type_mismatch "incompatible function arities"
                else
                  Result.bind
                    (unify_function_parameters substitutions
                       expected.fixed_params actual.fixed_params)
                    (fun substitutions ->
                      let rest =
                        match (expected.rest_param, actual.rest_param) with
                        | None, None -> Ok substitutions
                        | Some expected, Some actual ->
                            unify_assignable substitutions ~expected:actual
                              ~actual:expected
                        | _ -> Error.error ~code:Error_code.Type_mismatch "incompatible function arities"
                      in
                      Result.bind rest (fun substitutions ->
                          unify_assignable substitutions
                            ~expected:expected.return_ty
                            ~actual:actual.return_ty))
              in
              let unary_type fn =
                match fn.ty with
                | TFn ([ arg ], ret) -> Ok (arg, ret)
                | TFn _ -> Error.error ~code:Error_code.Arity "comp expects unary functions"
                | _ -> Error.error ~code:Error_code.Arity "comp expects functions"
              in
              let rec unify_chain substitutions = function
                | [] | [ _ ] -> Ok substitutions
                | left :: (right :: _ as rest) ->
                    Result.bind (unary_type left) (fun (left_arg, _) ->
                        Result.bind (unary_type right) (fun (_, right_ret) ->
                            match
                              unify_assignable substitutions
                                ~expected:left_arg ~actual:right_ret
                            with
                            | Ok substitutions ->
                                unify_chain substitutions rest
                            | Error _ ->
                                Error.error ~code:Error_code.Semantic
                                  ("comp function types do not line up: "
                                 ^ Types.source_name left_arg ^ " and "
                                 ^ Types.source_name right_ret)))
              in
              match unify_chain Type_solver.empty fns with
              | Error _ as err -> err
              | Ok substitutions -> (
                  match (unary_type (List.hd fns), unary_type (List.hd (List.rev fns))) with
                  | Error _ as err, _ | _, (Error _ as err) -> err
                  | Ok (_, ret_ty), Ok (arg_ty, _) ->
                      let arg_ty = Type_solver.apply substitutions arg_ty in
                      let ret_ty = Type_solver.apply substitutions ret_ty in
                      let argument_pattern =
                        match Types.seqable_constraint_info arg_ty with
                        | Some (`Required, _, _) ->
                            Semantic_ir.PTuple
                              [
                                Semantic_ir.PVar "x__seq";
                                Semantic_ir.PVar "x";
                              ]
                        | Some ((`Optional | `Optional_sequential), _, _) ->
                            Semantic_ir.PTuple
                              [
                                Semantic_ir.PVar "x__seq_optional";
                                Semantic_ir.PVar "x";
                              ]
                        | None -> Semantic_ir.PVar "x"
                      in
                      let rec compose expression = function
                        | [] -> Ok expression
                        | fn :: rest ->
                            Result.bind (unary_type fn) (fun (parameter, return_ty) ->
                                let parameter =
                                  Type_solver.apply substitutions parameter
                                in
                                let return_ty =
                                  Type_solver.apply substitutions return_ty
                                in
                                Result.bind
                                  (plan_and_emit_argument env
                                     ~expected:parameter expression)
                                  (fun argument ->
                                    compose
                                      (typed_ir return_ty
                                         (Semantic_ir.Apply
                                            (fn.semantic_expr, [ argument ])))
                                      rest))
                      in
                      Result.map
                        (fun inner ->
                          typed_ir (TFn ([ arg_ty ], ret_ty))
                            (Semantic_ir.Fun
                               ( [ argument_pattern ],
                                 inner.semantic_expr )))
                        (compose
                           (typed_ir arg_ty (Semantic_ir.Ident "x"))
                           (List.rev fns))))))

    and compile_static_fnil scope env arg_forms =
      match arg_forms with
      | [ FSymbol "__lg_conj"; default_form ] ->
          Result.bind (compile_expr scope env default_form) (fun default ->
              let default_name = "__lg_fnil_default_collection" in
              let collection_name = "collection" in
              let value_name = "value" in
              let selected_collection =
                Semantic_ir.Match
                  ( Semantic_ir.Ident collection_name,
                    [
                      ( Semantic_ir.PConstructor ("None", None),
                        Semantic_ir.Ident default_name );
                      ( Semantic_ir.PConstructor
                          ( "Some",
                            Some (Semantic_ir.PVar "present_collection") ),
                        Semantic_ir.Ident "present_collection" );
                    ] )
              in
              let wrap result_type value_type add_expression =
                typed_ir
                  (TFn ([ TNullable result_type; value_type ], result_type))
                  (capture_bindings
                     [ (Semantic_ir.PVar default_name, default.semantic_expr) ]
                     (Semantic_ir.Fun
                        ( [
                            Semantic_ir.PVar collection_name;
                            Semantic_ir.PVar value_name;
                          ],
                          add_expression selected_collection
                            (Semantic_ir.Ident value_name) )))
              in
              match default.ty with
              | TVector element_type ->
                  let element_type =
                    match element_type with
                    | TUnknown -> TVar "fnil_vector_element"
                    | element_type -> element_type
                  in
                  let result_type = TVector element_type in
                  Ok
                    (wrap result_type element_type (fun collection value ->
                         Semantic_ir.Apply
                           ( Semantic_ir.Ident "Rrbvec.push_back",
                             [ collection; value ] )))
              | TSet element_type ->
                  Result.map
                    (fun set_module ->
                      let result_type = TSet element_type in
                      wrap result_type TUnknown (fun collection value ->
                          Semantic_ir.Apply
                            ( Semantic_ir.Ident (set_module ^ ".add"),
                              [ value; collection ] )))
                    (Types.set_module_name element_type)
              | _ ->
                  Error.error ~code:Error_code.Semantic "fnil conj default must be a vector or set")
      | [ FSymbol "__lg_conj"; _; _ ]
      | [ FSymbol "__lg_conj"; _; _; _ ] ->
          Error.error ~code:Error_code.Arity "fnil conj currently supports one default argument"
      | function_form :: default_forms
        when List.length default_forms >= 1
             && List.length default_forms <= 3 -> (
          match
            ( compile_function_arg scope env function_form,
              compile_args_for scope env default_forms )
          with
          | (Error _ as error), _ | _, (Error _ as error) -> error
          | Ok fn, Ok defaults -> (
              match fn.ty with
              | TFn (parameter_tys, return_ty) ->
                  let default_count = List.length defaults in
                  let minimum_arity = if default_count = 3 then 2 else default_count in
                  if List.length parameter_tys < minimum_arity then
                    Error.error ~code:Error_code.Semantic
                      "fnil function has fewer parameters than required defaults"
                  else
                    let rec adapt_defaults adapted index = function
                      | [] -> Ok (List.rev adapted)
                      | default :: rest ->
                          let adapted_default =
                            match List.nth_opt parameter_tys index with
                            | Some expected ->
                                plan_and_emit_argument env ~expected default
                                |> Result.map (typed_ir expected)
                            | None -> Ok default
                          in
                          Result.bind adapted_default (fun default ->
                              adapt_defaults (default :: adapted) (index + 1)
                                rest)
                    in
                    Result.map
                      (fun defaults ->
                        let function_name = "__lg_fnil_function" in
                        let default_names =
                          List.mapi
                            (fun index _ ->
                              "__lg_fnil_default_" ^ string_of_int index)
                            defaults
                        in
                        let argument_names =
                          List.mapi
                            (fun index _ ->
                              "__lg_fnil_argument_" ^ string_of_int index)
                            parameter_tys
                        in
                        let selected_arguments =
                          List.mapi
                            (fun index name ->
                              if
                                index < default_count
                                && index < List.length parameter_tys
                              then
                                let present_name = name ^ "_value" in
                                Semantic_ir.Match
                                  ( Semantic_ir.Ident name,
                                    [
                                      ( Semantic_ir.PConstructor
                                          ("None", None),
                                        Semantic_ir.Ident
                                          (List.nth default_names index) );
                                      ( Semantic_ir.PConstructor
                                          ( "Some",
                                            Some
                                              (Semantic_ir.PVar present_name) ),
                                        Semantic_ir.Ident present_name );
                                    ] )
                              else Semantic_ir.Ident name)
                            argument_names
                        in
                        let returned_parameter_tys =
                          List.mapi
                            (fun index parameter_ty ->
                              if index < default_count then
                                TNullable parameter_ty
                              else parameter_ty)
                            parameter_tys
                        in
                        let bindings =
                          ( Semantic_ir.PVar function_name,
                            fn.semantic_expr )
                          :: List.map2
                               (fun name default ->
                                 (Semantic_ir.PVar name, default.semantic_expr))
                               default_names defaults
                        in
                        typed_ir
                          (TFn (returned_parameter_tys, return_ty))
                          (capture_bindings bindings
                             (Semantic_ir.Fun
                                ( List.map
                                    (fun name -> Semantic_ir.PVar name)
                                    argument_names,
                                  Semantic_ir.Apply
                                    ( Semantic_ir.Ident function_name,
                                      selected_arguments ) ))))
                      (adapt_defaults [] 0 defaults)
              | TOverloaded_fn arities ->
                  let default_count = List.length defaults in
                  let minimum_arity = if default_count = 3 then 2 else default_count in
                  let selected_arities =
                    arities
                    |> List.mapi (fun index arity -> (index, arity))
                    |> List.filter (fun (_, arity) ->
                           match arity.rest_param with
                           | None ->
                               List.length arity.fixed_params >= minimum_arity
                           | Some _ -> true)
                  in
                  (match selected_arities with
                  | [] ->
                      Error.error ~code:Error_code.Arity
                        "fnil has no function arity accepting the default positions"
                  | _ ->
                      let expected_default_type index =
                        selected_arities
                        |> List.filter_map (fun (_, arity) ->
                               match List.nth_opt arity.fixed_params index with
                               | Some ty -> Some ty
                               | None -> arity.rest_param)
                        |> function
                        | [] -> Ok None
                        | expected :: rest
                          when List.for_all (Types.equal expected) rest ->
                            Ok (Some expected)
                        | _ ->
                            Error.error ~code:Error_code.Arity
                              "fnil overloaded function arities disagree on default argument types"
                      in
                      let rec adapt_defaults adapted index = function
                        | [] -> Ok (List.rev adapted)
                        | default :: rest ->
                            Result.bind (expected_default_type index)
                              (fun expected ->
                                let adapted_default =
                                  match expected with
                                  | None -> Ok default
                                  | Some expected ->
                                      plan_and_emit_argument env ~expected default
                                      |> Result.map (typed_ir expected)
                                in
                                Result.bind adapted_default (fun default ->
                                    adapt_defaults (default :: adapted)
                                      (index + 1) rest))
                      in
                      Result.map
                        (fun defaults ->
                          let function_name = "__lg_fnil_function" in
                          let default_names =
                            List.mapi
                              (fun index _ ->
                                "__lg_fnil_default_" ^ string_of_int index)
                              defaults
                          in
                          let returned_arities, returned_functions =
                            selected_arities
                            |> List.mapi (fun returned_index
                                              (source_index, arity) ->
                                   match arity.rest_param with
                                   | None ->
                                       let argument_names =
                                         List.mapi
                                           (fun index _ ->
                                             "__lg_fnil_argument_"
                                             ^ string_of_int returned_index ^ "_"
                                             ^ string_of_int index)
                                           arity.fixed_params
                                       in
                                       let returned_parameter_tys =
                                         List.mapi
                                           (fun index parameter_ty ->
                                             if index < default_count then
                                               TNullable parameter_ty
                                             else parameter_ty)
                                           arity.fixed_params
                                       in
                                       let selected_arguments =
                                         List.mapi
                                           (fun index name ->
                                             if index < default_count then
                                               let present_name =
                                                 name ^ "_value"
                                               in
                                               Semantic_ir.Match
                                                 ( Semantic_ir.Ident name,
                                                   [
                                                     ( Semantic_ir.PConstructor
                                                         ("None", None),
                                                       Semantic_ir.Ident
                                                         (List.nth
                                                            default_names index)
                                                     );
                                                     ( Semantic_ir.PConstructor
                                                         ( "Some",
                                                           Some
                                                             (Semantic_ir.PVar
                                                                present_name) ),
                                                       Semantic_ir.Ident
                                                         present_name );
                                                   ] )
                                             else Semantic_ir.Ident name)
                                           argument_names
                                       in
                                       [
                                         ( {
                                             fixed_params =
                                               returned_parameter_tys;
                                             rest_param = None;
                                             return_ty = arity.return_ty;
                                           },
                                           Semantic_ir.Fun
                                             ( List.map
                                                 (fun name ->
                                                   Semantic_ir.PVar name)
                                                 argument_names,
                                               Semantic_ir.Apply
                                                 ( overloaded_projection
                                                     (Semantic_ir.Ident
                                                        function_name)
                                                     source_index,
                                                   selected_arguments ) ) );
                                       ]
                                   | Some rest_ty ->
                                       let fixed_count =
                                         List.length arity.fixed_params
                                       in
                                       let parameter_ty index =
                                         match
                                           List.nth_opt arity.fixed_params index
                                         with
                                         | Some ty -> ty
                                         | None -> rest_ty
                                       in
                                       let build_variadic suffix fixed_count'
                                           rest_param =
                                         let fixed_param_tys =
                                           List.init fixed_count' parameter_ty
                                         in
                                         let argument_names =
                                           List.mapi
                                             (fun index _ ->
                                               "__lg_fnil_argument_"
                                               ^ string_of_int returned_index
                                               ^ "_" ^ suffix ^ "_"
                                               ^ string_of_int index)
                                             fixed_param_tys
                                         in
                                         let rest_name =
                                           "__lg_fnil_argument_"
                                           ^ string_of_int returned_index ^ "_"
                                           ^ suffix ^ "_rest"
                                         in
                                         let returned_parameter_tys =
                                           List.mapi
                                             (fun index parameter_ty ->
                                               if index < default_count then
                                                 TNullable parameter_ty
                                               else parameter_ty)
                                             fixed_param_tys
                                         in
                                         let selected_arguments =
                                           List.mapi
                                             (fun index name ->
                                               if index < default_count then
                                                 let present_name =
                                                   name ^ "_value"
                                                 in
                                                 Semantic_ir.Match
                                                   ( Semantic_ir.Ident name,
                                                     [
                                                       ( Semantic_ir.PConstructor
                                                           ("None", None),
                                                         Semantic_ir.Ident
                                                           (List.nth
                                                              default_names
                                                              index) );
                                                       ( Semantic_ir.PConstructor
                                                           ( "Some",
                                                             Some
                                                               (Semantic_ir.PVar
                                                                  present_name)
                                                           ),
                                                         Semantic_ir.Ident
                                                           present_name );
                                                     ] )
                                               else Semantic_ir.Ident name)
                                             argument_names
                                         in
                                         let fixed_arguments =
                                           selected_arguments
                                           |> List.filteri (fun index _ ->
                                                  index < fixed_count)
                                         in
                                         let rest_prefix =
                                           selected_arguments
                                           |> List.filteri (fun index _ ->
                                                  index >= fixed_count)
                                         in
                                         let rest_sequence =
                                           match (rest_prefix, rest_param) with
                                           | [], None ->
                                               Semantic_ir.Ident
                                                 "Seq.empty"
                                           | prefix, None ->
                                               Semantic_ir.Apply
                                                 ( Semantic_ir.Ident
                                                     "Lg_runtime.Runtime_seq.of_list",
                                                   [ Semantic_ir.List prefix ] )
                                           | [], Some _ ->
                                               Semantic_ir.Ident rest_name
                                           | prefix, Some _ ->
                                               Semantic_ir.Apply
                                                 ( Semantic_ir.Ident
                                                     "Lg_runtime.Runtime_seq.concat",
                                                   [
                                                     Semantic_ir.List
                                                       [
                                                         Semantic_ir.Apply
                                                           ( Semantic_ir.Ident
                                                               "Lg_runtime.Runtime_seq.of_list",
                                                             [
                                                               Semantic_ir.List
                                                                 prefix;
                                                             ] );
                                                         Semantic_ir.Ident
                                                           rest_name;
                                                       ];
                                                   ] )
                                         in
                                         let patterns =
                                           List.map
                                             (fun name ->
                                               Semantic_ir.PVar name)
                                             argument_names
                                           @
                                           match rest_param with
                                           | None -> []
                                           | Some _ ->
                                               [ Semantic_ir.PVar rest_name ]
                                         in
                                         ( {
                                             fixed_params =
                                               returned_parameter_tys;
                                             rest_param;
                                             return_ty = arity.return_ty;
                                           },
                                           Semantic_ir.Fun
                                             ( patterns,
                                               Semantic_ir.Apply
                                                 ( overloaded_projection
                                                     (Semantic_ir.Ident
                                                        function_name)
                                                     source_index,
                                                   fixed_arguments
                                                   @ [ rest_sequence ] ) ) )
                                       in
                                       let variadic_fixed_count =
                                         max fixed_count default_count
                                       in
                                       let variadic =
                                         build_variadic "variadic"
                                           variadic_fixed_count (Some rest_ty)
                                       in
                                       if default_count = 3 && fixed_count <= 2
                                       then
                                         [
                                           build_variadic "fixed2"
                                             (max fixed_count 2) None;
                                           variadic;
                                         ]
                                       else [ variadic ])
                            |> List.concat |> List.split
                          in
                          let bindings =
                            (Semantic_ir.PVar function_name, fn.semantic_expr)
                            :: List.map2
                                 (fun name default ->
                                   ( Semantic_ir.PVar name,
                                     default.semantic_expr ))
                                 default_names defaults
                          in
                          typed_ir (TOverloaded_fn returned_arities)
                            (capture_bindings bindings
                               (overloaded_functions returned_functions)))
                        (adapt_defaults [] 0 defaults))
              | _ -> Error.error ~code:Error_code.Arity "fnil expects a statically typed function"))
      | _ -> Error.error ~code:Error_code.Type_mismatch "fnil called with incompatible arguments"
    
    and compile_static_partial scope env arg_forms =
      match arg_forms with
      | fn_form :: fixed_forms -> (
          match (compile_function_arg scope env fn_form, compile_args_for scope env fixed_forms) with
          | (Error _ as err), _ -> err
          | _, (Error _ as err) -> err
          | Ok fn, Ok fixed_args -> (
              match fn.ty with
              | TFn (parameter_tys, return_ty) ->
                  let accepted_fixed_count =
                    min (List.length fixed_args) (List.length parameter_tys)
                  in
                  let rec take_fixed count acc values =
                    if count = 0 then List.rev acc
                    else
                      match values with
                      | [] -> List.rev acc
                      | value :: rest -> take_fixed (count - 1) (value :: acc) rest
                  in
                  let accepted_fixed_args =
                    take_fixed accepted_fixed_count [] fixed_args
                  in
                  let ignored_fixed_args = drop accepted_fixed_count fixed_args in
                  let expected_fixed_tys =
                    parameter_tys
                    |> List.filteri (fun index _ ->
                           index < accepted_fixed_count)
                  in
                  let rec adapt_fixed adapted expected actual =
                    match (expected, actual) with
                    | [], [] -> Ok (List.rev adapted)
                    | expected :: expected_rest, actual :: actual_rest ->
                        Result.bind
                          (plan_and_emit_argument env ~expected actual)
                          (fun expression ->
                            adapt_fixed
                              (typed_ir expected expression :: adapted)
                              expected_rest actual_rest)
                    | _ -> Error.error ~code:Error_code.Arity "partial fixed arguments do not match function"
                  in
                  Result.map
                    (fun adapted_fixed_args ->
                      let function_name = "__lg_partial_function" in
                      let accepted_fixed_names =
                        List.mapi
                          (fun index _ ->
                            "__lg_partial_fixed_" ^ string_of_int index)
                          adapted_fixed_args
                      in
                      let ignored_fixed_names =
                        ignored_fixed_args
                        |> List.mapi (fun index _ ->
                               "__lg_partial_ignored_"
                               ^ string_of_int (accepted_fixed_count + index))
                      in
                      let fixed_names =
                        accepted_fixed_names @ ignored_fixed_names
                      in
                      let remaining_tys =
                        drop accepted_fixed_count parameter_tys
                      in
                      let remaining_names =
                        remaining_tys
                        |> List.mapi (fun index _ ->
                               "__lg_partial_argument_" ^ string_of_int index)
                      in
                      let bindings =
                        (Semantic_ir.PVar function_name, fn.semantic_expr)
                        :: List.map2
                             (fun name argument ->
                               (Semantic_ir.PVar name, argument.semantic_expr))
                             fixed_names
                             (adapted_fixed_args @ ignored_fixed_args)
                      in
                      typed_ir (TFn (remaining_tys, return_ty))
                        (capture_bindings bindings
                           (Semantic_ir.Fun
                              ( List.map
                                  (fun name -> Semantic_ir.PVar name)
                                  remaining_names,
                                Semantic_ir.Apply
                                  ( Semantic_ir.Ident function_name,
                                    List.map
                                      (fun name -> Semantic_ir.Ident name)
                                      (accepted_fixed_names @ remaining_names)
                                  ) ))))
                    (adapt_fixed [] expected_fixed_tys accepted_fixed_args)
              | TOverloaded_fn arities ->
                  let fixed_count = List.length fixed_args in
                  let selected_arities =
                    arities
                    |> List.mapi (fun index arity -> (index, arity))
                    |> List.filter (fun (_, arity) ->
                           match arity.rest_param with
                           | None -> List.length arity.fixed_params >= fixed_count
                           | Some _ -> true)
                  in
                  (match selected_arities with
                  | [] ->
                      Error.error ~code:Error_code.Arity
                        "partial has no function arity accepting the fixed arguments"
                  | (_, first_arity) :: _ ->
                      let expected_type_at arity index =
                        match List.nth_opt arity.fixed_params index with
                        | Some ty -> Some ty
                        | None -> arity.rest_param
                      in
                      let expected_fixed_tys =
                        List.init fixed_count (fun index ->
                            Option.get (expected_type_at first_arity index))
                      in
                      let compatible_prefix =
                        List.for_all
                          (fun (_, arity) ->
                            List.mapi
                              (fun index expected ->
                                match expected_type_at arity index with
                                | Some actual -> Types.equal actual expected
                                | None -> false)
                              expected_fixed_tys
                            |> List.for_all Fun.id)
                          selected_arities
                      in
                      if not compatible_prefix then
                        Error.error ~code:Error_code.Arity
                          "partial overloaded function arities disagree on fixed argument types"
                      else
                        let rec adapt_fixed adapted expected actual =
                          match (expected, actual) with
                          | [], [] -> Ok (List.rev adapted)
                          | expected :: expected_rest, actual :: actual_rest ->
                              Result.bind
                                (plan_and_emit_argument env ~expected actual)
                                (fun expression ->
                                  adapt_fixed
                                    (typed_ir expected expression :: adapted)
                                    expected_rest actual_rest)
                          | _ ->
                              Error.error ~code:Error_code.Arity
                                "partial fixed arguments do not match function"
                        in
                        Result.map
                          (fun fixed_args ->
                            let function_name = "__lg_partial_function" in
                            let fixed_names =
                              List.mapi
                                (fun index _ ->
                                  "__lg_partial_fixed_" ^ string_of_int index)
                                fixed_args
                            in
                            let returned_arities, returned_functions =
                              selected_arities
                              |> List.mapi (fun returned_index
                                                (source_index, arity) ->
                                     match arity.rest_param with
                                     | None ->
                                         let remaining_tys =
                                           drop fixed_count arity.fixed_params
                                         in
                                         let argument_names =
                                           List.mapi
                                             (fun index _ ->
                                               "__lg_partial_argument_"
                                               ^ string_of_int returned_index
                                               ^ "_" ^ string_of_int index)
                                             remaining_tys
                                         in
                                         ( {
                                             fixed_params = remaining_tys;
                                             rest_param = None;
                                             return_ty = arity.return_ty;
                                           },
                                           Semantic_ir.Fun
                                             ( List.map
                                                 (fun name ->
                                                   Semantic_ir.PVar name)
                                                 argument_names,
                                               Semantic_ir.Apply
                                                 ( overloaded_projection
                                                     (Semantic_ir.Ident
                                                        function_name)
                                                     source_index,
                                                   List.map
                                                     (fun name ->
                                                       Semantic_ir.Ident name)
                                                     (fixed_names @ argument_names)
                                                 ) ) )
                                     | Some rest_ty ->
                                         let source_fixed_count =
                                           List.length arity.fixed_params
                                         in
                                         let remaining_tys =
                                           if fixed_count < source_fixed_count
                                           then
                                             drop fixed_count arity.fixed_params
                                           else []
                                         in
                                         let argument_names =
                                           List.mapi
                                             (fun index _ ->
                                               "__lg_partial_argument_"
                                               ^ string_of_int returned_index
                                               ^ "_" ^ string_of_int index)
                                             remaining_tys
                                         in
                                         let rest_name =
                                           "__lg_partial_argument_"
                                           ^ string_of_int returned_index
                                           ^ "_rest"
                                         in
                                         let supplied_fixed_arguments =
                                           fixed_names
                                           |> List.filteri (fun index _ ->
                                                  index < source_fixed_count)
                                           |> List.map (fun name ->
                                                  Semantic_ir.Ident name)
                                         in
                                         let remaining_fixed_arguments =
                                           List.map
                                             (fun name -> Semantic_ir.Ident name)
                                             argument_names
                                         in
                                         let rest_prefix =
                                           fixed_names
                                           |> List.filteri (fun index _ ->
                                                  index >= source_fixed_count)
                                           |> List.map (fun name ->
                                                  Semantic_ir.Ident name)
                                         in
                                         let rest_sequence =
                                           match rest_prefix with
                                           | [] -> Semantic_ir.Ident rest_name
                                           | prefix ->
                                               Semantic_ir.Apply
                                                 ( Semantic_ir.Ident
                                                     "Lg_runtime.Runtime_seq.concat",
                                                   [
                                                     Semantic_ir.List
                                                       [
                                                         Semantic_ir.Apply
                                                           ( Semantic_ir.Ident
                                                               "Lg_runtime.Runtime_seq.of_list",
                                                             [
                                                               Semantic_ir.List
                                                                 prefix;
                                                             ] );
                                                         Semantic_ir.Ident
                                                           rest_name;
                                                       ];
                                                   ] )
                                         in
                                         ( {
                                             fixed_params = remaining_tys;
                                             rest_param = Some rest_ty;
                                             return_ty = arity.return_ty;
                                           },
                                           Semantic_ir.Fun
                                             ( List.map
                                                 (fun name ->
                                                   Semantic_ir.PVar name)
                                                 argument_names
                                               @ [ Semantic_ir.PVar rest_name ],
                                               Semantic_ir.Apply
                                                 ( overloaded_projection
                                                     (Semantic_ir.Ident
                                                        function_name)
                                                     source_index,
                                                   supplied_fixed_arguments
                                                   @ remaining_fixed_arguments
                                                   @ [ rest_sequence ] ) ) ))
                              |> List.split
                            in
                            let bindings =
                              (Semantic_ir.PVar function_name, fn.semantic_expr)
                              :: List.map2
                                   (fun name argument ->
                                     ( Semantic_ir.PVar name,
                                       argument.semantic_expr ))
                                   fixed_names fixed_args
                            in
                            typed_ir (TOverloaded_fn returned_arities)
                              (capture_bindings bindings
                                 (overloaded_functions returned_functions)))
                          (adapt_fixed [] expected_fixed_tys fixed_args))
              | other ->
                  Error.error ~code:Error_code.Arity
                    ("partial expects a function, got "
                   ^ Types.source_name other)))
      | _ -> Error.error ~code:Error_code.Type_mismatch "partial called with incompatible arguments"

    and compile_static_juxt scope env arg_forms =
      let compile_fns =
        arg_forms
        |> List.fold_left
             (fun acc form ->
               match acc with
               | Error _ as err -> err
               | Ok fns -> (
                   match compile_function_arg scope env form with
                   | Error _ as err -> err
                   | Ok fn -> Ok (fn :: fns)))
             (Ok [])
        |> Result.map List.rev
      in
      match compile_fns with
      | Error _ as err -> err
      | Ok [] -> Error.error ~code:Error_code.Arity "juxt expects at least 1 function"
      | Ok fns -> (
          let rec collect arg_ty ret_ty exprs = function
            | [] -> Ok (arg_ty, ret_ty, List.rev exprs)
            | fn :: rest -> (
                let unary =
                  match fn.ty with
                  | TFn ([ current_arg ], current_ret) ->
                      Some
                        ( current_arg,
                          current_ret,
                          Semantic_ir.Apply
                            (fn.semantic_expr, [ Semantic_ir.Ident "x" ]) )
                  | TOverloaded_fn arities ->
                      arities
                      |> List.mapi (fun index arity -> (index, arity))
                      |> List.find_map (fun (index, arity) ->
                             match (arity.fixed_params, arity.rest_param) with
                             | [ current_arg ], None ->
                                 Some
                                   ( current_arg,
                                     arity.return_ty,
                                     Semantic_ir.Apply
                                       ( overloaded_projection fn.semantic_expr
                                           index,
                                         [ Semantic_ir.Ident "x" ] ) )
                             | _ -> None)
                  | _ -> None
                in
                match unary with
                | Some (current_arg, current_ret, expression)
                  when option_for_all
                         (fun arg_ty ->
                           Types.assignable ~policy:Host_boundary ~expected:arg_ty
                             ~actual:current_arg)
                         arg_ty
                       && option_for_all
                            (fun ret_ty ->
                              Types.assignable ~policy:Host_boundary
                                ~expected:ret_ty ~actual:current_ret)
                            ret_ty ->
                    collect (Some current_arg) (Some current_ret)
                      (expression :: exprs)
                      rest
                | Some (current_arg, _, _)
                  when option_for_all
                         (fun arg_ty ->
                           Types.assignable ~policy:Host_boundary ~expected:arg_ty
                             ~actual:current_arg)
                         arg_ty ->
                    Error.error ~code:Error_code.Semantic "juxt functions must return the same type"
                | Some _ ->
                    Error.error ~code:Error_code.Arity
                      "juxt functions must accept the same argument type"
                | None -> Error.error ~code:Error_code.Arity "juxt expects unary functions")
          in
          match collect None None [] fns with
          | Error _ as err -> err
          | Ok (Some arg_ty, Some ret_ty, exprs) ->
              let result_bindings, results =
                exprs
                |> List.mapi (fun index expression ->
                       let name = "__lg_juxt_result_" ^ string_of_int index in
                       ( (Semantic_ir.PVar name, expression),
                         Semantic_ir.Ident name ))
                |> List.split
              in
              Ok
                (typed_ir
                   (TFn ([ arg_ty ], TVector ret_ty))
                   (Semantic_ir.Fun
                      ( [ Semantic_ir.PVar "x" ],
                        Semantic_ir.Let
                          ( result_bindings,
                            apply "Rrbvec.of_list"
                              [ Semantic_ir.List results ] ) )))
          | Ok _ -> Error.error ~code:Error_code.Arity "juxt expects at least 1 function")

  in
  {
    compile_apply;
    compile_static_fnil;
    compile_static_comp;
    compile_static_partial;
    compile_static_juxt;
  }
