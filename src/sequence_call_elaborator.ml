open Ast
open Types
open Expression_support
module Env = Compiler_environment

type expression_result = (typed_expr, Error.t) result
type call = string -> Env.t -> Ast.form list -> expression_result

type named_call =
  string -> Env.t -> string -> Ast.form list -> expression_result

type t = {
  compile_sort_by : call;
  compile_mapcat : call;
  compile_repeatedly : call;
  compile_reductions : call;
  compile_map_indexed : call;
  compile_mapv : call;
  compile_reduce_kv : call;
  compile_some : call;
  compile_map_call : call;
  compile_keep : call;
  compile_filter : call;
  compile_reduce : call;
}

let reduce_kv_counter = ref 0

let has_source_name name expected =
  String.equal name expected
  || String.ends_with ~suffix:("/" ^ expected) name

let compile_args_for compile_expr scope env arg_forms =
  let rec loop acc = function
    | [] -> Ok (List.rev acc)
    | form :: rest -> (
        match compile_expr scope env form with
        | Ok expr -> loop (expr :: acc) rest
        | Error _ as err -> err)
  in
  loop [] arg_forms

let returns_truthy_value = function
  | TBool | TUnknown | TMeta _ | TVar _ -> true
  | ty ->
      Types.is_dynamic ty
      || Option.is_some (Types.truthy_constraint_info ty)

let truthy_call return_ty fn arguments =
  let call = Semantic_ir.Apply (fn, arguments) in
  if Types.equal return_ty TBool then call
  else if Option.is_some (Types.truthy_constraint_info return_ty) then
    let result_name = "__lg_truthy_callback_result" in
    let result = Semantic_ir.Ident result_name in
    Semantic_ir.Let
      ( [ (Semantic_ir.PVar result_name, call) ],
        Semantic_ir.Apply
          ( Semantic_ir.Apply (Semantic_ir.Ident "fst", [ result ]),
            [ Semantic_ir.Apply (Semantic_ir.Ident "snd", [ result ]) ] ) )
  else
    Semantic_ir.Apply
      (Semantic_ir.Ident "Lg_runtime.Runtime_dynamic.truthy", [ call ])

let normalize_truthy_function fn =
  match (fn.ty, Semantic_ir.unlocated fn.semantic_expr) with
  | TFn (parameters, return_ty), Semantic_ir.Fun (patterns, body)
    when Option.is_some (Types.truthy_constraint_info return_ty) ->
      typed_ir (TFn (parameters, TBool))
        (Semantic_ir.Fun
           (patterns, Expression_support.truthiness_expression return_ty body))
  | _ -> fn

let create ~compile_expr ~pack_dynamic_value ~dynamic_unpack
    ~pack_constrained_value =
    let special_forms : Special_form_elaborator.t =
      Special_form_elaborator.create ~compile_expr ~dynamic_unpack
        ~pack_dynamic_value
        ~pack_constrained_value
      ~argument_compatible:(fun expected actual ->
        Types.assignable ~policy:Host_boundary ~expected ~actual)
  in
  let compile_body = special_forms.compile_body in
  let compile_function_arg scope env form =
    let compiled =
      match form with
      | FSymbol name -> lookup_function scope env name
      | form -> compile_expr scope env form
    in
    Result.bind compiled adapt_set_callable
  in
  let rec protocol_capability_pattern name ty =
    match Types.protocol_constraint_info ty with
    | Some (protocol_id, _, value_ty) ->
        Semantic_ir.PTuple
          [
            Semantic_ir.PVar
              (Types.protocol_witness_name name protocol_id);
            protocol_capability_pattern name value_ty;
          ]
    | None -> Semantic_ir.PVar name
  in
  let compile_contextual_fn scope env ?name ?expected_return_ty
      ?(refine_open_overrides = false) ~param_type_overrides params body_forms =
    let env = Env.with_expected_type None env in
    let lookup_function_ty name =
      match lookup_function scope env name with
      | Ok fn -> Ok fn.ty
      | Error _ as error -> error
    in
    let function_env =
      match name with
      | None -> env
      | Some name ->
          let parameter_tys =
            List.map
              (Option.value ~default:TUnknown)
              param_type_overrides
          in
          let ocaml_name = "__lg_named_fn_" ^ Names.sanitize_name name in
          Env.add (Names.scoped_key scope name)
            (Types.binding ocaml_name (TFn (parameter_tys, TUnknown)))
            env
    in
    let compile_default expected form =
      compile_expr scope
        (Env.with_expected_type (Some expected) function_env)
        form
    in
    let compile_function_body =
      Option.map
        (fun expected_return_ty function_env _parameter_tys body_forms ->
          compile_body scope
            (function_env
            |> Env.with_source_macros_expanded true
            |> Env.with_expected_type (Some expected_return_ty))
            "function body requires at least one form" body_forms)
        expected_return_ty
    in
    Function_elaborator.prepare ~refine_open_overrides ~param_type_overrides
      ?compile_function_body ~compile_default ~lookup_function_ty ~compile_body
      scope function_env params body_forms
    |> Result.map Function_elaborator.fn_code
    |> fun result ->
    Result.bind result (fun function_ ->
           match name with
           | None -> Ok function_
           | Some name -> (
               match Semantic_ir.unlocated function_.semantic_expr with
               | Semantic_ir.Fun (patterns, body) ->
                   let ocaml_name =
                     "__lg_named_fn_" ^ Names.sanitize_name name
                   in
                   Ok
                     {
                       function_ with
                       semantic_expr =
                         Semantic_ir.annotate function_.ty
                           (Semantic_ir.LetRecIn
                              ( ocaml_name,
                                patterns,
                                body,
                                Semantic_ir.Ident ocaml_name ));
                     }
               | _ -> Error.error "named fn requires a function body"))
  in
  let external_record_type = function
    | TOcaml type_name -> (
        match Ocaml_signature.record_type type_name with
        | Ok (TNamed_record record) -> Some (TNamed_record record)
        | Ok _ | Error _ -> None)
    | TOcaml_app (type_name, arguments) -> (
        match Ocaml_signature.record_type type_name with
        | Ok (TNamed_record record)
          when List.length record.type_parameters = List.length arguments ->
            let substitutions =
              List.combine record.type_parameters arguments
              |> List.map (fun (parameter, argument) ->
                     (Type_solver.Declared parameter, argument))
              |> Type_solver.of_list
            in
            Some (Type_solver.apply substitutions (TNamed_record record))
        | Ok _ | Error _ -> None)
    | ty when Option.is_some (Types.record_fields ty) -> Some ty
    | _ -> None
  in
  let structural_record_projection expected_ty actual_ty item_name =
    match (expected_ty, external_record_type actual_ty) with
    | TRecord expected_fields, Some source_ty
      when not (Types.is_dynamic actual_ty)
           && not (Types.is_dynamic source_ty)
           && Types.assignable ~policy:Host_boundary ~expected:expected_ty
                ~actual:source_ty ->
        let actual_fields = Types.record_fields source_ty |> Option.get in
        let source = typed_ir source_ty (Semantic_ir.Ident item_name) in
        let rec project fields = function
          | [] ->
              Some (Structural_map.record_expr expected_fields (List.rev fields))
          | (expected : field) :: rest -> (
              match Types.find_field expected.keyword actual_fields with
              | Some actual ->
                  let value = Structural_map.field_expr source actual in
                  project ((expected, value) :: fields) rest
              | None -> None)
        in
        project [] expected_fields
    | _ -> None
  in
  let adapt_unary_function env actual_ty fn =
    let fn =
      match fn.ty with
      | TFn ([ parameter_ty ], _) ->
          { fn with
            semantic_expr =
              Expression_support.constrain_record_function_argument_expr fn parameter_ty }
      | _ -> fn
    in
    match fn.ty with
    | TFn ([ expected_ty ], return_ty)
      when Type_solver.is_open expected_ty ->
        let return_ty =
          Types.instantiate_type ~templates:[ expected_ty ] ~actuals:[ actual_ty ]
            return_ty
        in
        Ok
          (normalize_truthy_function
             (typed_ir (TFn ([ actual_ty ], return_ty)) fn.semantic_expr))
    | TFn ([ expected_ty ], return_ty)
      when Types.is_dynamic actual_ty && not (Types.is_dynamic expected_ty) ->
        let item_name = "__lg_erased_sequence_item" in
        Result.map
          (fun item ->
            normalize_truthy_function
              (typed_ir (TFn ([ actual_ty ], return_ty))
                 (Semantic_ir.Fun
                    ( [ Semantic_ir.PVar item_name ],
                      Semantic_ir.Apply (fn.semantic_expr, [ item ]) ))))
          (dynamic_unpack env expected_ty (Semantic_ir.Ident item_name))
    | TFn ([ expected_ty ], return_ty)
      when Types.is_dynamic expected_ty && not (Types.is_dynamic actual_ty) ->
        let item_name = "__lg_static_sequence_item" in
        let item = typed_ir actual_ty (Semantic_ir.Ident item_name) in
        Result.map
          (fun item ->
            normalize_truthy_function
              (typed_ir (TFn ([ actual_ty ], return_ty))
                 (Semantic_ir.Fun
                    ( [ Semantic_ir.PVar item_name ],
                      Semantic_ir.Apply (fn.semantic_expr, [ item ]) ))))
          (pack_dynamic_value env expected_ty item)
    | TFn ([ expected_ty ], return_ty)
      when (not (Types.equal expected_ty actual_ty))
           && Types.assignable ~policy:Host_boundary ~expected:expected_ty
                ~actual:actual_ty -> (
        let item_name = "__lg_structural_sequence_item" in
        match structural_record_projection expected_ty actual_ty item_name with
        | Some projected ->
            Ok
              (normalize_truthy_function
                 (typed_ir (TFn ([ actual_ty ], return_ty))
                    (Semantic_ir.Fun
                       ( [ Semantic_ir.PVar item_name ],
                         Semantic_ir.Apply
                           (fn.semantic_expr, [ projected.semantic_expr ]) ))))
        | None -> Ok (normalize_truthy_function fn))
    | _ -> Ok (normalize_truthy_function fn)
  in
  let adapt_reducer_function env actual_item_ty fn =
    match fn.ty with
    | TFn ([ accumulator_ty; expected_item_ty ], return_ty)
      when Types.is_dynamic actual_item_ty
           && not (Types.is_dynamic expected_item_ty) ->
        let accumulator_name = "__lg_reduce_accumulator" in
        let item_name = "__lg_erased_reduce_item" in
        Result.map
          (fun item ->
            typed_ir
              (TFn ([ accumulator_ty; actual_item_ty ], return_ty))
              (Semantic_ir.Fun
                 ( [
                     Semantic_ir.PVar accumulator_name;
                     Semantic_ir.PVar item_name;
                   ],
                   Semantic_ir.Apply
                     ( fn.semantic_expr,
                       [ Semantic_ir.Ident accumulator_name; item ] ) )))
          (dynamic_unpack env expected_item_ty (Semantic_ir.Ident item_name))
    | TFn ([ accumulator_ty; expected_item_ty ], return_ty)
      when Types.is_dynamic expected_item_ty
           && not (Types.is_dynamic actual_item_ty) ->
        let accumulator_name = "__lg_reduce_accumulator" in
        let item_name = "__lg_static_reduce_item" in
        let item = typed_ir actual_item_ty (Semantic_ir.Ident item_name) in
        Result.map
          (fun item ->
            typed_ir
              (TFn ([ accumulator_ty; actual_item_ty ], return_ty))
              (Semantic_ir.Fun
                 ( [
                     Semantic_ir.PVar accumulator_name;
                     Semantic_ir.PVar item_name;
                   ],
                   Semantic_ir.Apply
                     ( fn.semantic_expr,
                       [ Semantic_ir.Ident accumulator_name; item ] ) )))
          (pack_dynamic_value env expected_item_ty item)
    | _ -> Ok fn
  in
  let adapt_reducer_return env actual_accumulator_ty fn =
    match fn.ty with
    | TFn ([ expected_accumulator_ty; item_ty ], return_ty)
      when (not (Types.equal expected_accumulator_ty actual_accumulator_ty))
           && Option.is_none (Types.reduced_element return_ty)
           && Types.assignable ~policy:Host_boundary
                ~expected:(Types.constraint_value_type expected_accumulator_ty)
                ~actual:actual_accumulator_ty
           && Types.assignable ~policy:Host_boundary
                ~expected:actual_accumulator_ty ~actual:return_ty ->
        let accumulator_name = "__lg_capability_reduce_accumulator" in
        let item_name = "__lg_capability_reduce_item" in
        let result =
          typed_ir return_ty
            (Semantic_ir.Apply
               ( fn.semantic_expr,
                 [
                   Semantic_ir.Ident accumulator_name;
                   Semantic_ir.Ident item_name;
                 ] ))
        in
        Result.map
          (fun result ->
            typed_ir
              (TFn
                 ( [ expected_accumulator_ty; item_ty ],
                   expected_accumulator_ty ))
              (Semantic_ir.Fun
                 ( [
                     Semantic_ir.PVar accumulator_name;
                     Semantic_ir.PVar item_name;
                   ],
                   result )))
          (pack_constrained_value env expected_accumulator_ty result)
    | TFn ([ expected_accumulator_ty; item_ty ], return_ty)
      when (not (Types.equal return_ty actual_accumulator_ty))
           && Types.equal
                (Types.constraint_value_type return_ty)
                actual_accumulator_ty ->
        let accumulator_name = "__lg_protocol_reduce_accumulator" in
        let item_name = "__lg_protocol_reduce_item" in
        let result =
          Semantic_ir.Apply
            ( fn.semantic_expr,
              [
                Semantic_ir.Ident accumulator_name;
                Semantic_ir.Ident item_name;
              ] )
        in
        Ok
          (typed_ir
             (TFn
                ( [ expected_accumulator_ty; item_ty ],
                  actual_accumulator_ty ))
             (Semantic_ir.Fun
                ( [
                    Semantic_ir.PVar accumulator_name;
                    Semantic_ir.PVar item_name;
                  ],
                  coerce_expression_to_type actual_accumulator_ty return_ty
                    result )))
    | TFn ([ _expected_accumulator_ty; item_ty ], return_ty)
      when Types.is_dynamic actual_accumulator_ty
           && not (Types.is_dynamic return_ty)
           && Option.is_none (Types.reduced_element return_ty) ->
        let accumulator_name = "__lg_erased_reduce_accumulator" in
        let item_name = "__lg_erased_reduce_return_item" in
        let result =
          typed_ir return_ty
            (Semantic_ir.Apply
               ( fn.semantic_expr,
                 [
                   Semantic_ir.Ident accumulator_name;
                   Semantic_ir.Ident item_name;
                 ] ))
        in
        Result.map
          (fun result ->
            typed_ir
              (TFn
                 ([ actual_accumulator_ty; item_ty ], actual_accumulator_ty))
              (Semantic_ir.Fun
                 ( [
                     Semantic_ir.PVar accumulator_name;
                     Semantic_ir.PVar item_name;
                   ],
                   result )))
          (pack_dynamic_value env actual_accumulator_ty result)
    | TFn ([ expected_accumulator_ty; item_ty ], return_ty)
      when Types.is_dynamic return_ty
           && not (Types.is_dynamic actual_accumulator_ty) ->
        let accumulator_name = "__lg_static_reduce_accumulator" in
        let item_name = "__lg_reduce_item" in
        let accumulator =
          typed_ir actual_accumulator_ty
            (Semantic_ir.Ident accumulator_name)
        in
        let accumulator =
          if Types.is_dynamic expected_accumulator_ty then
            pack_dynamic_value env expected_accumulator_ty accumulator
          else if
            Types.assignable ~policy:Host_boundary
              ~expected:expected_accumulator_ty
              ~actual:actual_accumulator_ty
          then Ok accumulator.semantic_expr
          else Error.error "reducer accumulator type does not match init"
        in
        Result.bind accumulator (fun accumulator ->
            let call =
              Semantic_ir.Apply
                ( fn.semantic_expr,
                  [ accumulator; Semantic_ir.Ident item_name ] )
            in
            Result.map
              (fun result ->
                typed_ir
                  (TFn
                     ( [ actual_accumulator_ty; item_ty ],
                       actual_accumulator_ty ))
                  (Semantic_ir.Fun
                     ( [ Semantic_ir.PVar accumulator_name;
                         Semantic_ir.PVar item_name ],
                       result )))
              (dynamic_unpack env actual_accumulator_ty call))
    | _ -> Ok fn
  in
  let uses_builtin_reducible = function
    | TList _ | TVector _ | TSet _ | TArray _ | TString | TSeq _
    | TOcaml_app (("list" | "array" | "Seq.t" | "Seq"), [ _ ]) ->
        true
    | _ -> false
  in
  let adapt_protocol_argument env expected argument =
    if Type_solver.is_open expected then Ok argument.semantic_expr
    else if Types.is_dynamic expected then
      pack_dynamic_value env expected argument
    else if
      Types.equal expected argument.ty
      || Types.assignable ~policy:Host_boundary ~expected ~actual:argument.ty
    then Ok argument.semantic_expr
    else if Types.is_dynamic argument.ty then
      dynamic_unpack env expected argument.semantic_expr
    else Error.error "protocol argument type does not match implementation"
  in
  let reify_reducible_method collection =
    match collection.ty with
    | TOcaml_app ("Lg_runtime.Runtime_reify.t", [ payload_ty ]) ->
        let payload =
          apply "Lg_runtime.Runtime_reify.payload"
            [ collection.semantic_expr ]
        in
        let rec select ty expression =
          match Types.reify_protocol_payload_info ty with
          | Some (candidate, methods_ty, rest_ty) ->
              if
                String.equal candidate
                  (Protocol_id.to_string Core_protocols.reducible_id)
              then Some (methods_ty, apply "fst" [ expression ])
              else select rest_ty (apply "snd" [ expression ])
          | None -> None
        in
        select payload_ty payload
    | _ -> None
  in
  let reduce_expression env ?(short_circuit = false) ~result_ty fn init
      collection sequence =
    if short_circuit || uses_builtin_reducible collection.ty then
      Ok
        (Collection_capability.reduce_expr env ~short_circuit fn init collection
           sequence)
    else
      match reify_reducible_method collection with
      | Some (TFn ([ reducer_ty; initial_ty ], _), method_expr) ->
          Result.bind (adapt_protocol_argument env reducer_ty fn) (fun reducer ->
              Result.map
                (fun initial ->
                  Semantic_ir.Apply (method_expr, [ reducer; initial ]))
                (adapt_protocol_argument env initial_ty init))
      | Some _ -> Error.error "Reducible reify method has an invalid type"
      | None ->
      match
        Core_protocols.find_reducible collection.ty
          (Compiler_environment.protocols env)
      with
      | Some
          { ty = TFn ([ _receiver_ty; reducer_ty; initial_ty ], return_ty);
            ocaml_name;
            _ } ->
          Result.bind (adapt_protocol_argument env reducer_ty fn) (fun reducer ->
              Result.bind
                (adapt_protocol_argument env initial_ty init)
                (fun initial ->
                  let call =
                    apply ocaml_name
                      [ collection.semantic_expr; reducer; initial ]
                  in
                  if Types.is_dynamic result_ty then Ok call
                  else if Types.is_dynamic return_ty then
                    dynamic_unpack env result_ty call
                  else if
                    Types.equal result_ty return_ty
                    || Types.assignable ~policy:Host_boundary
                         ~expected:result_ty ~actual:return_ty
                  then Ok call
                  else Error.error "Reducible result type does not match init"))
      | Some _ | None ->
          Ok
            (Collection_capability.reduce_expr env ~short_circuit fn init
               collection sequence)
  in
  let is_callable_map_type ty =
    Option.is_some (Types.dynamic_map_types ty)
    || match ty with
       | TRecord _ | TNamed_record _ -> true
       | _ -> false
  in
  let optional_payload_type = function
    | TNullable payload | TOcaml_app ("option", [ payload ]) -> Some payload
    | _ -> None
  in
  let adapt_constant_callable element_ty callable =
    match Types.constant_function_result callable.ty with
    | None -> Ok callable
    | Some return_ty ->
        let result_name = "__lg_map_constant_function_result" in
        let item_name = "__lg_map_constant_function_item" in
        Ok
          (typed_ir (TFn ([ element_ty ], return_ty))
             (Semantic_ir.Let
                ( [
                    (Semantic_ir.PVar result_name, callable.semantic_expr);
                  ],
                  Semantic_ir.Fun
                    ( [ Semantic_ir.PVar item_name ],
                      Semantic_ir.Sequence
                        [
                          Semantic_ir.evaluate_for_effect
                            (Semantic_ir.Ident item_name);
                          Semantic_ir.Ident result_name;
                        ] ) )))
  in
  let adapt_optional_map_callable element_ty callable =
    match (optional_payload_type element_ty, Types.dynamic_map_types callable.ty) with
    | Some payload_ty, Some (key_ty, value_ty)
      when Option.is_none (optional_payload_type key_ty)
           && Types.assignable ~policy:Host_boundary ~expected:key_ty
             ~actual:payload_ty ->
        let callable_name = "__lg_optional_map_callable" in
        let item_name = "__lg_optional_map_item" in
        let key_name = "__lg_optional_map_key" in
        let map_expr = Semantic_ir.Ident callable_name in
        let lookup =
          Semantic_ir.Apply
            ( Semantic_ir.Ident "Lg_runtime.Runtime_map.get_option",
              [ map_expr; Semantic_ir.Ident key_name ] )
        in
        Ok
          (typed_ir (TFn ([ element_ty ], TNullable value_ty))
             (Semantic_ir.Let
                ( [ (Semantic_ir.PVar callable_name, callable.semantic_expr) ],
                  Semantic_ir.Fun
                    ( [ Semantic_ir.PVar item_name ],
                      Semantic_ir.Match
                        ( Semantic_ir.Ident item_name,
                          [
                            ( Semantic_ir.PConstructor ("None", None),
                              Semantic_ir.Constructor ("None", None) );
                            ( Semantic_ir.PConstructor
                                ("Some", Some (Semantic_ir.PVar key_name)),
                              lookup );
                          ] ) ) )))
    | _ -> Ok callable
  in
  let compile_function_arg_for_collection scope env ?expected_return_ty
      element_ty form =
    let element_ty =
      Collection_capability.resolve_callback_record env element_ty
    in
    match form with
    | FKeyword keyword ->
        let item_name = "__lg_keyword_function_item" in
        let binding = Types.binding item_name element_ty in
        let function_env =
          Env.add (Names.scoped_key scope item_name) binding env
        in
        compile_expr scope function_env
          (FList [ FKeyword keyword; FSymbol item_name ])
        |> Result.map (fun body ->
            typed_ir
              (TFn ([ element_ty ], body.ty))
                 (Semantic_ir.Fun
                    ([ Semantic_ir.PVar item_name ], body.semantic_expr)))
    | FList (FSymbol "juxt" :: keyword_forms)
      when keyword_forms <> []
           && List.for_all
                (function FKeyword _ -> true | _ -> false)
                keyword_forms ->
        let item_name = "__lg_juxt_keyword_item" in
        let binding = Types.binding item_name element_ty in
        let function_env =
          Env.add (Names.scoped_key scope item_name) binding env
        in
        let dynamic = Types.dynamic_constraint TUnknown in
        let rec compile_keywords compiled = function
          | [] -> Ok (List.rev compiled)
          | FKeyword keyword :: rest ->
              Result.bind
                (compile_expr scope function_env
                   (FList [ FKeyword keyword; FSymbol item_name ]))
                (fun value ->
                  Result.bind (pack_dynamic_value env dynamic value)
                    (fun value ->
                      compile_keywords (value :: compiled) rest))
          | _ -> assert false
        in
        Result.map
          (fun values ->
            typed_ir (TFn ([ element_ty ], TVector dynamic))
              (Semantic_ir.Fun
                 ( [ Semantic_ir.PVar item_name ],
                   apply "Rrbvec.of_list" [ Semantic_ir.List values ] )))
          (compile_keywords [] keyword_forms)
    | FList (FSymbol "fn" :: (FVector [ _ ] as params) :: body_forms) ->
        compile_contextual_fn scope env ?expected_return_ty
          ~param_type_overrides:[ Some element_ty ] params body_forms
    | FList
        (FSymbol "fn" :: FSymbol name :: (FVector [ _ ] as params)
        :: body_forms) ->
        compile_contextual_fn scope env ~name ?expected_return_ty
          ~param_type_overrides:[ Some element_ty ] params body_forms
    | FList (FSymbol "__lg_hash-set" :: _) as form ->
        Result.bind
          (compile_expr scope
             (Env.with_expected_type (Some (TSet element_ty)) env)
             form)
          adapt_set_callable
    | FSymbol name -> (
        let compile_deferred_call () =
          let item_name = "__lg_protocol_function_item" in
          let binding = Types.binding item_name element_ty in
          let function_env =
            Env.add (Names.scoped_key scope item_name) binding env
          in
          compile_expr scope function_env
            (FList [ FSymbol name; FSymbol item_name ])
          |> Result.map (fun body ->
                 typed_ir
                   (TFn ([ element_ty ], body.ty))
                   (Semantic_ir.Fun
                      ( [ protocol_capability_pattern item_name element_ty ],
                        body.semantic_expr )))
        in
        let function_ = lookup_function scope env name in
        match function_ with
        | Ok _ when (match Resolver.lookup_binding scope env name with
                     | Ok binding -> List.exists Option.is_some binding.row_param_types
                     | Error _ -> false) ->
            compile_deferred_call ()
        | Ok { ty = TOcaml "__declared_fn" | TUnknown | TMeta _ | TVar _; _ } ->
            compile_deferred_call ()
        | Ok function_ when Types.is_dynamic function_.ty ->
            compile_deferred_call ()
        | Ok function_ when is_callable_map_type function_.ty ->
            compile_deferred_call ()
        | Ok _
          when has_source_name name "zero?"
               || has_source_name name "pos?"
               || has_source_name name "neg?"
               || has_source_name name "nil?"
               || has_source_name name "true?"
               || has_source_name name "false?"
               || has_source_name name "not" ->
            compile_deferred_call ()
        | Ok { ty = TOverloaded_fn arities; _ }
          when List.exists
                 (fun arity ->
                   let fixed_count = List.length arity.fixed_params in
                   fixed_count = 1
                   || (fixed_count < 1 && Option.is_some arity.rest_param))
                 arities ->
            compile_deferred_call ()
        | Ok
            {
              ty = TFn ([ parameter_ty ], _);
              _;
            }
          when Option.is_some (Types.seqable_constraint_info parameter_ty)
               || Option.is_some
                    (Types.protocol_constraint_info parameter_ty) ->
            compile_deferred_call ()
        | Ok function_ ->
            Result.bind (adapt_constant_callable element_ty function_)
              adapt_set_callable
        | Error _ -> compile_deferred_call ())
    | form ->
        Result.bind (compile_function_arg scope env form) (fun callable ->
            Result.bind (adapt_constant_callable element_ty callable)
              (fun callable ->
            Result.bind (adapt_optional_map_callable element_ty callable)
              (fun callable ->
            let callable_map = is_callable_map_type callable.ty in
            if not callable_map then Ok callable
            else
              let callable_name = "__lg_map_callable" in
              let item_name = "__lg_map_callable_item" in
              let callable_binding = Types.binding callable_name callable.ty in
              let item_binding = Types.binding item_name element_ty in
              let function_env =
                env
                |> Env.add (Names.scoped_key scope callable_name)
                     callable_binding
                |> Env.add (Names.scoped_key scope item_name) item_binding
              in
              Result.map
                (fun body ->
                  typed_ir (TFn ([ element_ty ], body.ty))
                    (Semantic_ir.Let
                       ( [
                           ( Semantic_ir.PVar callable_name,
                             callable.semantic_expr );
                         ],
                         Semantic_ir.Fun
                           ( [ Semantic_ir.PVar item_name ],
                             body.semantic_expr ) )))
                (compile_expr scope function_env
                   (FList
                      [ FSymbol callable_name; FSymbol item_name ])))))
  in
  let compile_function_arg_for_collections scope env element_tys = function
    | (FSymbol name as form) ->
        Result.bind (compile_function_arg scope env form) (fun function_arg ->
            match function_arg.ty with
            | TOverloaded_fn
                [
                  {
                    fixed_params = [];
                    rest_param = Some rest_param;
                    return_ty = TVector return_element;
                  };
                ]
              when Types.equal rest_param return_element ->
        let parameter_names =
          List.mapi
            (fun index _ -> "__lg_map_argument_" ^ string_of_int index)
            element_tys
        in
        let function_env =
          List.fold_left2
            (fun env parameter_name element_ty ->
              Env.add (Names.scoped_key scope parameter_name)
                (Types.binding parameter_name element_ty)
                env)
            (Env.with_expected_type None env)
            parameter_names element_tys
        in
        Result.map
          (fun body ->
            typed_ir (TFn (element_tys, body.ty))
              (Semantic_ir.Fun
                 ( List.map
                     (fun parameter_name -> Semantic_ir.PVar parameter_name)
                     parameter_names,
                   body.semantic_expr )))
          (compile_expr scope function_env
             (FList
                (FSymbol name
                :: List.map (fun name -> FSymbol name) parameter_names)))
            | _ -> Ok function_arg)
    | FList (FSymbol "fn" :: (FVector parameters as params) :: body_forms)
      when List.length parameters = List.length element_tys ->
        compile_contextual_fn scope env
          ~param_type_overrides:(List.map (fun ty -> Some ty) element_tys)
          params body_forms
    | FList
        (FSymbol "fn" :: FSymbol name :: (FVector parameters as params)
        :: body_forms)
      when List.length parameters = List.length element_tys ->
        compile_contextual_fn scope env ~name
          ~param_type_overrides:(List.map (fun ty -> Some ty) element_tys)
          params body_forms
    | form -> compile_function_arg scope env form
  in
  let compile_reducer scope env accumulator_ty element_ty = function
    | FList
        (FSymbol "fn"
        :: FVector [ FSymbol accumulator; FSymbol element ]
        :: body_forms)
      when
        not (Type_solver.is_open accumulator_ty) ->
        let accumulator_binding =
          Types.binding (Names.sanitize_name accumulator) accumulator_ty
        in
        let element_binding =
          Types.binding (Names.sanitize_name element) element_ty
        in
        let function_env =
          env
          |> Env.add (Names.scoped_key scope accumulator) accumulator_binding
          |> Env.add (Names.scoped_key scope element) element_binding
          |> Env.with_expected_type (Some accumulator_ty)
        in
        let pattern binding ty =
          match ty with
          | TNamed_record record ->
              Semantic_ir.PConstraint
                ( Semantic_ir.PVar binding.ocaml_name,
                  Expression_support.record_type_application record.type_name
                    record.type_arguments )
          | TOcaml _ | TOcaml_app _ ->
              Semantic_ir.PTyped (Semantic_ir.PVar binding.ocaml_name, ty)
          | _ -> Semantic_ir.PVar binding.ocaml_name
        in
        compile_body scope function_env
          "function body requires at least one form" body_forms
        |> Result.map (fun body ->
            typed_ir
              (TFn ([ accumulator_ty; element_ty ], body.ty))
              (Semantic_ir.Fun
                 ( [
                     pattern accumulator_binding accumulator_ty;
                     pattern element_binding element_ty;
                   ],
                   body.semantic_expr )))
        |> fun result ->
        Result.bind result (adapt_reducer_return env accumulator_ty)
    | FList
        (FSymbol "fn"
        :: (FVector [ (FVector _ as _accumulator); _element ] as params)
        :: body_forms) ->
        compile_contextual_fn scope env
          ~expected_return_ty:accumulator_ty
          ~refine_open_overrides:(Type_solver.is_open accumulator_ty)
          ~param_type_overrides:[ Some accumulator_ty; Some element_ty ]
          params body_forms
        |> fun result ->
        Result.bind result (adapt_reducer_return env accumulator_ty)
    | FList
        (FSymbol "fn"
        :: (FVector [ _accumulator; _element ] as params)
        :: body_forms) ->
        compile_contextual_fn scope env
          ~expected_return_ty:accumulator_ty
          ~refine_open_overrides:(Type_solver.is_open accumulator_ty)
          ~param_type_overrides:[ Some accumulator_ty; Some element_ty ]
          params body_forms
        |> fun result ->
        Result.bind result (adapt_reducer_return env accumulator_ty)
    | FList
        (FSymbol "fn" :: FSymbol name
        :: (FVector [ _accumulator; _element ] as params)
        :: body_forms) ->
        compile_contextual_fn scope env ~name
          ~expected_return_ty:accumulator_ty
          ~refine_open_overrides:
            (match accumulator_ty with
            | TSet (TUnknown | TMeta _ | TVar _) -> true
            | _ -> false)
          ~param_type_overrides:[ Some accumulator_ty; Some element_ty ]
          params body_forms
        |> fun result ->
        Result.bind result (adapt_reducer_return env accumulator_ty)
    | FSymbol name ->
        let accumulator_name = "__lg_symbol_reduce_accumulator" in
        let item_name = "__lg_symbol_reduce_item" in
        let rec capability_pattern name ty =
          match Types.protocol_constraint_info ty with
          | Some (protocol_id, _, value_ty) ->
              Semantic_ir.PTuple
                [
                  Semantic_ir.PVar
                    (Types.protocol_witness_name name protocol_id);
                  capability_pattern name value_ty;
                ]
          | None -> (
              match ty with
              | TConstraint
                  (Seqable_constraint { requirement; storage = value_ty; _ }) ->
                  Semantic_ir.PTuple
                    [
                      Semantic_ir.PVar
                        (if requirement = Required then
                           name ^ "__seq"
                         else name ^ "__seq_optional");
                      capability_pattern name value_ty;
                    ]
              | _ -> Semantic_ir.PVar name)
        in
        let function_env =
          env
          |> Env.add (Names.scoped_key scope accumulator_name)
               (Types.binding accumulator_name accumulator_ty)
          |> Env.add (Names.scoped_key scope item_name)
               (Types.binding item_name element_ty)
          |> Env.with_expected_type (Some accumulator_ty)
        in
        compile_expr scope function_env
          (FList
             [
               FSymbol name;
               FSymbol accumulator_name;
               FSymbol item_name;
             ])
        |> Result.map (fun body ->
               typed_ir
                 (TFn ([ accumulator_ty; element_ty ], body.ty))
                 (Semantic_ir.Fun
                    ( [
                        capability_pattern accumulator_name accumulator_ty;
                        capability_pattern item_name element_ty;
                      ],
                      body.semantic_expr )))
        |> fun result ->
        Result.bind result (adapt_reducer_return env accumulator_ty)
    | form ->
        Result.bind (compile_function_arg scope env form)
          (fun fn ->
            Result.bind (adapt_reducer_function env element_ty fn)
              (adapt_reducer_return env accumulator_ty))
  in
  let compile_kv_reducer scope env accumulator_ty key_ty value_ty = function
    | FList
        (FSymbol "fn"
        :: (FVector [ _accumulator; _key; _value ] as params)
        :: body_forms) ->
        compile_contextual_fn scope env
          ~param_type_overrides:
            [ Some accumulator_ty; Some key_ty; Some value_ty ]
          params body_forms
    | FList
        (FSymbol "fn" :: FSymbol name
        :: (FVector [ _accumulator; _key; _value ] as params)
        :: body_forms) ->
        compile_contextual_fn scope env ~name
          ~param_type_overrides:
            [ Some accumulator_ty; Some key_ty; Some value_ty ]
          params body_forms
    | form -> compile_function_arg scope env form
  in
  let collection_to_list_expr env collection =
    match Core_sequence_transform.collection_to_list_expr collection with
    | Ok _ as result -> result
    | Error _ ->
        Collection_capability.to_seq_expr env collection
        |> Result.map (fun (inner, sequence) ->
               ( inner,
                 Semantic_ir.Apply
                   (Semantic_ir.Ident "List.of_seq", [ sequence ]) ))
  in
  let rec comparable_type = function
      | TInt | TString | TSymbol | TKeyword | TBool | TUnknown -> true
      | _ -> false
    and compile_sort_by scope env arg_forms =
      let sort_default fn inner list_expr =
        match fn.ty with
        | TFn ([ param_ty ], key_ty) when Types.equal param_ty inner -> (
            let compare =
              if Types.is_dynamic key_ty then
                Some "Lg_runtime.Runtime_dynamic.compare"
              else if comparable_type key_ty then Some "Stdlib.compare"
              else if
                match key_ty with TUnknown | TMeta _ | TVar _ -> true | _ -> false
              then Some "Stdlib.compare"
              else None
            in
            match compare with
            | None ->
                Error.error
                  "sort-by key function must return a comparable value"
            | Some compare ->
                Ok
                  (typed_ir (TList inner)
                     (apply "List.sort"
                        [
                          Semantic_ir.Fun
                            ( [
                                Semantic_ir.PVar "left";
                                Semantic_ir.PVar "right";
                              ],
                              apply compare
                                [
                                  Semantic_ir.Apply
                                    ( fn.semantic_expr,
                                      [ Semantic_ir.Ident "left" ] );
                                  Semantic_ir.Apply
                                    ( fn.semantic_expr,
                                      [ Semantic_ir.Ident "right" ] );
                                ] );
                          list_expr;
                        ])))
        | TFn ([ param_ty ], _) when not (Types.equal param_ty inner) ->
            Error.error "sort-by key function must match collection elements"
        | TFn _ ->
            Error.error
              "sort-by key function must return a comparable value"
        | _ -> Error.error "sort-by expects a function"
      in
      let sort_with_comparator fn comparator inner list_expr =
        match (fn.ty, comparator.ty) with
        | ( TFn ([ param_ty ], key_ty),
            TFn ([ left_ty; right_ty ], return_ty) )
          when Types.equal param_ty inner
               && Types.assignable ~policy:Host_boundary ~expected:left_ty
                    ~actual:key_ty
               && Types.assignable ~policy:Host_boundary ~expected:right_ty
                    ~actual:key_ty
               && (Types.equal return_ty TInt
                  || Types.equal return_ty (TOcaml "int")) ->
            let left = "__lg_sort_by_left" in
            let right = "__lg_sort_by_right" in
            Ok
              (typed_ir (TList inner)
                 (apply "List.sort"
                    [
                      Semantic_ir.Fun
                        ( [ Semantic_ir.PVar left; Semantic_ir.PVar right ],
                          Semantic_ir.Apply
                            ( comparator.semantic_expr,
                              [
                                Semantic_ir.Apply
                                  ( fn.semantic_expr,
                                    [ Semantic_ir.Ident left ] );
                                Semantic_ir.Apply
                                  ( fn.semantic_expr,
                                    [ Semantic_ir.Ident right ] );
                              ] ) );
                      list_expr;
                    ]))
        | TFn ([ param_ty ], _), _ when not (Types.equal param_ty inner) ->
            Error.error "sort-by key function must match collection elements"
        | TFn _, TFn _ ->
            Error.error
              "sort-by comparator must accept two keys and return int"
        | _, TFn _ -> Error.error "sort-by expects a key function"
        | _, _ -> Error.error "sort-by expects key and comparator functions"
      in
      match arg_forms with
      | [ fn_form; collection_form ] -> (
          match
            ( compile_function_arg scope env fn_form,
              compile_expr scope env collection_form )
          with
          | (Error _ as err), _ -> err
          | _, (Error _ as err) -> err
          | Ok fn, Ok collection -> (
                  match collection_to_list_expr env collection with
                  | Error _ -> Error.error "sort-by expects a collection"
                  | Ok (inner, list_expr) ->
                      Result.bind (adapt_unary_function env inner fn) (fun fn ->
                      sort_default fn inner list_expr)))
      | [ fn_form; comparator_form; collection_form ] -> (
          match
            ( compile_function_arg scope env fn_form,
              compile_function_arg scope env comparator_form,
              compile_expr scope env collection_form )
          with
          | (Error _ as error), _, _ | _, (Error _ as error), _
          | _, _, (Error _ as error) -> error
          | Ok fn, Ok comparator, Ok collection -> (
              match collection_to_list_expr env collection with
              | Error _ -> Error.error "sort-by expects a collection"
              | Ok (inner, list_expr) ->
                  Result.bind (adapt_unary_function env inner fn) (fun fn ->
                      sort_with_comparator fn comparator inner list_expr)))
      | _ ->
          Error.error
            "sort-by expects a key function, optional comparator, and collection"
    and compile_mapcat scope env arg_forms =
      match arg_forms with
    | [ fn_form; collection_form ] -> (
          match
            compile_expr scope (Env.with_expected_type None env)
              collection_form
          with
          | Error _ as error -> error
          | Ok collection -> (
              match Collection_capability.to_seq_expr env collection with
              | Error _ ->
                  Error.error
                    ("mapcat expects a collection, got "
                   ^ Types.source_name collection.ty)
              | Ok (inner, sequence) -> (
                  match
                    compile_function_arg_for_collection scope env inner fn_form
                  with
                  | Error _ as error -> error
                  | Ok ({ ty = TFn ([ param_ty ], return_ty); _ } as fn)
                  when Types.assignable ~policy:Host_boundary ~expected:param_ty
                         ~actual:inner -> (
                      let item_name = "__lg_mapcat_item" in
                      let result =
                        typed_ir return_ty
                          (Semantic_ir.Apply
                             (fn.semantic_expr, [ Semantic_ir.Ident item_name ]))
                      in
                    match Collection_capability.to_seq_expr env result with
                      | Error _ ->
                          Error.error
                            ("mapcat function must return a collection, got "
                           ^ Types.source_name return_ty)
                      | Ok (result_inner, result_sequence) ->
                          Ok
                            (typed_ir (TSeq result_inner)
                               (apply "Lg_runtime.Runtime_seq.flat_map"
                                [
                                  Semantic_ir.Fun
                                      ( [ Semantic_ir.PVar item_name ],
                                        result_sequence );
                                    sequence;
                                  ])))
                  | Ok { ty = TFn _; _ } ->
                      Error.error
                        "mapcat function argument type does not match collection"
                  | Ok _ -> Error.error "mapcat expects a function")))
      | fn_form :: (_ :: _ as collection_forms) ->
          let rec compile_collections compiled = function
            | [] -> Ok (List.rev compiled)
            | form :: rest -> (
                match
                  compile_expr scope (Env.with_expected_type None env) form
                with
                | Error _ as error -> error
                | Ok collection -> (
                    match Collection_capability.to_seq_expr env collection with
                    | Error _ ->
                        Error.error
                          ("mapcat expects seqable collections, got "
                         ^ Types.source_name collection.ty)
                    | Ok (element_ty, sequence) ->
                        compile_collections
                          ((element_ty, sequence) :: compiled)
                          rest))
          in
          (match compile_collections [] collection_forms with
          | Error _ as error -> error
          | Ok collections -> (
              let element_tys = List.map fst collections in
              let sequences = List.map snd collections in
              match
                compile_function_arg_for_collections scope env element_tys
                  fn_form
              with
              | Error _ as error -> error
              | Ok fn -> (
                  match fn.ty with
                  | TFn (parameter_tys, return_ty)
                    when List.length parameter_tys = List.length element_tys
                    ->
                      let argument_names =
                        List.mapi
                          (fun index _ ->
                            "__lg_mapcat_argument_" ^ string_of_int index)
                          element_tys
                      in
                      let rec prepare_arguments prepared parameter_tys
                          element_tys names =
                        match (parameter_tys, element_tys, names) with
                        | [], [], [] -> Ok (List.rev prepared)
                        | ( expected :: parameter_tys,
                            actual :: element_tys,
                            name :: names ) ->
                            let argument =
                              typed_ir actual (Semantic_ir.Ident name)
                            in
                            let prepared_argument =
                              if Types.is_dynamic expected then
                                pack_dynamic_value env expected argument
                              else if
                                Types.assignable ~policy:Host_boundary
                                  ~expected ~actual
                                || Types.equal expected TUnknown
                                ||
                                match expected with
                                | TVar _ -> true
                                | _ -> false
                              then Ok argument.semantic_expr
                              else
                                Error.error
                                  "mapcat function type does not match \
                                   collections"
                            in
                            Result.bind prepared_argument (fun argument ->
                                prepare_arguments (argument :: prepared)
                                  parameter_tys element_tys names)
                        | _ ->
                            Error.error
                              "internal multi-collection mapcat arity \
                               mismatch"
                      in
                      Result.bind
                        (prepare_arguments [] parameter_tys element_tys
                           argument_names)
                        (fun arguments ->
                          let function_name = "__lg_mapcat_function" in
                          let sequence_names =
                            List.mapi
                              (fun index _ ->
                                "__lg_mapcat_sequence_" ^ string_of_int index)
                              sequences
                          in
                          let bound_sequences =
                            List.map
                              (fun name -> Semantic_ir.Ident name)
                              sequence_names
                          in
                          let zipped, pattern =
                            match (bound_sequences, argument_names) with
                            | ( first_sequence :: rest_sequences,
                                first_name :: rest_names ) ->
                                List.fold_left2
                                  (fun (zipped, pattern) sequence name ->
                                    let left_name = "__lg_mapcat_left" in
                                    let right_name = "__lg_mapcat_right" in
                                    ( apply "Lg_runtime.Runtime_seq.map2"
                                        [
                                          Semantic_ir.Fun
                                            ( [
                                                Semantic_ir.PVar left_name;
                                                Semantic_ir.PVar right_name;
                                              ],
                                              Semantic_ir.Tuple
                                                [
                                                  Semantic_ir.Ident
                                                    left_name;
                                                  Semantic_ir.Ident
                                                    right_name;
                                                ] );
                                          zipped;
                                          sequence;
                                        ],
                                      Semantic_ir.PTuple
                                        [ pattern; Semantic_ir.PVar name ] ))
                                  ( first_sequence,
                                    Semantic_ir.PVar first_name )
                                  rest_sequences rest_names
                            | _ -> assert false
                          in
                          let result =
                            typed_ir return_ty
                              (Semantic_ir.Apply
                                 ( Semantic_ir.Ident function_name,
                                   arguments ))
                          in
                          match
                            Collection_capability.to_seq_expr env result
                          with
                          | Error _ ->
                              Error.error
                                ("mapcat function must return a collection, \
                                  got "
                                ^ Types.source_name return_ty)
                          | Ok (result_inner, result_sequence) ->
                              let flat_mapped =
                                apply "Lg_runtime.Runtime_seq.flat_map"
                                  [
                                    Semantic_ir.Fun
                                      ( [ pattern ],
                                        result_sequence );
                                    zipped;
                                  ]
                              in
                              let result =
                                List.fold_right2
                                  (fun name sequence body ->
                                    Semantic_ir.Let
                                      ( [ ( Semantic_ir.PVar name,
                                            sequence ) ],
                                        body ))
                                  sequence_names sequences flat_mapped
                              in
                              Ok
                                (typed_ir (TSeq result_inner)
                                   (Semantic_ir.Let
                                      ( [
                                          ( Semantic_ir.PVar function_name,
                                            fn.semantic_expr );
                                        ],
                                        result ))))
                  | TFn _ ->
                      Error.error
                        "mapcat function arity does not match collections"
                  | _ -> Error.error "mapcat expects a function")))
      | _ -> Error.error "mapcat expects function and collection"
    and compile_repeatedly scope env arg_forms =
      match arg_forms with
    | [ count_form; fn_form ] -> (
        match
          ( compile_expr scope env count_form,
            compile_function_arg scope env fn_form )
        with
          | (Error _ as err), _ -> err
          | _, (Error _ as err) -> err
          | Ok count, Ok fn -> (
            if not (Types.equal count.ty TInt) then
              Error.error "repeatedly count must be int"
              else
                match fn.ty with
                | TFn ([], ret) ->
                    let body =
                      Semantic_ir.If
                      ( Semantic_ir.Infix
                          ("<=", Semantic_ir.Ident "n", Semantic_ir.Int 0),
                          Semantic_ir.Ident "acc",
                          apply "repeatedly"
                          [
                            Semantic_ir.Cons
                                ( Semantic_ir.Apply (fn.semantic_expr, []),
                                  Semantic_ir.Ident "acc" );
                            Semantic_ir.Infix
                              ("-", Semantic_ir.Ident "n", Semantic_ir.Int 1);
                          ] )
                    in
                    Ok
                      (typed_ir (TList ret)
                         (Semantic_ir.LetRec
                            ( "repeatedly",
                              [ Semantic_ir.PVar "acc"; Semantic_ir.PVar "n" ],
                              body,
                              [ Semantic_ir.List []; count.semantic_expr ] )))
              | TFn _ ->
                  Error.error "repeatedly expects a zero-argument function"
                | _ -> Error.error "repeatedly expects a function"))
      | _ -> Error.error "repeatedly expects count and function"
    and compile_reductions scope env arg_forms =
      match arg_forms with
    | [ fn_form; collection_form ] -> (
        match
          ( compile_function_arg scope env fn_form,
            compile_expr scope env collection_form )
        with
          | (Error _ as err), _ -> err
          | _, (Error _ as err) -> err
          | Ok fn, Ok collection -> (
            match (fn.ty, collection_to_list_expr env collection) with
              | TFn ([ acc_ty; item_ty ], ret), Ok (inner, list_expr)
              when Types.equal acc_ty inner && Types.equal item_ty inner
                   && Types.equal ret inner ->
                  let reductions_body =
                    Semantic_ir.Match
                      ( Semantic_ir.Ident "xs",
                      [
                        ( Semantic_ir.PList [],
                          apply "List.rev" [ Semantic_ir.Ident "acc" ] );
                        ( Semantic_ir.PCons
                            (Semantic_ir.PVar "item", Semantic_ir.PVar "tail"),
                            Semantic_ir.Let
                            ( [
                                ( Semantic_ir.PVar "next",
                                    Semantic_ir.Apply
                                      ( fn.semantic_expr,
                                      [
                                        Semantic_ir.Ident "current";
                                        Semantic_ir.Ident "item";
                                      ] ) );
                              ],
                                apply "reductions"
                                [
                                  Semantic_ir.Ident "next";
                                    Semantic_ir.Cons
                                    ( Semantic_ir.Ident "next",
                                      Semantic_ir.Ident "acc" );
                                  Semantic_ir.Ident "tail";
                                ] ) );
                      ] )
                  in
                  Ok
                    (typed_ir (TList inner)
                       (Semantic_ir.Match
                          ( list_expr,
                          [
                            (Semantic_ir.PList [], Semantic_ir.List []);
                            ( Semantic_ir.PCons
                                ( Semantic_ir.PVar "first",
                                  Semantic_ir.PVar "rest" ),
                                Semantic_ir.LetRec
                                  ( "reductions",
                                  [
                                    Semantic_ir.PVar "current";
                                      Semantic_ir.PVar "acc";
                                    Semantic_ir.PVar "xs";
                                  ],
                                    reductions_body,
                                  [
                                    Semantic_ir.Ident "first";
                                    Semantic_ir.List
                                      [ Semantic_ir.Ident "first" ];
                                    Semantic_ir.Ident "rest";
                                  ] ) );
                          ] )))
            | TFn _, Ok _ ->
                Error.error "reductions function type does not match collection"
              | _, Ok _ -> Error.error "reductions expects a function"
              | _, Error _ -> Error.error "reductions expects a collection"))
    | [ fn_form; init_form; collection_form ] -> (
          match
            ( compile_function_arg scope env fn_form,
              compile_expr scope env init_form,
              compile_expr scope env collection_form )
          with
          | (Error _ as err), _, _ -> err
          | _, (Error _ as err), _ -> err
          | _, _, (Error _ as err) -> err
          | Ok fn, Ok init, Ok collection -> (
            match (fn.ty, collection_to_list_expr env collection) with
              | TFn ([ acc_ty; item_ty ], ret), Ok (inner, list_expr)
              when Types.equal acc_ty init.ty && Types.equal item_ty inner
                   && Types.equal ret init.ty ->
                  let reductions_body =
                    Semantic_ir.Match
                      ( Semantic_ir.Ident "xs",
                      [
                        ( Semantic_ir.PList [],
                          apply "List.rev" [ Semantic_ir.Ident "acc" ] );
                        ( Semantic_ir.PCons
                            (Semantic_ir.PVar "item", Semantic_ir.PVar "rest"),
                            Semantic_ir.Let
                            ( [
                                ( Semantic_ir.PVar "next",
                                    Semantic_ir.Apply
                                      ( fn.semantic_expr,
                                      [
                                        Semantic_ir.Ident "current";
                                        Semantic_ir.Ident "item";
                                      ] ) );
                              ],
                                apply "reductions"
                                [
                                  Semantic_ir.Ident "next";
                                    Semantic_ir.Cons
                                    ( Semantic_ir.Ident "next",
                                      Semantic_ir.Ident "acc" );
                                  Semantic_ir.Ident "rest";
                                ] ) );
                      ] )
                  in
                  Ok
                    (typed_ir (TList init.ty)
                       (Semantic_ir.LetRec
                          ( "reductions",
                          [
                            Semantic_ir.PVar "current";
                              Semantic_ir.PVar "acc";
                            Semantic_ir.PVar "xs";
                          ],
                            reductions_body,
                          [
                            init.semantic_expr;
                              Semantic_ir.List [ init.semantic_expr ];
                            list_expr;
                          ] )))
            | TFn _, Ok _ ->
                Error.error
                  "reductions function type does not match init and collection"
              | _, Ok _ -> Error.error "reductions expects a function"
              | _, Error _ -> Error.error "reductions expects a collection"))
    | _ ->
        Error.error "reductions expects function, optional init, and collection"
    and compile_map_indexed scope env arg_forms =
      match arg_forms with
    | [ fn_form; collection_form ] -> (
        match compile_expr scope env collection_form with
        | Error _ as error -> error
        | Ok collection -> (
            match Collection_capability.to_seq_expr env collection with
            | Error _ -> Error.error "map-indexed expects a collection"
            | Ok (inner, sequence) -> (
                match compile_function_arg scope env fn_form with
                | Error _ as error -> error
                | Ok { ty = TFn ([ TInt; item_ty ], ret); semantic_expr; _ }
                  when Types.assignable ~policy:Host_boundary ~expected:item_ty
                         ~actual:inner ->
                    Ok
                      (typed_ir (TSeq ret)
                         (apply "Lg_runtime.Runtime_seq.mapi"
                            [ Semantic_ir.Fun
                                ( [ Semantic_ir.PVar "index";
                                    Semantic_ir.PVar "item";
                                  ],
                                  Semantic_ir.Apply
                                    ( semantic_expr,
                                      [ Semantic_ir.Ident "index";
                                        Semantic_ir.Ident "item";
                                      ] ) );
                              sequence;
                            ]))
                | Ok { ty = TFn _; _ } ->
                    Error.error
                      "map-indexed function type does not match collection"
                | Ok _ -> Error.error "map-indexed expects a function")))
      | _ -> Error.error "map-indexed expects function and collection"
  and compile_multi_map scope env ~vector fn_form collection_forms =
    let rec compile_collections compiled = function
      | [] -> Ok (List.rev compiled)
      | form :: rest -> (
          match compile_expr scope (Env.with_expected_type None env) form with
          | Error _ as error -> error
          | Ok collection -> (
              match Collection_capability.to_seq_expr env collection with
              | Error _ ->
                  Error.error
                    ((if vector then "mapv" else "map")
                    ^ " expects seqable collections, got "
                    ^ Types.source_name collection.ty)
              | Ok (element_ty, sequence) ->
                  compile_collections ((element_ty, sequence) :: compiled) rest)
          )
    in
    match compile_collections [] collection_forms with
    | Error _ as error -> error
    | Ok collections -> (
        let element_tys = List.map fst collections in
        let sequences = List.map snd collections in
        match
          compile_function_arg_for_collections scope env element_tys fn_form
        with
        | Error _ as error -> error
        | Ok fn -> (
            match fn.ty with
            | TFn (parameter_tys, return_ty)
              when List.length parameter_tys = List.length element_tys ->
                let argument_names =
                  List.mapi
                    (fun index _ -> "__lg_map_argument_" ^ string_of_int index)
                    element_tys
                in
                let rec prepare_arguments prepared parameter_tys element_tys
                    names =
                  match (parameter_tys, element_tys, names) with
                  | [], [], [] -> Ok (List.rev prepared)
                  | ( expected :: parameter_tys,
                      actual :: element_tys,
                      name :: names ) ->
                      let argument = typed_ir actual (Semantic_ir.Ident name) in
                      let prepared_argument =
                        if Types.is_dynamic expected then
                          pack_dynamic_value env expected argument
                        else if
                          Types.assignable ~policy:Host_boundary ~expected
                            ~actual
                          || Types.equal expected TUnknown
                          || match expected with TVar _ -> true | _ -> false
                        then Ok argument.semantic_expr
                        else
                          Error.error
                            ((if vector then "mapv" else "map")
                            ^ " function type does not match collections")
                      in
                      Result.bind prepared_argument (fun argument ->
                          prepare_arguments (argument :: prepared) parameter_tys
                            element_tys names)
                  | _ ->
                      Error.error "internal multi-collection map arity mismatch"
                in
                Result.map
                  (fun arguments ->
                    let function_name = "__lg_map_function" in
                    let sequence_names =
                      List.mapi
                        (fun index _ ->
                          "__lg_map_sequence_" ^ string_of_int index)
                        sequences
                    in
                    let bound_sequences =
                      List.map
                        (fun name -> Semantic_ir.Ident name)
                        sequence_names
                    in
                    let zipped, pattern =
                      match (bound_sequences, argument_names) with
                      | ( first_sequence :: rest_sequences,
                          first_name :: rest_names ) ->
                          List.fold_left2
                            (fun (zipped, pattern) sequence name ->
                              let left_name = "__lg_map_left" in
                              let right_name = "__lg_map_right" in
                              ( apply "Lg_runtime.Runtime_seq.map2"
                                  [
                                    Semantic_ir.Fun
                                      ( [
                                          Semantic_ir.PVar left_name;
                                          Semantic_ir.PVar right_name;
                                        ],
                                        Semantic_ir.Tuple
                                          [
                                            Semantic_ir.Ident left_name;
                                            Semantic_ir.Ident right_name;
                                          ] );
                                    zipped;
                                    sequence;
                                  ],
                                Semantic_ir.PTuple
                                  [ pattern; Semantic_ir.PVar name ] ))
                            (first_sequence, Semantic_ir.PVar first_name)
                            rest_sequences rest_names
                      | _ -> assert false
                    in
                    let mapped =
                      apply "Lg_runtime.Runtime_seq.map"
                        [
                          Semantic_ir.Fun
                            ( [ pattern ],
                              Semantic_ir.Apply
                                (Semantic_ir.Ident function_name, arguments) );
                          zipped;
                        ]
                    in
                    let result_ty, result =
                      if vector then
                        ( TVector return_ty,
                          apply "Rrbvec.of_list"
                            [ apply "List.of_seq" [ mapped ] ] )
                      else (TSeq return_ty, mapped)
                    in
                    let result =
                      List.fold_right2
                        (fun name sequence body ->
                          Semantic_ir.Let
                            ([ (Semantic_ir.PVar name, sequence) ], body))
                        sequence_names sequences result
                    in
                    typed_ir result_ty
                      (Semantic_ir.Let
                         ( [
                             ( Semantic_ir.PVar function_name,
                               fn.semantic_expr );
                           ],
                           result )))
                  (prepare_arguments [] parameter_tys element_tys argument_names)
            | TFn _ ->
                Error.error
                  ((if vector then "mapv" else "map")
                  ^ " function arity does not match collections")
            | _ ->
                Error.error
                  ((if vector then "mapv" else "map") ^ " expects a function")))
    and compile_mapv scope env arg_forms =
      match arg_forms with
    | [ fn_form; collection_form ] -> (
          match
            compile_expr scope (Env.with_expected_type None env) collection_form
          with
          | Error _ as error -> error
          | Ok collection -> (
              match Collection_capability.to_seq_expr env collection with
              | Error _ -> Error.error "mapv expects a collection"
              | Ok (inner, sequence) -> (
                  match
                    compile_function_arg_for_collection scope env inner fn_form
                  with
                  | Error _ as error -> error
                  | Ok fn ->
                      Result.bind (adapt_unary_function env inner fn) (fun fn ->
                          match fn.ty with
                          | TFn ([ param_ty ], ret)
                            when Types.assignable ~policy:Host_boundary
                                   ~expected:param_ty ~actual:inner ->
                              let mapped =
                                match collection.ty with
                                | TVector _ ->
                                    apply "Rrbvec.map"
                                      [ fn.semantic_expr; collection.semantic_expr ]
                                | _ ->
                                    apply "Rrbvec.of_list"
                                      [
                                        apply "List.of_seq"
                                          [
                                            apply "Lg_runtime.Runtime_seq.map"
                                              [ fn.semantic_expr; sequence ];
                                          ];
                                      ]
                              in
                              Ok
                                (typed_ir (TVector ret) mapped)
                          | TFn _ ->
                              Error.error
                                ("mapv function type " ^ Types.source_name fn.ty
                                 ^ " does not match collection element " ^ Types.source_name inner)
                          | _ -> Error.error "mapv expects a function"))))
    | fn_form :: (_ :: _ as collection_forms) ->
        compile_multi_map scope env ~vector:true fn_form collection_forms
      | _ -> Error.error "mapv expects function and collection"
    and compile_reduce_kv scope env arg_forms =
      match arg_forms with
    | [ fn_form; init_form; collection_form ] -> (
          incr reduce_kv_counter;
          let suffix = string_of_int !reduce_kv_counter in
          let accumulator_name = "__lg_reduce_kv_accumulator_" ^ suffix in
          let key_name = "__lg_reduce_kv_key_" ^ suffix in
          let value_name = "__lg_reduce_kv_value_" ^ suffix in
          let index_name = "__lg_reduce_kv_index_" ^ suffix in
          match
            ( compile_expr scope env init_form,
              compile_expr scope env collection_form )
          with
          | (Error _ as error), _ -> error
          | _, (Error _ as error) -> error
        | Ok init, Ok collection -> (
              let compile_for fold key_ty value_ty entries =
                match
                  compile_kv_reducer scope env init.ty key_ty value_ty fn_form
                with
                | Error _ as error -> error
                | Ok fn -> (
                    match fn.ty with
                    | TFn ([ accumulator_ty; actual_key; actual_value ], result)
                      when Types.assignable ~policy:Host_boundary
                             ~expected:accumulator_ty ~actual:init.ty
                           && Types.assignable ~policy:Host_boundary
                                ~expected:actual_key ~actual:key_ty
                           && Types.assignable ~policy:Host_boundary
                                ~expected:actual_value ~actual:value_ty
                           && Types.assignable ~policy:Host_boundary
                                ~expected:init.ty ~actual:result ->
                        let result_ty =
                          match (init.ty, result) with
                          | TVector (TUnknown | TMeta _ | TVar _), TVector _ -> result
                          | _ -> init.ty
                        in
                        Ok
                          (typed_ir result_ty
                             (apply fold
                              [
                                Semantic_ir.Fun
                                  ( [
                                      Semantic_ir.PVar accumulator_name;
                                        Semantic_ir.PTuple
                                        [
                                          Semantic_ir.PVar key_name;
                                          Semantic_ir.PVar value_name;
                                        ];
                                    ],
                                      Semantic_ir.Apply
                                        ( fn.semantic_expr,
                                        [
                                          Semantic_ir.Ident accumulator_name;
                                            Semantic_ir.Ident key_name;
                                          Semantic_ir.Ident value_name;
                                        ] ) );
                                  init.semantic_expr;
                                entries;
                              ]))
                    | TFn _ ->
                        Error.error
                          "reduce-kv function type does not match collection"
                    | _ -> Error.error "reduce-kv expects a function")
              in
            match collection.ty with
              | TVector value_ty ->
                  let entries =
                    apply "List.mapi"
                    [
                      Semantic_ir.Fun
                        ( [
                            Semantic_ir.PVar index_name;
                            Semantic_ir.PVar value_name;
                          ],
                            Semantic_ir.Tuple
                            [
                              Semantic_ir.Ident index_name;
                              Semantic_ir.Ident value_name;
                            ] );
                      apply "Rrbvec.to_list" [ collection.semantic_expr ];
                    ]
                  in
                  compile_for "List.fold_left" TInt value_ty entries
              | TRecord fields -> (
                  match Types.homogeneous_record_value_type fields with
                  | Some value_ty ->
                      compile_for "Lg_runtime.Runtime_map.fold_left" TKeyword
                        value_ty collection.semantic_expr
                  | None ->
                      Error.error
                        "reduce-kv requires map values with one static type")
              | map_type -> (
                  match Types.dynamic_map_types map_type with
                  | Some (key_ty, value_ty) ->
                      compile_for "Lg_runtime.Runtime_map.fold_left" key_ty
                        value_ty collection.semantic_expr
                | None when Types.is_dynamic map_type ->
                    let dynamic = Types.dynamic_constraint TUnknown in
                    compile_for "List.fold_left" dynamic dynamic
                      (apply "Lg_runtime.Runtime_dynamic.entries"
                         [ collection.semantic_expr ])
                | None -> Error.error "reduce-kv expects a vector or map")))
      | _ -> Error.error "reduce-kv expects function, init, and vector"
    and compile_some scope env arg_forms =
      match arg_forms with
    | [ fn_form; collection_form ] -> (
        match compile_expr scope env collection_form with
        | Error _ as err -> err
        | Ok collection -> (
            match collection_to_list_expr env collection with
            | Error _ -> Error.error "some expects a collection"
            | Ok (inner, list_expr) -> (
                match
                  compile_function_arg_for_collection scope env inner fn_form
                with
                | Error _ as err -> err
                | Ok fn ->
                    Result.bind (adapt_unary_function env inner fn) (fun fn ->
                    match fn.ty with
                    | TFn ([ param_ty ], return_ty)
              when Types.assignable ~policy:Host_boundary ~expected:param_ty
                     ~actual:inner ->
                let item = typed_ir inner (Semantic_ir.Ident "item") in
                let item_argument =
                  if Types.is_dynamic param_ty then
                    pack_dynamic_value env param_ty item
                  else Ok item.semantic_expr
                in
                Result.map
                  (fun item_argument ->
                  let value_ty = Types.constraint_value_type return_ty in
                  let result_value =
                    coerce_expression_to_type
                      ~stored:(not (Types.equal value_ty return_ty)) value_ty
                      return_ty (Semantic_ir.Ident "result")
                  in
                  let result_ty, present_result =
                    match value_ty with
                    | TNullable _
                    | TOcaml_app ("option", [ _ ])
                    | TOcaml "option" ->
                        (value_ty, result_value)
                    | _ ->
                        ( TNullable value_ty,
                          Semantic_ir.Constructor
                            ("Some", Some result_value) )
                  in
                  let recurse =
                    apply "find_truthy" [ Semantic_ir.Ident "rest" ]
                  in
                  let body =
                    Semantic_ir.Match
                      ( Semantic_ir.Ident "values",
                          [
                            ( Semantic_ir.PList [],
                            Semantic_ir.Constructor ("None", None) );
                          ( Semantic_ir.PCons
                                ( Semantic_ir.PVar "item",
                                  Semantic_ir.PVar "rest" ),
                            Semantic_ir.Let
                                ( [
                                    ( Semantic_ir.PVar "result",
                                    Semantic_ir.Apply
                                        (fn.semantic_expr, [ item_argument ]) );
                                  ],
                                Semantic_ir.If
                                  ( truthiness_expression ~env
                                      ~constrained_identifier:false return_ty
                                      (Semantic_ir.Ident "result"),
                                    present_result,
                                    recurse ) ) );
                        ] )
                  in
                    typed_ir result_ty
                       (Semantic_ir.LetRecIn
                          ( "find_truthy",
                            [ Semantic_ir.PVar "values" ],
                            body,
                            Semantic_ir.Apply
                              (Semantic_ir.Ident "find_truthy", [ list_expr ]) )))
                  item_argument
                    | TFn _ ->
                        Error.error
                          "some function type must match collection elements"
                    | _ -> Error.error "some expects a function"))))
      | _ -> Error.error "some expects function and collection"
    and compile_map_call scope env arg_forms =
      match arg_forms with
    | [ fn_form; collection_form ] -> (
          match compile_expr scope env collection_form with
          | Error _ as err -> err
          | Ok collection -> (
              match Collection_capability.to_seq_expr env collection with
              | Error _ ->
                  Error.error
                    ("map expects a seqable value, got "
                    ^ Types.source_name collection.ty)
              | Ok (inner, sequence) -> (
                  let expected_return_ty =
                    match Env.expected_type env with
                    | Some expected -> (
                        match
                          match expected with
                          | TSeq element | TList element | TVector element ->
                              Some element
                          | _ -> Types.seqable_constraint_element expected
                        with
                        | Some element
                          when not
                                 (match element with
                                 | TUnknown | TMeta _ | TVar _ -> true
                                 | _ -> false) ->
                            Some element
                        | Some _ | None -> None)
                    | None -> None
                  in
                  match
                    compile_function_arg_for_collection scope env
                      ?expected_return_ty inner fn_form
                  with
                  | Error _ as err -> err
                  | Ok ({ ty = TFn ([ param_ty ], ret); _ } as fn)
                    when Types.assignable ~policy:Host_boundary ~expected:param_ty
                           ~actual:inner ->
                      Result.map
                        (fun fn ->
                          typed_ir (TSeq ret)
                            (apply "Lg_runtime.Runtime_seq.map"
                               [ fn.semantic_expr; sequence ]))
                        (adapt_unary_function env inner fn)
                  | Ok { ty = TFn _; _ } ->
                    Error.error
                      "map function argument type does not match sequence"
                  | Ok fn when Types.is_dynamic fn.ty ->
                      Error.error
                        "map requires a statically typed function; define a \
                         typed wrapper or closed sum type"
                  | Ok fn ->
                      Error.error
                        ("map expects a function, got "
                        ^ Types.source_name fn.ty))))
    | fn_form :: (_ :: _ as collection_forms) ->
        compile_multi_map scope env ~vector:false fn_form collection_forms
      | _ -> Error.error "map expects function and collection"
    and compile_filter scope env arg_forms =
      match arg_forms with
    | [ fn_form; collection_form ] -> (
          match compile_expr scope env collection_form with
          | Error _ as err -> err
          | Ok collection -> (
              match Collection_capability.to_seq_expr env collection with
              | Error _ -> Error.error "filter expects a seqable value"
              | Ok (inner, sequence) -> (
                  match
                    compile_function_arg_for_collection scope env inner fn_form
                  with
                  | Error _ as err -> err
                  | Ok fn -> (
                      match fn.ty with
                      | TFn ([ param_ty ], return_ty)
                        when Types.assignable ~policy:Host_boundary
                               ~expected:param_ty ~actual:inner ->
                          Result.map
                            (fun fn ->
                              let predicate =
                                if Types.equal return_ty TBool then
                                  fn.semantic_expr
                                else
                                  let item_name = "__lg_filter_item" in
                                  Semantic_ir.Fun
                                    ( [ Semantic_ir.PVar item_name ],
                                      truthiness_expression ~env return_ty
                                        (Semantic_ir.Apply
                                           ( fn.semantic_expr,
                                             [
                                               Semantic_ir.Ident item_name;
                                             ] )) )
                              in
                              typed_ir (TSeq inner)
                                (apply "Lg_runtime.Runtime_seq.filter"
                                   [ predicate; sequence ]))
                            (adapt_unary_function env inner fn)
                    | ty when Types.is_dynamic ty ->
                        Error.error
                          "filter requires a statically typed predicate; define \
                           a typed wrapper or closed sum type"
                      | TFn _ ->
                          Error.error
                          "filter expects a predicate matching sequence \
                           elements"
                      | _ -> Error.error "filter expects a function"))))
      | _ -> Error.error "filter expects function and collection"
    and compile_keep scope env arg_forms =
      match arg_forms with
      | [ fn_form; collection_form ] -> (
          match compile_expr scope env collection_form with
          | Error _ as error -> error
          | Ok collection -> (
              match Collection_capability.to_seq_expr env collection with
              | Error _ -> Error.error "keep expects a Seqable value"
              | Ok (inner, sequence) -> (
                  match
                    compile_function_arg_for_collection scope env inner fn_form
                  with
                  | Error _ as error -> error
                  | Ok ({ ty = TFn ([ parameter_ty ], return_ty); _ } as fn)
                    when Types.assignable ~policy:Host_boundary
                           ~expected:parameter_ty ~actual:inner ->
                      Result.map
                        (fun fn ->
                          match return_ty with
                          | TNullable result_ty
                          | TOcaml_app ("option", [ result_ty ]) ->
                              typed_ir (TSeq result_ty)
                                (apply "Lg_runtime.Runtime_seq.filter_map"
                                   [ fn.semantic_expr; sequence ])
                          | TNil ->
                              typed_ir (TSeq TUnknown)
                                (apply "Lg_runtime.Runtime_seq.filter_map"
                                   [ fn.semantic_expr; sequence ])
                          | return_ty when Types.is_dynamic return_ty ->
                              let item_name = "__lg_keep_item" in
                              let result_name = "__lg_keep_result" in
                              typed_ir (TSeq return_ty)
                                (apply "Lg_runtime.Runtime_seq.filter_map"
                                   [
                                     Semantic_ir.Fun
                                       ( [ Semantic_ir.PVar item_name ],
                                         Semantic_ir.Let
                                           ( [
                                               ( Semantic_ir.PVar result_name,
                                                 Semantic_ir.Apply
                                                   ( fn.semantic_expr,
                                                     [
                                                       Semantic_ir.Ident
                                                         item_name;
                                                     ] ) );
                                             ],
                                             Semantic_ir.If
                                               ( apply
                                                   "Lg_runtime.Runtime_dynamic.is_nil"
                                                   [
                                                     Semantic_ir.Ident
                                                       result_name;
                                                   ],
                                                 Semantic_ir.Constructor
                                                   ("None", None),
                                                 Semantic_ir.Constructor
                                                   ( "Some",
                                                     Some
                                                       (Semantic_ir.Ident
                                                          result_name) ) ) ) );
                                     sequence;
                                   ])
                          | result_ty ->
                              typed_ir (TSeq result_ty)
                                (apply "Lg_runtime.Runtime_seq.map"
                                   [ fn.semantic_expr; sequence ]))
                        (adapt_unary_function env inner fn)
                  | Ok { ty = TFn _; _ } ->
                      Error.error
                        "keep function argument type does not match sequence"
                  | Ok _ -> Error.error "keep expects a function")))
      | _ -> Error.error "keep expects function and collection"
    and compile_reduce scope env arg_forms =
      let compile_initial ?expected_type fn_form init_form =
        let env =
          match expected_type with
          | None -> env
          | Some ty -> Env.with_expected_type (Some ty) env
        in
        let fixed_tuple_arity =
          match fn_form with
          | FList
              (FSymbol "fn"
              :: FVector [ FVector pattern; _element_pattern ]
              :: _body_forms) -> (
              match Destructure.parse_sequence_pattern pattern with
              | Ok
                  {
                    item_patterns;
                    rest_name = None;
                    sequence_as_name = _;
                  } ->
                  Some (List.length item_patterns)
              | Ok _ | Error _ -> None)
          | _ -> None
        in
        match (fixed_tuple_arity, init_form) with
        | Some arity, FVector forms
          when arity > 0 && List.length forms = arity ->
            let expected_items =
              match Env.expected_type env with
              | Some (TTuple items) -> items
              | _ -> []
            in
            let rec compile index expressions types = function
              | [] ->
                  Ok
                    (typed_ir (TTuple (List.rev types))
                       (Semantic_ir.Tuple (List.rev expressions)))
              | form :: rest ->
                  Result.bind
                    (compile_expr scope
                       (Env.with_expected_type (List.nth_opt expected_items index) env) form)
                    (fun expression ->
                      compile (index + 1) (expression.semantic_expr :: expressions)
                        (expression.ty :: types) rest)
            in
            compile 0 [] [] forms
        | (Some _, _) | (None, _) -> compile_expr scope env init_form
      in
      match arg_forms with
      | [
       fn_form;
       FList [ FSymbol first_name; FSymbol source_name ];
       FList [ FSymbol next_name; FSymbol next_source ];
      ]
        when (has_source_name first_name "__lg_first"
             || has_source_name first_name "first")
             && (has_source_name next_name "__lg_next"
                || has_source_name next_name "next")
             && String.equal source_name next_source -> (
          match compile_expr scope env (FSymbol source_name) with
          | Error _ as error -> error
          | Ok collection -> (
              match Collection_capability.to_seq_expr env collection with
              | Error _ ->
                  Error.error
                    ("reduce expects a seqable value, got "
                   ^ Types.source_name collection.ty)
              | Ok (inner, sequence) ->
                  let accumulator_ty = Types.constraint_value_type inner in
                  Result.bind
                    (compile_reducer scope env accumulator_ty inner fn_form)
                    (fun fn ->
                      let reduction =
                        match fn.ty with
                        | TFn ([ acc_ty; item_ty ], return_ty)
                          when Types.assignable ~policy:Host_boundary
                                 ~expected:acc_ty ~actual:accumulator_ty
                               && Types.assignable ~policy:Host_boundary
                                    ~expected:item_ty ~actual:inner -> (
                            let first_value =
                              Collection_capability.constraint_value_expression
                                item_ty
                                (Semantic_ir.Ident "__lg_reduce_first")
                            in
                            match Types.reduced_element return_ty with
                            | None
                              when Types.assignable ~policy:Host_boundary
                                     ~expected:accumulator_ty
                                     ~actual:return_ty ->
                                Ok
                                  (apply "Lg_runtime.Runtime_seq.fold_left"
                                     [
                                       fn.semantic_expr;
                                       first_value;
                                       Semantic_ir.Ident "__lg_reduce_rest";
                                     ])
                            | Some reduced_ty
                              when Types.assignable ~policy:Host_boundary
                                     ~expected:accumulator_ty
                                     ~actual:reduced_ty ->
                                Ok
                                  (apply "Lg_runtime.Runtime_reduced.fold_seq"
                                     [
                                       fn.semantic_expr;
                                       first_value;
                                       Semantic_ir.Ident "__lg_reduce_rest";
                                     ])
                            | Some _ | None ->
                                Error.error
                                  "reduce function must preserve the first element type")
                        | TFn _ ->
                            Error.error
                              "reduce function type does not match first and next"
                        | _ -> Error.error "reduce expects a function"
                      in
                      Result.map
                        (fun reduction ->
                          typed_ir (TNullable accumulator_ty)
                            (Semantic_ir.Match
                               ( apply "Seq.uncons" [ sequence ],
                                 [
                                   ( Semantic_ir.PConstructor ("None", None),
                                     Semantic_ir.Constructor ("None", None) );
                                   ( Semantic_ir.PConstructor
                                       ( "Some",
                                         Some
                                           (Semantic_ir.PTuple
                                              [
                                                Semantic_ir.PVar
                                                  "__lg_reduce_first";
                                                Semantic_ir.PVar
                                                  "__lg_reduce_rest";
                                              ]) ),
                                     Semantic_ir.Constructor
                                       ("Some", Some reduction) );
                                 ] )))
                        reduction)))
      | [ fn_form; collection_form ] -> (
          match compile_expr scope env collection_form with
          | Error _ as error -> error
          | Ok collection -> (
              match Collection_capability.to_seq_expr env collection with
              | Error _ ->
                  Error.error
                    ("reduce expects a seqable value, got "
                   ^ Types.source_name collection.ty)
              | Ok (inner, sequence) -> (
                  let accumulator_ty =
                    let element_type_is_open =
                      Types.is_dynamic inner
                      || Types.equal inner TUnknown
                      || match inner with
                         | TMeta _ | TVar _ -> true
                         | _ -> false
                    in
                    match fn_form with
                    | FSymbol name -> (
                        match Resolver.lookup_binding scope env name with
                        | Ok { ty = TFn ([ acc_ty; _ ], _); _ }
                          when element_type_is_open
                               && not
                                    (Types.equal acc_ty
                                       (Types.constraint_value_type acc_ty)) ->
                            inner
                        | Ok { ty = TFn ([ acc_ty; _item_ty ], return_ty); _ }
                          when element_type_is_open
                               && not (Types.is_dynamic acc_ty)
                               && Types.equal acc_ty return_ty ->
                            acc_ty
                        | Ok { ty = TOverloaded_fn arities; _ }
                          when element_type_is_open -> (
                            match
                              List.find_opt
                                (fun arity ->
                                  List.length arity.fixed_params = 2)
                                arities
                            with
                            | Some { fixed_params = acc_ty :: _; _ }
                              when not
                                     (Types.equal acc_ty
                                        (Types.constraint_value_type acc_ty)) ->
                                inner
                            | Some
                                {
                                  fixed_params = acc_ty :: _;
                                  return_ty;
                                  _;
                                }
                              when not (Types.is_dynamic acc_ty)
                                   && Types.equal acc_ty return_ty ->
                                acc_ty
                            | Some _ | None -> inner)
                        | Ok _ | Error _ -> inner)
                    | _ -> inner
                  in
                  let first =
                    if
                      Types.is_dynamic inner
                      && not (Types.is_dynamic accumulator_ty)
                    then
                      dynamic_unpack env accumulator_ty
                        (Semantic_ir.Ident "__lg_reduce_first")
                    else Ok (Semantic_ir.Ident "__lg_reduce_first")
                  in
                  match
                    ( first,
                      compile_reducer scope env accumulator_ty inner fn_form )
                  with
                  | (Error _ as error), _ | _, (Error _ as error) -> error
                  | Ok first, Ok fn -> (
                      let reduction =
                        match fn.ty with
                        | TFn ([ fn_accumulator_ty; item_ty ], return_ty)
                          when Types.assignable ~policy:Host_boundary
                                 ~expected:fn_accumulator_ty
                                 ~actual:accumulator_ty
                               && Types.assignable ~policy:Host_boundary
                                    ~expected:item_ty ~actual:inner
                               && Option.is_none
                                    (Types.reduced_element return_ty)
                               && Types.assignable ~policy:Host_boundary
                                    ~expected:fn_accumulator_ty
                                    ~actual:return_ty ->
                            Ok
                              (apply "Lg_runtime.Runtime_seq.fold_left"
                                 [
                                   fn.semantic_expr;
                                   first;
                                   Semantic_ir.Ident "__lg_reduce_rest";
                                 ])
                        | TFn ([ accumulator_ty; item_ty ], return_ty)
                          when Types.assignable ~policy:Host_boundary
                                 ~expected:accumulator_ty ~actual:inner
                               && Types.assignable ~policy:Host_boundary
                                    ~expected:item_ty ~actual:inner -> (
                            match Types.reduced_element return_ty with
                            | Some reduced_ty
                              when Types.assignable ~policy:Host_boundary
                                     ~expected:inner ~actual:reduced_ty ->
                                Ok
                                  (apply "Lg_runtime.Runtime_reduced.fold_seq"
                                     [
                                       fn.semantic_expr;
                                       Semantic_ir.Ident "__lg_reduce_first";
                                       Semantic_ir.Ident "__lg_reduce_rest";
                                     ])
                            | _ ->
                                Error.error
                                  "two-arity reduce function must preserve the sequence element type")
                        | TFn _ ->
                            Error.error
                              "two-arity reduce expects a binary reducer"
                        | _ -> Error.error "reduce expects a function"
                      in
                      Result.map
                        (fun reduction ->
                          let empty_result =
                            match
                              compile_expr scope env (FList [ fn_form ])
                            with
                            | Ok result
                              when Types.assignable ~policy:Host_boundary
                                     ~expected:accumulator_ty ~actual:result.ty ->
                                result.semantic_expr
                            | Ok _ | Error _ ->
                                apply "invalid_arg"
                                  [
                                    Semantic_ir.String
                                      "reduce of empty collection with no identity";
                                  ]
                          in
                          typed_ir accumulator_ty
                            (Semantic_ir.Match
                               ( apply "Seq.uncons" [ sequence ],
                                 [
                                   ( Semantic_ir.PConstructor ("None", None),
                                     empty_result );
                                   ( Semantic_ir.PConstructor
                                       ( "Some",
                                         Some
                                           (Semantic_ir.PTuple
                                              [
                                                Semantic_ir.PVar
                                                  "__lg_reduce_first";
                                                Semantic_ir.PVar
                                                  "__lg_reduce_rest";
                                              ]) ),
                                     reduction );
                                 ] )) )
                        reduction))))
      | [ fn_form; init_form; collection_form ] -> (
        match
          ( compile_initial fn_form init_form,
            compile_expr scope env collection_form )
        with
          | (Error _ as err), _ -> err
          | _, (Error _ as err) -> err
          | Ok init, Ok collection -> (
              let reducible_input =
                match Collection_capability.to_seq_expr env collection with
                | Ok input -> Ok input
                | Error _ -> (
                    match reify_reducible_method collection with
                    | Some
                        ( TFn
                            ([ TFn ([ _accumulator; item ], _); _initial ], _),
                          _ ) ->
                        Ok (item, Semantic_ir.Ident "Seq.empty")
                    | Some _ ->
                        Error.error "Reducible reify method has an invalid type"
                    | None ->
                    match
                      Core_protocols.find_reducible collection.ty
                        (Compiler_environment.protocols env)
                    with
                    | Some
                        { ty =
                            TFn
                              ([ _receiver;
                                 TFn ([ _accumulator; item ], _reducer_result);
                                 _initial ],
                               _return);
                          _ } ->
                        Ok (item, Semantic_ir.Ident "Seq.empty")
                    | Some _ | None ->
                        Error.error
                          ("reduce expects a seqable or reducible value, got "
                          ^ Types.source_name collection.ty))
              in
              match reducible_input with
              | Error _ as error -> error
              | Ok (inner, sequence) -> (
                  match compile_reducer scope env init.ty inner fn_form with
                  | Error _ as err -> err
                  | Ok initial_fn ->
                      let refined_fn =
                        match initial_fn.ty with
                        | TFn ([ accumulator_ty; _ ], return_ty)
                          when Type_solver.is_open accumulator_ty
                               && not (Type_solver.is_open return_ty)
                               && not (Types.is_dynamic return_ty)
                               && Result.is_ok
                                    (Type_solver.unify Type_solver.empty accumulator_ty return_ty) ->
                            compile_reducer scope env return_ty inner fn_form
                        | TFn ([ accumulator_ty; _ ], return_ty)
                          when (Types.is_dynamic return_ty
                               ||
                               match Types.reduced_element return_ty with
                               | Some reduced_ty -> Types.is_dynamic reduced_ty
                               | None -> false)
                               && not (Types.is_dynamic accumulator_ty) ->
                            let accumulator_ty =
                              match Types.reduced_element return_ty with
                              | Some reduced_ty when Types.is_dynamic reduced_ty ->
                                  reduced_ty
                              | _ -> return_ty
                            in
                            compile_reducer scope env accumulator_ty inner fn_form
                        | _ -> Ok initial_fn
                      in
                      Result.bind refined_fn (fun fn ->
                      let specialize_empty_set accumulator_ty =
                        match
                          ( init.ty,
                            accumulator_ty,
                            Semantic_ir.unlocated init.semantic_expr )
                        with
                        | ( TSet (TUnknown | TMeta _ | TVar _),
                            TSet element_ty,
                            Semantic_ir.Ident
                              "Lg_runtime.Runtime_poly_set.empty" ) ->
                            Result.map
                              (fun set_module ->
                                {
                                  init with
                                  ty = accumulator_ty;
                                  semantic_expr =
                                    Semantic_ir.Ident (set_module ^ ".empty");
                                })
                              (Types.set_module_name element_ty)
                        | ( TSet (TUnknown | TMeta _ | TVar _),
                            dynamic_ty,
                            Semantic_ir.Ident
                              "Lg_runtime.Runtime_poly_set.empty" )
                          when Types.is_dynamic dynamic_ty ->
                            Ok
                              {
                                init with
                                ty = dynamic_ty;
                                semantic_expr =
                                  apply "Lg_runtime.Runtime_dynamic.set"
                                    [ Semantic_ir.Ident "Seq.empty" ];
                              }
                        | _ -> Ok init
                      in
                      let init =
                        match fn.ty with
                        | TFn (accumulator_ty :: _, _)
                          when Type_solver.is_open init.ty
                               && not (Type_solver.is_open accumulator_ty)
                               && not (Types.is_dynamic accumulator_ty) ->
                            compile_initial ~expected_type:accumulator_ty fn_form init_form
                        | TFn (accumulator_ty :: _, _) ->
                            specialize_empty_set accumulator_ty
                        | _ -> Ok init
                      in
                      let init =
                        Result.bind init (fun init ->
                            match fn.ty with
                            | TFn (accumulator_ty :: _, _)
                              when (not (Types.equal accumulator_ty init.ty))
                                   && Types.assignable ~policy:Host_boundary
                                        ~expected:
                                          (Types.constraint_value_type
                                             accumulator_ty)
                                        ~actual:init.ty ->
                                Result.map
                                  (fun semantic_expr ->
                                    { init with ty = accumulator_ty; semantic_expr })
                                  (pack_constrained_value env accumulator_ty init)
                            | _ -> Ok init)
                      in
                      let init =
                        Result.bind init (fun init ->
                            let dynamic_accumulator_ty =
                              match fn.ty with
                              | TFn (accumulator_ty :: _, _)
                                when Types.is_dynamic accumulator_ty ->
                                  Some accumulator_ty
                              | TFn (_, return_ty)
                                when Types.is_dynamic return_ty ->
                                  Some return_ty
                              | TFn (_, return_ty) -> (
                                  match Types.reduced_element return_ty with
                                  | Some reduced_ty
                                    when Types.is_dynamic reduced_ty ->
                                      Some reduced_ty
                                  | _ -> None)
                              | _ -> None
                            in
                            match dynamic_accumulator_ty with
                            | Some accumulator_ty
                              when not (Types.is_dynamic init.ty) ->
                                Result.map
                                  (fun semantic_expr ->
                                    { init with ty = accumulator_ty; semantic_expr })
                                  (pack_dynamic_value env accumulator_ty init)
                            | _ -> Ok init)
                      in
                      Result.bind init (fun init ->
                      match fn.ty with
                      | TFn ([ acc_ty; item_ty ], TNullable reduced_type)
                      when Types.equal init.ty TNil && Types.equal acc_ty TNil
                             && (Types.equal item_ty inner
                                || Types.equal inner TUnknown
                                || Types.assignable ~policy:Host_boundary
                                     ~expected:item_ty ~actual:inner) -> (
                          match Types.reduced_element reduced_type with
                          | None ->
                              Error.error
                              "nullable reduce result must contain a reduced \
                               value"
                          | Some result_type ->
                              let accumulator = Semantic_ir.Ident "accumulator" in
                              let item = Semantic_ir.Ident "item" in
                              let reduced_value = "reduced_value" in
                              let nullable_result = TNullable result_type in
                              let adapted_fn =
                                typed_ir
                                  (TFn
                                     ( [ nullable_result; item_ty ],
                                       Types.reduced nullable_result ))
                                  (Semantic_ir.Fun
                                   ( [
                                       Semantic_ir.PVar "accumulator";
                                       Semantic_ir.PVar "item";
                                     ],
                                       Semantic_ir.Match
                                         ( Semantic_ir.Apply
                                             ( fn.semantic_expr,
                                               [ accumulator; item ] ),
                                         [
                                           ( Semantic_ir.PConstructor
                                                 ("None", None),
                                               Semantic_ir.Apply
                                                 ( Semantic_ir.Ident
                                                     "Lg_runtime.Runtime_reduced.continue",
                                                 [
                                                   Semantic_ir.Constructor
                                                     ("None", None);
                                                 ] ) );
                                             ( Semantic_ir.PConstructor
                                                 ( "Some",
                                                   Some
                                                     (Semantic_ir.PVar
                                                        reduced_value) ),
                                               Semantic_ir.Apply
                                                 ( Semantic_ir.Ident
                                                     "Lg_runtime.Runtime_reduced.reduced",
                                                 [
                                                   Semantic_ir.Constructor
                                                       ( "Some",
                                                         Some
                                                           (Semantic_ir.Apply
                                                              ( Semantic_ir.Ident
                                                                  "Lg_runtime.Runtime_reduced.unreduced",
                                                              [
                                                                Semantic_ir
                                                                .Ident
                                                                  reduced_value;
                                                              ] )) );
                                                 ] ) );
                                         ] ) ))
                              in
                              Ok
                                (typed_ir nullable_result
                                   (Collection_capability.reduce_expr env
                                      ~short_circuit:true adapted_fn
                                      { init with ty = nullable_result }
                                      collection sequence)))
                      | TFn ([ acc_ty; item_ty ], ret)
                        when Types.assignable ~policy:Host_boundary
                               ~expected:acc_ty ~actual:init.ty
                             && (Types.equal item_ty inner
                                || Types.equal inner TUnknown
                                || Types.assignable ~policy:Host_boundary
                                     ~expected:item_ty ~actual:inner)
                             && Types.assignable ~policy:Host_boundary
                                  ~expected:init.ty ~actual:ret
                             && Option.is_none (Types.reduced_element ret) ->
                          Result.map
                            (typed_ir ret)
                            (reduce_expression env ~result_ty:ret fn init
                               collection sequence)
                      | TFn ([ acc_ty; item_ty ], ret)
                        when Types.assignable ~policy:Host_boundary
                               ~expected:acc_ty ~actual:init.ty
                             && (Types.equal item_ty inner
                                || Types.equal inner TUnknown
                                || Types.assignable ~policy:Host_boundary
                                     ~expected:item_ty ~actual:inner)
                           &&
                           match Types.reduced_element ret with
                                | Some (TNullable _) -> false
                                | Some reduced_ty ->
                                    Types.assignable ~policy:Host_boundary
                                      ~expected:init.ty ~actual:reduced_ty
                           | None -> false ->
                          Ok
                            (typed_ir init.ty
                               (Collection_capability.reduce_expr env
                                  ~short_circuit:true fn init collection sequence))
                      | TFn ([ acc_ty; item_ty ], ret)
                        when Types.assignable ~policy:Host_boundary
                               ~expected:acc_ty ~actual:init.ty
                             && (Types.equal item_ty inner
                                || Types.equal inner TUnknown
                                || Types.assignable ~policy:Host_boundary
                                     ~expected:item_ty ~actual:inner) -> (
                          match Types.reduced_element ret with
                          | Some (TNullable result_ty)
                            when Types.assignable ~policy:Host_boundary
                                   ~expected:init.ty ~actual:result_ty ->
                              let nullable_init = TNullable init.ty in
                              let accumulator = Semantic_ir.Ident "accumulator" in
                              let item = Semantic_ir.Ident "item" in
                              let value = Semantic_ir.Ident "value" in
                              let adapted_fn =
                                typed_ir
                                  (TFn
                                     ( [ nullable_init; item_ty ],
                                       Types.reduced nullable_init ))
                                  (Semantic_ir.Fun
                                   ( [
                                       Semantic_ir.PVar "accumulator";
                                       Semantic_ir.PVar "item";
                                     ],
                                       Semantic_ir.Match
                                         ( accumulator,
                                         [
                                           ( Semantic_ir.PConstructor
                                                 ("None", None),
                                               Semantic_ir.Apply
                                                 ( Semantic_ir.Ident
                                                     "Lg_runtime.Runtime_reduced.reduced",
                                                 [
                                                   Semantic_ir.Constructor
                                                     ("None", None);
                                                 ] ) );
                                             ( Semantic_ir.PConstructor
                                                 ( "Some",
                                                 Some (Semantic_ir.PVar "value")
                                               ),
                                               Semantic_ir.Apply
                                                 ( fn.semantic_expr,
                                                   [ value; item ] ) );
                                           ] ) ))
                              in
                              let nullable_init_expr =
                                {
                                  init with
                                  ty = nullable_init;
                                  semantic_expr =
                                    Semantic_ir.Constructor
                                      ("Some", Some init.semantic_expr);
                                }
                              in
                              Ok
                                (typed_ir nullable_init
                                   (Collection_capability.reduce_expr env
                                      ~short_circuit:true adapted_fn
                                      nullable_init_expr collection sequence))
                          | _ -> Error.error "reduced value must match init")
                      | TFn _ ->
                          Error.error
                          ("reduce function type does not match init and \
                            sequence: fn=" ^ Types.source_name fn.ty ^ ", init="
                           ^ Types.source_name init.ty ^ ", sequence="
                           ^ Types.source_name inner)
                      | _ -> Error.error "reduce expects a function")))))
      | _ -> Error.error "reduce expects function, init, and collection"
  in
  {
    compile_sort_by;
    compile_mapcat;
    compile_repeatedly;
    compile_reductions;
    compile_map_indexed;
    compile_mapv;
    compile_reduce_kv;
    compile_some;
    compile_map_call;
    compile_keep;
    compile_filter;
    compile_reduce;
  }
