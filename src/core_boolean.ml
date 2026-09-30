open Types

let one_arg name args =
  match args with
  | [ arg ] -> Ok arg
  | _ -> Error.error ~code:Error_code.Arity (name ^ " expects 1 arguments")

let evaluated_argument arg =
  Semantic_ir.evaluate_for_effect arg.semantic_expr

let type_predicate name predicate args =
  match one_arg name args with
  | Error _ as err -> err
  | Ok arg ->
      Ok
        (typed_ir TBool
           (Semantic_ir.Sequence
              [ evaluated_argument arg; Semantic_ir.Bool (predicate arg.ty) ]))

let compile_predicate name args expected_ty =
  type_predicate name (fun actual_ty -> Types.equal actual_ty expected_ty) args

let compile_bool_literal_predicate name args expected =
  match one_arg name args with
  | Error _ as err -> err
  | Ok arg ->
      let expression =
        if Types.is_dynamic arg.ty then
          Semantic_ir.Apply
            ( Semantic_ir.Ident
                (if expected then "Lg_runtime.Runtime_dynamic.is_true"
                 else "Lg_runtime.Runtime_dynamic.is_false"),
              [ arg.semantic_expr ] )
        else if Edn_value_elaborator.is_value_type arg.ty then
          Semantic_ir.Apply
            ( Semantic_ir.Ident
                (if expected then "Lg_runtime.Runtime_edn.is_true"
                 else "Lg_runtime.Runtime_edn.is_false"),
              [ arg.semantic_expr ] )
        else if Types.equal arg.ty TBool then
          Semantic_ir.Infix ("=", arg.semantic_expr, Semantic_ir.Bool expected)
        else if Option.is_some (Types.truthy_constraint_info arg.ty) then
          (* Constrained values are (witness, value) pairs; evaluate the
             witness on the payload to get the logical value, then compare
             it against the literal. *)
          Semantic_ir.Infix
            ( "=",
              Semantic_ir.Apply
                ( Semantic_ir.Apply
                    (Semantic_ir.Ident "fst", [ arg.semantic_expr ]),
                  [ Semantic_ir.Apply
                      (Semantic_ir.Ident "snd", [ arg.semantic_expr ]) ] ),
              Semantic_ir.Bool expected )
        else if Type_solver.is_open arg.ty then
          (* The value's type is open, so it may hold a boolean at runtime;
             compare structurally instead of assuming it is never the
             literal. *)
          Semantic_ir.Infix ("=", arg.semantic_expr, Semantic_ir.Bool expected)
        else
          Semantic_ir.Sequence [ evaluated_argument arg; Semantic_ir.Bool false ]
      in
      Ok (typed_ir TBool expression)

let compile_type_predicate name predicate args = type_predicate name predicate args

let compile_runtime_type_predicate name runtime_function predicate args =
  match one_arg name args with
  | Error _ as error -> error
  | Ok arg when Types.is_dynamic arg.ty ->
      Ok
        (typed_ir TBool
           (Semantic_ir.Apply
              (Semantic_ir.Ident runtime_function, [ arg.semantic_expr ])))
  | Ok ({ ty = (TNullable inner | TOcaml_app ("option", [ inner ])); _ } as arg)
    ->
      let expression =
        if Types.is_dynamic inner then
          let payload_name = "__lg_type_predicate_payload" in
          Semantic_ir.Match
            ( arg.semantic_expr,
              [
                (Semantic_ir.PConstructor ("None", None), Semantic_ir.Bool false);
                ( Semantic_ir.PConstructor
                    ("Some", Some (Semantic_ir.PVar payload_name)),
                  Semantic_ir.Apply
                    ( Semantic_ir.Ident runtime_function,
                      [ Semantic_ir.Ident payload_name ] ) );
              ] )
        else if predicate inner then
          Semantic_ir.Apply
            (Semantic_ir.Ident "Option.is_some", [ arg.semantic_expr ])
        else
          Semantic_ir.Sequence
            [ evaluated_argument arg; Semantic_ir.Bool false ]
      in
      Ok (typed_ir TBool expression)
  | Ok arg ->
      Ok
        (typed_ir TBool
           (Semantic_ir.Sequence
              [ evaluated_argument arg; Semantic_ir.Bool (predicate arg.ty) ]))

let compile_string_family_predicate ~target name ~keyword args =
  match one_arg name args with
  | Error _ as err -> err
  | Ok arg -> (
      match arg.ty with
      | ty when Types.is_dynamic ty ->
          let function_name =
            if keyword then "Lg_runtime.Runtime_dynamic.is_keyword"
            else "Lg_runtime.Runtime_dynamic.is_string"
          in
          Ok
            (typed_ir TBool
               (Semantic_ir.Apply
                  (Semantic_ir.Ident function_name, [ arg.semantic_expr ])))
      | TUnknown ->
          let starts_with_colon =
            Semantic_ir.Apply
              ( Semantic_ir.Ident "Lg_runtime.Runtime_string.starts_with",
                [ arg.semantic_expr; Semantic_ir.String ":" ] )
          in
          let expression =
            if keyword then starts_with_colon
            else Semantic_ir.Prefix ("not", starts_with_colon)
          in
          Ok (typed_ir TBool expression)
      | actual
        when Option.is_some (Types.protocol_constraint_info actual)
             || Option.is_some (Types.contains_constraint_info actual) ->
          Error.error ~code:Error_code.Semantic
            (name
           ^ " requires a closed sum type when the value may have multiple \
              static types")
      | actual ->
          let matches =
            if keyword then Types.equal actual TKeyword
            else
              Types.equal actual TString
              || (target = Target.Melange && Types.equal actual TChar)
          in
          Ok
            (typed_ir TBool
               (Semantic_ir.Sequence
                  [ evaluated_argument arg; Semantic_ir.Bool matches ])))

let compile_nil_predicate name args expected_nil =
  match one_arg name args with
  | Error _ as err -> err
  | Ok arg ->
      let is_nil =
        Expression_support.nil_predicate_expression arg.ty arg.semantic_expr
      in
      let expression =
        if expected_nil then is_nil else Semantic_ir.Prefix ("not", is_nil)
      in
      Ok (typed_ir TBool expression)

let compile ~target name args =
  match name with
  | "__lg_nil-predicate" -> compile_nil_predicate name args true
  | "__lg_true-predicate" -> compile_bool_literal_predicate name args true
  | "__lg_false-predicate" -> compile_bool_literal_predicate name args false
  | "__lg_int-predicate" ->
      if target <> Target.Melange then
        compile_runtime_type_predicate name "Lg_runtime.Runtime_dynamic.is_int"
          (function TInt -> true | _ -> false)
          args
      else (
        match one_arg name args with
        | Error _ as error -> error
        | Ok arg when Types.is_dynamic arg.ty ->
            Ok
              (typed_ir TBool
                 (Semantic_ir.Apply
                    ( Semantic_ir.Ident
                        "Lg_runtime.Runtime_dynamic.is_integer_number",
                      [ arg.semantic_expr ] )))
        | Ok arg ->
            let expression =
              match arg.ty with
              | TInt ->
                  Semantic_ir.Sequence
                    [ evaluated_argument arg; Semantic_ir.Bool true ]
              | TFloat ->
                  Semantic_ir.Apply
                    ( Semantic_ir.Ident
                        "Lg_runtime.Runtime_int_melange.is_safe_float_integer",
                      [ arg.semantic_expr ] )
              | TOcaml "Lg_runtime.Runtime_decimal.t" ->
                  Semantic_ir.Apply
                    ( Semantic_ir.Ident
                        "Lg_runtime.Runtime_decimal.is_safe_integer",
                      [ arg.semantic_expr ] )
              | _ ->
                  Semantic_ir.Sequence
                    [ evaluated_argument arg; Semantic_ir.Bool false ]
            in
            Ok (typed_ir TBool expression))
  | "__lg_number-predicate" ->
      compile_runtime_type_predicate name "Lg_runtime.Runtime_dynamic.is_number"
        (fun ty ->
          Types.is_numeric ty
          || Types.equal ty (TOcaml "Lg_runtime.Runtime_decimal.t")
          || Types.equal ty (TOcaml "Lg_runtime.Runtime_ratio.t"))
        args
  | "__lg_string-predicate" ->
      compile_string_family_predicate ~target name ~keyword:false args
  | "__lg_keyword-predicate" ->
      compile_string_family_predicate ~target name ~keyword:true args
  | "__lg_list-predicate" ->
      compile_runtime_type_predicate name "Lg_runtime.Runtime_dynamic.is_list"
        (function TList _ -> true | _ -> false)
        args
  | "__lg_seq-predicate" ->
      (match one_arg name args with
      | Error _ as error -> error
      | Ok arg when Option.is_some (Types.next_seq_element arg.ty) ->
          Ok
            (typed_ir TBool
               (Semantic_ir.Apply
                  ( Semantic_ir.Ident "not",
                    [
                      Semantic_ir.Apply
                        ( Semantic_ir.Ident
                            "Lg_runtime.Runtime_seq.is_empty",
                          [ arg.semantic_expr ] );
                    ] )))
      | Ok _ ->
          compile_runtime_type_predicate name
            "Lg_runtime.Runtime_dynamic.is_seq"
            (function TList _ | TSeq _ -> true | _ -> false)
            args)
  | "__lg_fn-predicate" ->
      let rec overloaded_storage_predicate = function
        | TUnit -> true
        | TTuple [ TFn _; rest ] -> overloaded_storage_predicate rest
        | _ -> false
      in
      compile_type_predicate name
        (function
          | TFn _ | TOverloaded_fn _ -> true
          | ty when Option.is_some (Types.constant_function_result ty) -> true
          | ty -> overloaded_storage_predicate ty)
        args
  | "__lg_uuid-predicate" ->
      (match one_arg name args with
      | Error _ as error -> error
      | Ok
          ({
             ty =
               (TNullable (TOcaml "Lg_runtime.Runtime_uuid.t")
               | TOcaml_app
                   ( "option",
                     [ TOcaml "Lg_runtime.Runtime_uuid.t" ] ));
             semantic_expr;
             _;
           }) ->
          Ok
            (typed_ir TBool
               (Semantic_ir.Apply
                  (Semantic_ir.Ident "Option.is_some", [ semantic_expr ])))
      | Ok arg ->
          Ok
            (typed_ir TBool
               (Semantic_ir.Sequence
                  [
                    evaluated_argument arg;
                    Semantic_ir.Bool
                      (Types.equal arg.ty
                         (TOcaml "Lg_runtime.Runtime_uuid.t"));
                  ])))
  | "__lg_delay-predicate" ->
      compile_type_predicate name
        (function TOcaml_app ("Lazy.t", [ _ ]) -> true | _ -> false)
        args
  | _ -> Error.error ~code:Error_code.Unresolved ("unknown function " ^ name)
