open Types

let value_ty = Edn_value_elaborator.value_ty

let compile_form ~compile_expr scope env form =
  Result.bind
    (compile_expr scope
       (Compiler_environment.with_expected_type (Some value_ty) env) form)
    (fun value ->
      Edn_value_elaborator.pack_expression value.ty value.semantic_expr
      |> Result.map (typed_ir value_ty))

let callback_argument ~pack_argument parameter_ty expression =
  let scalar_accessor =
    match parameter_ty with
    | TInt | TOcaml "int" -> Some "int_value"
    | TFloat -> Some "float_value"
    | TChar -> Some "char_value"
    | TString -> Some "string_value"
    | TKeyword -> Some "keyword_value"
    | TSymbol -> Some "symbol_value"
    | TBool -> Some "bool_value"
    | _ -> None
  in
  match scalar_accessor with
  | Some accessor ->
      Ok
        (Semantic_ir.Apply
           (Semantic_ir.Ident ("Lg_runtime.Runtime_metadata." ^ accessor),
            [ expression ]))
  | None -> pack_argument parameter_ty (typed_ir value_ty expression)

let compile_callback ~compile_expr ~pack_argument scope env form =
  Result.bind (compile_expr scope env form) (fun callback ->
    match callback.ty with
    | TFn ([ parameter_ty ], _) ->
        let parameter_name = "__lg_tap_value" in
        Result.map
          (fun argument ->
            typed_ir (TFn ([ value_ty ], TUnit))
              (Semantic_ir.Fun
                 ([ Semantic_ir.PVar parameter_name ],
                  Semantic_ir.Sequence
                    [ Semantic_ir.Apply (callback.semantic_expr, [ argument ]);
                      Semantic_ir.Unit ])))
          (callback_argument ~pack_argument parameter_ty
             (Semantic_ir.Ident parameter_name))
    | TFn (parameters, _) ->
        Error.error ~code:Error_code.Arity
          ("tap callbacks expect one argument, got "
           ^ string_of_int (List.length parameters))
    | _ ->
        Error.error ~code:Error_code.Arity
          ("tap expects a one-argument function, got "
           ^ Types.source_name callback.ty))
