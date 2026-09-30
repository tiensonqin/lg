open Types

let one_arg name args =
  match args with
  | [ arg ] -> Ok arg
  | _ -> Error.error ~code:Error_code.Arity (name ^ " expects 1 arguments")

let evaluated_argument arg =
  Semantic_ir.evaluate_for_effect arg.semantic_expr

let apply name args = Semantic_ir.Apply (Semantic_ir.Ident name, args)

let compile ~target name args =
  match one_arg name args with
  | Error _ as err -> err
  | Ok arg ->
      let bool value = Ok (typed_ir TBool value) in
      let static_bool value =
        bool
          (Semantic_ir.Sequence
             [ evaluated_argument arg; Semantic_ir.Bool value ])
      in
      match name with
      | "__lg_ratio-predicate"
        when Types.equal arg.ty (TOcaml "Lg_runtime.Runtime_ratio.t") ->
          bool
            (apply "Lg_runtime.Runtime_ratio.is_ratio"
               [ arg.semantic_expr ])
      | "__lg_ratio-predicate" -> static_bool false
      | "__lg_rational-predicate" ->
          static_bool
            (Types.equal arg.ty TInt
            || Types.equal arg.ty (TOcaml "Lg_runtime.Runtime_ratio.t")
            || Types.equal arg.ty (TOcaml "Lg_runtime.Runtime_decimal.t"))
      | "__lg_decimal-predicate" ->
          static_bool
            (Types.equal arg.ty (TOcaml "Lg_runtime.Runtime_decimal.t"))
      | "__lg_float-predicate" | "__lg_double-predicate" ->
          static_bool
            (Types.equal arg.ty TFloat
            || (target = Target.Melange
               &&
               (Types.equal arg.ty TInt
               || Types.equal arg.ty
                    (TOcaml "Lg_runtime.Runtime_decimal.t"))))
      | "__lg_symbol-predicate"
        when Option.is_some
               (Types.symbol_predicate_constraint_info arg.ty) ->
          let projected =
            match Semantic_ir.unlocated arg.semantic_expr with
            | Semantic_ir.Ident name ->
                apply (name ^ "__symbol") [ arg.semantic_expr ]
            | _ ->
                apply "fst" [ arg.semantic_expr ]
                |> fun projector ->
                Semantic_ir.Apply
                  ( projector,
                    [ apply "snd" [ arg.semantic_expr ] ] )
          in
          bool (apply "Option.is_some" [ projected ])
      | "__lg_symbol-predicate"
        when Types.is_dynamic arg.ty || Types.equal arg.ty TUnknown ->
          bool
            (apply "Lg_runtime.Runtime_dynamic.is_symbol"
               [ arg.semantic_expr ])
      | "__lg_symbol-predicate" -> static_bool (Types.equal arg.ty TSymbol)
      | "__lg_char-predicate"
        when target = Target.Melange && Types.equal arg.ty TString ->
          bool
            (Semantic_ir.Infix
               ( "=",
                 Semantic_ir.Apply
                   (Semantic_ir.Ident "String.length", [ arg.semantic_expr ]),
                 Semantic_ir.Int 1 ))
      | "__lg_char-predicate" -> static_bool (Types.equal arg.ty TChar)
      | "__lg_regex-predicate" -> static_bool (Types.equal arg.ty TRegex)
      | _ -> Error.error ~code:Error_code.Unresolved ("unknown function " ^ name)
