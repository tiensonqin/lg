open Types

let apply name args = Semantic_ir.Apply (Semantic_ir.Ident name, args)

let concat_expr = function
  | [] -> Semantic_ir.String ""
  | parts ->
      let bindings, values =
        parts
        |> List.mapi (fun index part ->
               let name = "__lg_concat_" ^ string_of_int index in
               ((Semantic_ir.PVar name, part), Semantic_ir.Ident name))
        |> List.split
      in
      let body =
        match values with
        | [] -> assert false
        | first :: rest ->
            List.fold_left
              (fun acc part -> Semantic_ir.Infix ("^", acc, part))
              first rest
      in
      Semantic_ir.Let (bindings, body)

let wrap_expr prefix value suffix =
  concat_expr [ Semantic_ir.String prefix; value; Semantic_ir.String suffix ]

let render_strings ?print_length separator values =
  match print_length with
  | None -> apply "String.concat" [ separator; values ]
  | Some print_length ->
      apply "Lg_runtime.Runtime_print.render_strings"
        [ separator; print_length; values ]

let render_print_level ?print_level render_collection =
  match print_level with
  | None -> render_collection None
  | Some print_level ->
      let level_name = "__lg_print_level" in
      Semantic_ir.Match
        ( print_level,
          [
            (Semantic_ir.PConstructor ("None", None), render_collection None);
            ( Semantic_ir.PConstructor
                ("Some", Some (Semantic_ir.PVar level_name)),
              Semantic_ir.If
                ( Semantic_ir.Infix
                    ("<=", Semantic_ir.Ident level_name, Semantic_ir.Int 0),
                  Semantic_ir.String "#",
                  render_collection
                    (Some
                       (Semantic_ir.Constructor
                          ( "Some",
                            Some
                              (Semantic_ir.Infix
                                 ( "-", Semantic_ir.Ident level_name,
                                   Semantic_ir.Int 1 )) ))) ) );
          ] )

let rec stringify_expr_ir ?(pr = false) ?print_length ?print_level expr =
  let scalar_mapper ?print_level ty =
    match ty with
    | TInt | TOcaml "int" -> Semantic_ir.Ident "string_of_int"
    | TFloat ->
        Semantic_ir.Ident
          (if pr then "Lg_runtime.Runtime_dynamic.pr_str_float"
           else "Lg_runtime.Runtime_dynamic.str_float")
    | TSymbol | TKeyword -> Semantic_ir.Fun ([ Semantic_ir.PVar "x" ], Semantic_ir.Ident "x")
    | TString ->
        if pr then
          Semantic_ir.Fun
            ( [ Semantic_ir.PVar "x" ],
              apply "Printf.sprintf" [ Semantic_ir.String "%S"; Semantic_ir.Ident "x" ] )
        else
          Semantic_ir.Fun
            ( [ Semantic_ir.PVar "x" ],
              wrap_expr "\"" (Semantic_ir.Ident "x") "\"" )
    | TBool -> Semantic_ir.Ident "string_of_bool"
    | ty when Types.is_dynamic ty ->
        Semantic_ir.Fun
          ( [ Semantic_ir.PVar "x" ],
            apply
              (if pr then "Lg_runtime.Runtime_dynamic.pr_str"
               else "Lg_runtime.Runtime_dynamic.str")
              [ Semantic_ir.Ident "x" ] )
    | TUnknown | TMeta _ | TVar _ ->
        Semantic_ir.Fun ([ Semantic_ir.PAny ], Semantic_ir.String "<value>")
    | TNullable inner | TOcaml_app ("option", [ inner ]) ->
        Semantic_ir.Fun
          ( [ Semantic_ir.PVar "value" ],
            stringify_expr_ir ~pr ?print_length ?print_level
              (typed_ir
                 (TOcaml_app ("option", [ inner ]))
                 (Semantic_ir.Ident "value")) )
    | TOcaml "value" ->
        Semantic_ir.Fun ([ Semantic_ir.PAny ], Semantic_ir.String "<value>")
    | TOcaml "Lg_edn_backend.t" ->
        Semantic_ir.Ident
          (if pr then "Lg_runtime.Runtime_edn.pr_str"
           else "Lg_runtime.Runtime_edn.str")
    | TList _ | TSeq _ | TVector _ | TSet _ ->
        Semantic_ir.Fun
          ( [ Semantic_ir.PVar "value" ],
            stringify_expr_ir ~pr ?print_length ?print_level
              (typed_ir ty (Semantic_ir.Ident "value")) )
    | ty when Option.is_some (Types.next_seq_element ty) ->
        Semantic_ir.Fun
          ( [ Semantic_ir.PVar "value" ],
            stringify_expr_ir ~pr ?print_length ?print_level
              (typed_ir ty (Semantic_ir.Ident "value")) )
    | _ -> Semantic_ir.Fun ([ Semantic_ir.PAny ], Semantic_ir.String "<value>")
  in
  match expr.ty with
  | TPoly_variant row ->
      let cases = List.map (fun (tag, payload) ->
        match payload with
        | None -> (Semantic_ir.PPolyTag (tag, None), Semantic_ir.String ("(tag " ^ tag ^ ")"))
        | Some ty ->
            let value = typed_ir ty (Semantic_ir.Ident "__lg_tag_payload") in
            (Semantic_ir.PPolyTag (tag, Some (Semantic_ir.PVar "__lg_tag_payload")),
             wrap_expr ("(tag " ^ tag ^ " ") (stringify_expr_ir ~pr ?print_length ?print_level value) ")")) row.tags in
      let cases = if row.bound = Lower_row then cases @ [Semantic_ir.PAny, Semantic_ir.String "<variant>"] else cases in
      Semantic_ir.Match (expr.semantic_expr, cases)
  | TInt | TOcaml "int" -> apply "string_of_int" [ expr.semantic_expr ]
  | TFloat ->
      apply
        (if pr then "Lg_runtime.Runtime_dynamic.pr_str_float"
         else "Lg_runtime.Runtime_dynamic.str_float")
        [ expr.semantic_expr ]
  | TChar -> apply "String.make" [ Semantic_ir.Int 1; expr.semantic_expr ]
  | TString | TRegex ->
      if pr then apply "Printf.sprintf" [ Semantic_ir.String "%S"; expr.semantic_expr ]
      else expr.semantic_expr
  | TSymbol | TKeyword -> expr.semantic_expr
  | TBool -> apply "string_of_bool" [ expr.semantic_expr ]
  | TUnit -> Semantic_ir.Sequence [ expr.semantic_expr; Semantic_ir.String "" ]
  | TNil ->
      Semantic_ir.Sequence [ expr.semantic_expr; Semantic_ir.String "nil" ]
  | ty when Types.is_dynamic ty ->
      apply
        (if pr then "Lg_runtime.Runtime_dynamic.pr_str"
         else "Lg_runtime.Runtime_dynamic.str")
        [ expr.semantic_expr ]
  | TNullable inner | TOcaml_app ("option", [ inner ]) ->
      Semantic_ir.Match
        ( expr.semantic_expr,
          [ (Semantic_ir.PConstructor ("None", None), Semantic_ir.String "nil");
            ( Semantic_ir.PConstructor
                ("Some", Some (Semantic_ir.PVar "value")),
              stringify_expr_ir ~pr ?print_length ?print_level
                (typed_ir inner (Semantic_ir.Ident "value")) );
          ] )
  | TUnknown -> (
      match Semantic_ir.unlocated expr.semantic_expr with
      | Semantic_ir.Field _ ->
          apply
            (if pr then "Lg_runtime.Runtime_dynamic.pr_str"
             else "Lg_runtime.Runtime_dynamic.str")
            [ expr.semantic_expr ]
      | _ -> expr.semantic_expr)
  | TMap_keys -> Semantic_ir.String "<map>"
  | TMeta _ | TVar _ ->
      Semantic_ir.Sequence [ expr.semantic_expr; Semantic_ir.String "<value>" ]
  | TOcaml "Lg_runtime.Runtime_uuid.t" ->
      apply "Lg_runtime.Runtime_uuid.to_string" [ expr.semantic_expr ]
  | TOcaml "Lg_runtime.Runtime_instant.t" ->
      apply
        (if pr then "Lg_runtime.Runtime_instant.to_edn_string"
         else "Lg_runtime.Runtime_instant.to_string")
        [ expr.semantic_expr ]
  | TOcaml "Lg_runtime.Runtime_decimal.t" ->
      apply
        (if pr then "Lg_runtime.Runtime_decimal.to_edn_string"
         else "Lg_runtime.Runtime_decimal.to_string")
        [ expr.semantic_expr ]
  | TOcaml "Lg_runtime.Runtime_ratio.t" ->
      apply "Lg_runtime.Runtime_ratio.to_string" [ expr.semantic_expr ]
  | TOcaml "Lg_edn_backend.t" ->
      apply
        (if pr then "Lg_runtime.Runtime_edn.pr_str"
         else "Lg_runtime.Runtime_edn.str")
        [ expr.semantic_expr ]
  | TOcaml "value" ->
      Semantic_ir.Sequence [ expr.semantic_expr; Semantic_ir.String "<value>" ]
  | ty when Option.is_some (Types.next_seq_element ty) ->
      let inner = Option.get (Types.next_seq_element ty) in
      render_print_level ?print_level (fun child_print_level ->
          Semantic_ir.If
            ( apply "Lg_runtime.Runtime_seq.is_empty" [ expr.semantic_expr ],
              Semantic_ir.String "nil",
              wrap_expr "("
                (render_strings ?print_length (Semantic_ir.String " ")
                   (apply "List.map"
                      [
                        scalar_mapper ?print_level:child_print_level inner;
                        apply "Lg_runtime.Runtime_seq.to_list"
                          [ expr.semantic_expr ];
                      ]))
                ")" ))
  | TArray _ | TRef _ | TOcaml _ | TOcaml_app _ | TTuple _ | TConstraint _
  | TCompiler _ ->
      Semantic_ir.String "<value>"
  | TList inner ->
      render_print_level ?print_level (fun child_print_level ->
          wrap_expr "("
            (render_strings ?print_length (Semantic_ir.String " ")
               (apply "List.map"
                  [
                    scalar_mapper ?print_level:child_print_level inner;
                    expr.semantic_expr;
                  ]))
            ")")
  | TSeq inner ->
      render_print_level ?print_level (fun child_print_level ->
          wrap_expr "("
            (render_strings ?print_length (Semantic_ir.String " ")
               (apply "List.map"
                  [
                    scalar_mapper ?print_level:child_print_level inner;
                    apply "Lg_runtime.Runtime_seq.to_list"
                      [ expr.semantic_expr ];
                  ]))
            ")")
  | TVector inner ->
      render_print_level ?print_level (fun child_print_level ->
          wrap_expr "["
            (render_strings ?print_length (Semantic_ir.String " ")
               (apply "List.map"
                  [
                    scalar_mapper ?print_level:child_print_level inner;
                    apply "Rrbvec.to_list" [ expr.semantic_expr ];
                  ]))
            "]")
  | TSet inner ->
      render_print_level ?print_level (fun child_print_level ->
          let mapper =
            Semantic_ir.Fun
              ( [ Semantic_ir.PVar "value" ],
                stringify_expr_ir ~pr ?print_length
                  ?print_level:child_print_level
                  (typed_ir inner (Semantic_ir.Ident "value")) )
          in
          let values =
            match Types.set_module_name inner with
            | Ok set_module ->
                apply (set_module ^ ".elements") [ expr.semantic_expr ]
            | Error _ -> Semantic_ir.List []
          in
          wrap_expr "#{"
            (render_strings ?print_length (Semantic_ir.String " ")
               (apply "List.map" [ mapper; values ]))
            "}")
  | TFn _ | TOverloaded_fn _ -> Semantic_ir.String "<function>"
  | (TRecord fields | TNamed_record { fields; _ }) ->
      render_print_level ?print_level (fun child_print_level ->
          let field_part field expression =
            concat_expr
              [
                Semantic_ir.String (field.keyword ^ " ");
                stringify_expr_ir ~pr:true ?print_length
                  ?print_level:child_print_level
                  (typed_ir field.ty expression);
              ]
          in
          let parts =
            match expr.record_values with
            | Some values ->
                values
                |> List.map (fun ((field : field), expression) ->
                       field_part field expression)
            | None ->
                fields
                |> List.map (fun (field : field) ->
                       field_part field (Structural_map.field_expr expr field))
          in
          wrap_expr "{"
            (render_strings ?print_length (Semantic_ir.String ", ")
               (Semantic_ir.List parts))
            "}")

let print_expr_ir expr =
  match expr.ty with
  | TString -> stringify_expr_ir ~pr:false expr
  | _ -> stringify_expr_ir ~pr:true expr
