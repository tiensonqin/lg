open Types

let apply name args = Semantic_ir.Apply (Semantic_ir.Ident name, args)

let rec collection_to_list_expr collection =
  match collection.ty with
  | TNullable value_ty | TOcaml_app ("option", [ value_ty ]) ->
      let value_name = "__lg_optional_collection" in
      let value = typed_ir value_ty (Semantic_ir.Ident value_name) in
      Result.map
        (fun (inner, list_expr) ->
          ( inner,
            Semantic_ir.Match
              ( collection.semantic_expr,
                [
                  (Semantic_ir.PConstructor ("None", None), Semantic_ir.List []);
                  ( Semantic_ir.PConstructor
                      ("Some", Some (Semantic_ir.PVar value_name)),
                    list_expr );
                ] ) ))
        (collection_to_list_expr value)
  | TList inner -> Ok (inner, collection.semantic_expr)
  | TVector inner -> Ok (inner, apply "Rrbvec.to_list" [ collection.semantic_expr ])
  | TArray inner -> Ok (inner, apply "Array.to_list" [ collection.semantic_expr ])
  | TSeq inner -> Ok (inner, apply "List.of_seq" [ collection.semantic_expr ])
  | TOcaml_app (name, [ inner ]) when Types.is_next_seq_type_name name ->
      Ok (inner, apply "List.of_seq" [ collection.semantic_expr ])
  | TSet inner ->
      Types.set_module_name inner
      |> Result.map (fun set_module ->
          (inner, apply (set_module ^ ".elements") [ collection.semantic_expr ]))
  | TOcaml_app ("array", [ inner ]) ->
      Ok (inner, apply "Array.to_list" [ collection.semantic_expr ])
  | _ -> Error.error "collection value is not sequenceable"

let collection_to_seq_expr collection =
  match collection.ty with
  | TSeq inner -> Ok (inner, collection.semantic_expr)
  | TOcaml_app (name, [ inner ]) when Types.is_next_seq_type_name name ->
      Ok (inner, collection.semantic_expr)
  | TList inner ->
      Ok
        (inner, apply "Lg_runtime.Runtime_seq.of_list" [ collection.semantic_expr ])
  | TVector inner ->
      Ok
        (inner, apply "Lg_runtime.Runtime_seq.of_vector" [ collection.semantic_expr ])
  | TSet inner ->
      Types.set_module_name inner
      |> Result.map (fun set_module ->
             ( inner,
               apply "Lg_runtime.Runtime_seq.of_list"
                 [ apply (set_module ^ ".elements") [ collection.semantic_expr ] ] ))
  | TArray inner ->
      Ok
        (inner, apply "Lg_runtime.Runtime_seq.of_array" [ collection.semantic_expr ])
  | TOcaml_app ("list", [ inner ]) ->
      Ok
        (inner, apply "Lg_runtime.Runtime_seq.of_list" [ collection.semantic_expr ])
  | TOcaml_app ("array", [ inner ]) ->
      Ok
        (inner, apply "Lg_runtime.Runtime_seq.of_array" [ collection.semantic_expr ])
  | TOcaml_app (("Seq.t" | "Seq"), [ inner ]) ->
      Ok
        (inner, apply "Lg_runtime.Runtime_seq.memoize" [ collection.semantic_expr ])
  | TString ->
      Ok
        (TChar, apply "Lg_runtime.Runtime_seq.of_string" [ collection.semantic_expr ])
  | _ -> Error.error "collection value is not sequenceable"

let rec collection_from_list_expr collection_ty list_expr =
  match collection_ty with
  | TNullable value_ty | TOcaml_app ("option", [ value_ty ]) ->
      Semantic_ir.Constructor
        ("Some", Some (collection_from_list_expr value_ty list_expr))
  | TList _ -> list_expr
  | TVector _ -> apply "Rrbvec.of_list" [ list_expr ]
  | TSeq _ -> apply "Lg_runtime.Runtime_seq.of_list" [ list_expr ]
  | TSet inner -> (
      match Types.set_module_name inner with
      | Ok set_module -> apply (set_module ^ ".of_list") [ list_expr ]
      | Error _ -> list_expr)
  | _ -> list_expr

let take_list_expr count source =
  let name = "take__" in
  let n = Semantic_ir.Ident "n" in
  let xs = Semantic_ir.Ident "xs" in
  let body =
    Semantic_ir.If
      ( Semantic_ir.Infix ("<=", n, Semantic_ir.Int 0),
        Semantic_ir.List [],
        Semantic_ir.Match
          ( xs,
            [ (Semantic_ir.PList [], Semantic_ir.List []);
              ( Semantic_ir.PCons (Semantic_ir.PVar "x", Semantic_ir.PVar "rest"),
                Semantic_ir.Cons
                  ( Semantic_ir.Ident "x",
                    apply name
                      [ Semantic_ir.Infix ("-", n, Semantic_ir.Int 1);
                        Semantic_ir.Ident "rest" ] ) ) ] ) )
  in
  Semantic_ir.LetRec (name, [ Semantic_ir.PVar "n"; Semantic_ir.PVar "xs" ], body, [ count; source ])

let drop_list_expr count source =
  let name = "drop__" in
  let n = Semantic_ir.Ident "n" in
  let xs = Semantic_ir.Ident "xs" in
  let body =
    Semantic_ir.If
      ( Semantic_ir.Infix ("<=", n, Semantic_ir.Int 0),
        xs,
        Semantic_ir.Match
          ( xs,
            [ (Semantic_ir.PList [], Semantic_ir.List []);
              ( Semantic_ir.PCons (Semantic_ir.PAny, Semantic_ir.PVar "rest"),
                apply name
                  [ Semantic_ir.Infix ("-", n, Semantic_ir.Int 1);
                    Semantic_ir.Ident "rest" ] ) ] ) )
  in
  Semantic_ir.LetRec (name, [ Semantic_ir.PVar "n"; Semantic_ir.PVar "xs" ], body, [ count; source ])

let remove fn collection =
  match (fn.ty, collection_to_list_expr collection) with
  | TFn ([ param_ty ], TBool), Ok (inner, list_expr)
    when Result.is_ok (Type_solver.unify Type_solver.empty param_ty inner) ->
      let filtered =
        apply "List.filter"
          [ Semantic_ir.Fun
              ( [ Semantic_ir.PVar "item" ],
                Semantic_ir.Prefix
                  ( "not",
                    Semantic_ir.Apply (fn.semantic_expr, [ Semantic_ir.Ident "item" ]) ) );
            list_expr ]
      in
      Ok (typed_ir collection.ty (collection_from_list_expr collection.ty filtered))
  | TFn _, Ok _ -> Error.error "remove expects a predicate matching collection elements"
  | _, Ok _ -> Error.error "remove expects a function"
  | _, Error _ -> Error.error "remove expects a list, vector, or set"

let take_drop_while name fn collection =
  match (fn.ty, collection_to_list_expr collection) with
  | TFn ([ param_ty ], TBool), Ok (inner, list_expr) when Types.equal param_ty inner ->
      let rec_name = if name = "take-while" then "take_while" else "drop_while" in
      let predicate = Semantic_ir.Apply (fn.semantic_expr, [ Semantic_ir.Ident "item" ]) in
      let body =
        if name = "take-while" then
          Semantic_ir.Match
            ( Semantic_ir.Ident "xs",
              [ ( Semantic_ir.PCons (Semantic_ir.PVar "item", Semantic_ir.PVar "rest"),
                  Semantic_ir.If
                    ( predicate,
                      Semantic_ir.Cons
                        (Semantic_ir.Ident "item", apply rec_name [ Semantic_ir.Ident "rest" ]),
                      Semantic_ir.List [] ) );
                (Semantic_ir.PAny, Semantic_ir.List []) ] )
        else
          Semantic_ir.Match
            ( Semantic_ir.Ident "xs",
              [ ( Semantic_ir.PCons (Semantic_ir.PVar "item", Semantic_ir.PVar "rest"),
                  Semantic_ir.If
                    ( predicate,
                      apply rec_name [ Semantic_ir.Ident "rest" ],
                      Semantic_ir.Cons (Semantic_ir.Ident "item", Semantic_ir.Ident "rest") ) );
                (Semantic_ir.PList [], Semantic_ir.List []) ] )
      in
      let list_expr =
        Semantic_ir.LetRec (rec_name, [ Semantic_ir.PVar "xs" ], body, [ list_expr ])
      in
      Ok (typed_ir collection.ty (collection_from_list_expr collection.ty list_expr))
  | TFn _, Ok _ ->
      Error.error (name ^ " expects a predicate matching collection elements")
  | _, Ok _ -> Error.error (name ^ " expects a function")
  | _, Error _ -> Error.error (name ^ " expects a list, vector, or set")

let sort collection =
  if Types.is_dynamic collection.ty then
    Ok
      (typed_ir collection.ty
         (apply "Lg_runtime.Runtime_dynamic.sort" [ collection.semantic_expr ]))
  else
    match collection_to_list_expr collection with
    | Error _ -> Error.error "sort expects a list, vector, or set"
    | Ok (inner, list_expr) ->
        let comparator =
          if Types.is_dynamic inner then
            Semantic_ir.Ident "Lg_runtime.Runtime_dynamic.compare"
          else if Types.equal inner TKeyword || Types.equal inner TSymbol then
            Semantic_ir.Ident "Lg_runtime.Runtime_keyword.compare_identifier"
          else Semantic_ir.Ident "compare"
        in
        Ok
          (typed_ir (TList inner)
             (apply "List.sort" [ comparator; list_expr ]))

let vec collection =
  match collection_to_list_expr collection with
  | Error _ -> Error.error "vec expects a list, vector, or set"
  | Ok (inner, list_expr) ->
      Ok (typed_ir (TVector inner) (apply "Rrbvec.of_list" [ list_expr ]))

let set collection =
  match collection_to_list_expr collection with
  | Error _ -> Error.error "set expects a list, vector, or set"
  | Ok (TSeq inner, list_expr) ->
      let element_ty = TList inner in
      Types.set_module_name element_ty
      |> Result.map (fun set_module ->
             typed_ir (TSet element_ty)
               (apply (set_module ^ ".of_list")
                  [
                    apply "List.map"
                      [
                        Semantic_ir.Ident "List.of_seq";
                        list_expr;
                      ];
                  ]))
  | Ok (inner, list_expr) ->
      Types.set_module_name inner
      |> Result.map (fun set_module ->
             typed_ir (TSet inner)
               (apply (set_module ^ ".of_list") [ list_expr ]))

let into target source =
  match collection_to_list_expr source with
  | Error _ -> Error.error "into source must be a collection"
  | Ok (source_inner, source_list_expr) -> (
      match target.ty with
      | target_ty when Option.is_some (Types.dynamic_map_types target_ty) ->
          let target_key, target_value =
            Option.get (Types.dynamic_map_types target_ty)
          in
          let unresolved = function
            | TUnknown | TMeta _ | TVar _ -> true
            | _ -> false
          in
          let compatible expected actual =
            unresolved expected
            || unresolved actual
            || Types.equal expected actual
            || Types.row_compatible ~expected ~actual
          in
          (match source_inner with
          | TTuple [ source_key; source_value ]
            when compatible target_key source_key
                 && compatible target_value source_value ->
              let result_key =
                if unresolved target_key && not (unresolved source_key) then
                  source_key
                else target_key
              in
              let result_value =
                if unresolved target_value && not (unresolved source_value) then
                  source_value
                else if
                  (not (Types.equal target_value source_value))
                  && Types.row_compatible ~expected:target_value
                       ~actual:source_value
                then source_value
                else target_value
              in
              let source_list_expr =
                if Types.equal result_value source_value then source_list_expr
                else
                  match Types.record_fields target_value with
                  | Some fields
                    when Types.row_compatible ~expected:target_value
                           ~actual:source_value ->
                      let source_fields =
                        Types.record_fields source_value
                        |> Option.value ~default:[]
                      in
                      let entry_name = "__lg_into_entry" in
                      let value =
                        typed_ir source_value
                          (apply "snd" [ Semantic_ir.Ident entry_name ])
                      in
                      let values =
                        List.map
                          (fun (field : field) ->
                            let source_field =
                              Types.find_field field.keyword source_fields
                              |> Option.value ~default:field
                            in
                            let source_field_value =
                              "__lg_into_source_field_" ^ source_field.ocaml_name
                            in
                            let source_pattern =
                              Semantic_ir.PConstraint
                                ( Semantic_ir.PRecord
                                    [
                                      ( source_field.ocaml_name,
                                        Semantic_ir.PVar source_field_value );
                                    ],
                                  Types.ocaml_name source_value )
                            in
                            let source_field_expr =
                              Semantic_ir.Apply
                                ( Semantic_ir.Fun
                                    ( [ source_pattern ],
                                      Semantic_ir.Ident source_field_value ),
                                  [ value.semantic_expr ] )
                            in
                            (field, source_field_expr))
                          fields
                      in
                      let adapted_value =
                        match target_value with
                        | TNamed_record record ->
                            Structural_map.named_record_expr record values
                        | _ ->
                            Structural_map.record_expr fields values
                      in
                      apply "List.map"
                        [
                          Semantic_ir.Fun
                            ( [ Semantic_ir.PVar entry_name ],
                              Semantic_ir.Tuple
                                [
                                  apply "fst" [ Semantic_ir.Ident entry_name ];
                                  adapted_value.semantic_expr;
                                ] );
                          Semantic_ir.Constraint
                            ( source_list_expr,
                              "(" ^ Types.ocaml_name source_key ^ " * "
                              ^ Types.ocaml_name source_value ^ ") list" );
                        ]
                  | Some _ | None -> source_list_expr
              in
              Ok
                (typed_ir (Types.dynamic_map result_key result_value)
                   (apply "List.fold_left"
                      [
                        Semantic_ir.Fun
                          ( [
                              Semantic_ir.PVar "map";
                              Semantic_ir.PVar "entry";
                            ],
                            apply "Lg_runtime.Runtime_map.assoc"
                              [
                                Semantic_ir.Ident "map";
                                apply "fst" [ Semantic_ir.Ident "entry" ];
                                apply "snd" [ Semantic_ir.Ident "entry" ];
                              ] );
                        target.semantic_expr;
                        source_list_expr;
                      ]))
          | TTuple [ _; _ ] ->
              Error.error
                ("into source entry types " ^ Types.source_name source_inner
               ^ " must match target map types "
               ^ Types.source_name target.ty)
          | (TUnknown | TMeta _ | TVar _) ->
              Ok
                (typed_ir (Types.dynamic_map target_key target_value)
                   (apply "List.fold_left"
                      [
                        Semantic_ir.Fun
                          ( [
                              Semantic_ir.PVar "map";
                              Semantic_ir.PVar "entry";
                            ],
                            apply "Lg_runtime.Runtime_map.assoc"
                              [
                                Semantic_ir.Ident "map";
                                apply "fst" [ Semantic_ir.Ident "entry" ];
                                apply "snd" [ Semantic_ir.Ident "entry" ];
                              ] );
                        target.semantic_expr;
                        source_list_expr;
                      ]))
          | _ ->
              Error.error
                "into map target expects key-value tuple entries")
      | TVector (TUnknown | TMeta _ | TVar _) ->
          Ok
            (typed_ir (TVector source_inner)
               (apply "Rrbvec.append_list"
                  [ target.semantic_expr; source_list_expr ]))
      | TVector target_inner when Types.equal target_inner source_inner -> (
          match source.ty with
          | TVector _ ->
              Ok
                (typed_ir target.ty
                   (apply "Rrbvec.append" [ target.semantic_expr; source.semantic_expr ]))
          | _ ->
              Ok
                (typed_ir target.ty
                   (apply "Rrbvec.append_list" [ target.semantic_expr; source_list_expr ])))
      | TVector target_inner
        when Types.is_dynamic target_inner && Types.is_dynamic source_inner ->
          Ok
            (typed_ir target.ty
               (apply "Rrbvec.append_list"
                  [ target.semantic_expr; source_list_expr ]))
      | TList target_inner when Types.equal target_inner source_inner ->
          Ok
            (typed_ir target.ty
               (apply "List.fold_left"
                  [ Semantic_ir.Fun
                      ( [ Semantic_ir.PVar "acc"; Semantic_ir.PVar "item" ],
                        Semantic_ir.Cons (Semantic_ir.Ident "item", Semantic_ir.Ident "acc") );
                    target.semantic_expr;
                    source_list_expr ]))
      | TList target_inner
        when Types.is_dynamic target_inner && Types.is_dynamic source_inner ->
          Ok
            (typed_ir target.ty
               (apply "List.fold_left"
                  [ Semantic_ir.Fun
                      ( [ Semantic_ir.PVar "acc"; Semantic_ir.PVar "item" ],
                        Semantic_ir.Cons
                          (Semantic_ir.Ident "item", Semantic_ir.Ident "acc") );
                    target.semantic_expr;
                    source_list_expr ]))
      | TSet (TUnknown | TMeta _ | TVar _) ->
          Types.set_module_name source_inner
          |> Result.map (fun set_module ->
                 typed_ir (TSet source_inner)
                   (apply (set_module ^ ".of_list")
                      [ Semantic_ir.Infix
                          ( "@",
                            apply "Lg_runtime.Runtime_poly_set.elements"
                              [ target.semantic_expr ],
                            source_list_expr ) ]))
      | TSet target_inner when Types.equal target_inner source_inner ->
          Types.set_module_name target_inner
          |> Result.map (fun set_module ->
                 typed_ir target.ty
                   (apply (set_module ^ ".of_list")
                      [ Semantic_ir.Infix
                          ( "@",
                            apply (set_module ^ ".elements") [ target.semantic_expr ],
                            source_list_expr ) ]))
      | TVector _ | TList _ | TSet _ ->
          Error.error "into source element type must match target element type"
      | _ -> Error.error "into target must be a collection")

let into_cat target source =
  match collection_to_list_expr source with
  | Error _ ->
      Error.error
        ("into cat source must be a collection, got "
       ^ Types.source_name source.ty)
  | Ok (TVector element_type, outer) ->
      let flattened =
        apply "List.concat"
          [ apply "List.map"
              [ Semantic_ir.Ident "Rrbvec.to_list"; outer ] ]
      in
      into target (typed_ir (TList element_type) flattened)
  | Ok (TList element_type, outer) ->
      into target
        (typed_ir (TList element_type) (apply "List.concat" [ outer ]))
  | Ok (inner, outer)
    when Types.is_dynamic inner
         || match inner with TUnknown | TMeta _ | TVar _ -> true | _ -> false ->
      let flattened =
        apply "List.concat"
          [ apply "List.map"
              [
                Semantic_ir.Fun
                  ( [ Semantic_ir.PVar "__lg_cat_item" ],
                    apply "List.of_seq"
                      [
                        apply "Lg_runtime.Runtime_dynamic.to_seq"
                          [ Semantic_ir.Ident "__lg_cat_item" ];
                      ] );
                outer;
              ] ]
      in
      into target
        (typed_ir (TList (Types.dynamic_constraint TUnknown)) flattened)
  | Ok _ ->
      Error.error "into cat source elements must be collections"

let compile name args =
  match (name, args) with
  | "remove", [ fn; collection ] -> remove fn collection
  | ("take-while" | "drop-while"), [ fn; collection ] ->
      take_drop_while name fn collection
  | "sort", [ collection ] -> sort collection
  | "vec", [ collection ] -> vec collection
  | "set", [ collection ] -> set collection
  | "__lg_into", [ target; source ] -> into target source
  | "into-cat", [ target; source ] -> into_cat target source
  | "remove", _ -> Error.error "remove expects function and collection"
  | ("take-while" | "drop-while"), _ ->
      Error.error (name ^ " expects function and collection")
  | ("sort" | "vec" | "set"),
    _ -> Error.error (name ^ " expects 1 arguments")
  | "__lg_into", _ -> Error.error "into expects target and source collections"
  | _ -> Error.error ("unknown function " ^ name)
