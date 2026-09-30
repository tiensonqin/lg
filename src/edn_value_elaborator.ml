open Types

let value_ty = TOcaml "Lg_edn_backend.t"
let is_value_type ty =
  Types.equal ty value_ty
  ||
  match ty with
  | TOcaml name -> (
      match Ocaml_signature.type_manifest name with
      | Ok manifest -> Types.equal manifest value_ty
      | Error _ -> false)
  | _ -> false
let optional_payload = function
  | TNullable ty | TOcaml_app ("option", [ ty ]) -> Some ty
  | _ -> None

let rec unwrap_shared_expression expression =
  match Semantic_ir.unlocated expression with
  | Semantic_ir.SharedValue (_, value) -> unwrap_shared_expression value
  | value -> value

let empty_list_expression expression =
  match unwrap_shared_expression expression with
  | Semantic_ir.List []
  | Semantic_ir.Ident "[]" ->
      true
  | _ -> false

let empty_vector_expression expression =
  match unwrap_shared_expression expression with
  | Semantic_ir.Ident ("Rrbvec.empty" | "V.empty") -> true
  | _ -> false

let empty_set_expression expression =
  match unwrap_shared_expression expression with
  | Semantic_ir.Ident
      ( "Lg_runtime.Runtime_poly_set.empty"
      | "Lg_runtime.Runtime_map_set.empty"
      | "Set.empty" ) ->
      true
  | _ -> false

let empty_map_expression expression =
  match unwrap_shared_expression expression with
  | Semantic_ir.Ident
      ( "Lg_runtime.Runtime_map.empty" | "Lg_runtime.Lg_map.empty" | "M.empty" )
    ->
      true
  | Semantic_ir.Apply (Semantic_ir.Ident "Lg_runtime.Runtime_map.empty_like", _)
    ->
      true
  | _ -> false

let is_provably_empty_collection ty expression =
  match Types.constraint_value_type ty with
  | TNil -> true
  | TList _ -> empty_list_expression expression
  | TVector _ -> empty_vector_expression expression
  | TSet _ -> empty_set_expression expression
  | map_ty when Option.is_some (Types.dynamic_map_types map_ty) ->
      empty_map_expression expression
  | _ -> false

let is_literal_empty_collection ty expression =
  match (Types.constraint_value_type ty, unwrap_shared_expression expression) with
  | TNil, Semantic_ir.Constructor ("None", None) -> true
  | TList _, (Semantic_ir.List [] | Semantic_ir.Ident "[]") -> true
  | TVector _, Semantic_ir.Ident ("Rrbvec.empty" | "V.empty") -> true
  | ( TSet _,
      Semantic_ir.Ident
        ( "Lg_runtime.Runtime_poly_set.empty"
        | "Lg_runtime.Runtime_map_set.empty"
        | "Set.empty" ) ) ->
      true
  | ( map_ty,
      Semantic_ir.Ident
        ( "Lg_runtime.Runtime_map.empty" | "Lg_runtime.Lg_map.empty"
        | "M.empty" ) )
    when Option.is_some (Types.dynamic_map_types map_ty) ->
      true
  | _ -> false

let rec is_packable ty =
  match Types.constraint_value_type ty with
  | TOcaml "Lg_edn_backend.t" -> true
  | TNil | TBool | TInt | TFloat | TChar | TString | TSymbol | TKeyword
  | TRegex | TOcaml "int" ->
      true
  | TNullable inner | TOcaml_app ("option", [ inner ]) | TList inner
  | TSeq inner | TVector inner | TArray inner
  | TOcaml_app ("array", [ inner ]) | TSet inner ->
      is_packable inner
  | TTuple items -> List.for_all is_packable items
  | TRecord fields | TNamed_record { fields; nominal = false; _ } ->
      List.for_all (fun (field : field) -> is_packable field.ty) fields
  | map_ty -> (
      match Types.dynamic_map_types map_ty with
      | Some (key_ty, value_ty) -> is_packable key_ty && is_packable value_ty
      | None -> false)

let rec pack_expression ty expression =
  let convert name =
    Ok
      (Semantic_ir.Apply
         ( Semantic_ir.Ident ("Lg_runtime.Runtime_metadata." ^ name),
           [ expression ] ))
  in
  let constrained = Types.constraint_value_type ty in
  if
    match constrained with
    | TList (TUnknown | TMeta _ | TVar _) -> empty_list_expression expression
    | _ -> false
  then
    Ok
      (Semantic_ir.Constructor
         ("Lg_edn_backend.List", Some (Semantic_ir.Array [])))
  else if
    match constrained with
    | TVector (TUnknown | TMeta _ | TVar _) -> empty_vector_expression expression
    | _ -> false
  then
    Ok
      (Semantic_ir.Constructor
         ("Lg_edn_backend.Vector", Some (Semantic_ir.Array [])))
  else if
    match constrained with
    | TSet (TUnknown | TMeta _ | TVar _) -> empty_set_expression expression
    | _ -> false
  then
    Ok
      (Semantic_ir.Constructor
         ("Lg_edn_backend.Set", Some (Semantic_ir.Array [])))
  else if
    Option.is_some (Types.dynamic_map_types constrained)
    && empty_map_expression expression
  then
    Ok
      (Semantic_ir.Constructor
         ("Lg_edn_backend.Map", Some (Semantic_ir.Array [])))
  else
  match constrained with
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
  | TNullable inner | TOcaml_app ("option", [ inner ]) ->
      let value_name = "__lg_edn_optional_value" in
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
        (pack_expression inner (Semantic_ir.Ident value_name))
  | TList element_ty ->
      Result.map
        (fun convert ->
          Semantic_ir.Apply
            ( Semantic_ir.Ident "Lg_runtime.Runtime_metadata.of_list",
              [ convert; expression ] ))
        (mapper element_ty)
  | TSeq element_ty ->
      Result.map
        (fun convert ->
          Semantic_ir.Apply
            ( Semantic_ir.Ident "Lg_runtime.Runtime_metadata.of_seq",
              [ convert; expression ] ))
        (mapper element_ty)
  | TVector element_ty ->
      Result.map
        (fun convert ->
          Semantic_ir.Apply
            ( Semantic_ir.Ident "Lg_runtime.Runtime_metadata.of_vector",
              [ convert; expression ] ))
        (mapper element_ty)
  | TArray element_ty | TOcaml_app ("array", [ element_ty ]) ->
      Result.map
        (fun convert ->
          Semantic_ir.Apply
            ( Semantic_ir.Ident "Lg_runtime.Runtime_metadata.of_array",
              [ convert; expression ] ))
        (mapper element_ty)
  | TSet element_ty -> (
      match (mapper element_ty, Types.set_module_name element_ty) with
      | (Error _ as error), _ | _, (Error _ as error) -> error
      | Ok convert, Ok set_module ->
          Ok
            (Semantic_ir.Apply
               ( Semantic_ir.Ident "Lg_runtime.Runtime_metadata.of_set",
                 [
                   convert;
                   Semantic_ir.Apply
                     ( Semantic_ir.Ident (set_module ^ ".elements"),
                       [ expression ] );
                 ] )))
  | TTuple element_types ->
      let names =
        List.mapi
          (fun index _ -> "__lg_edn_tuple_value_" ^ string_of_int index)
          element_types
      in
      let pattern_names = names in
      let rec pack_values packed types names =
        match (types, names) with
        | [], [] ->
            Ok
              (Semantic_ir.Let
                 ( [
                     ( Semantic_ir.PTuple
                         (List.map (fun name -> Semantic_ir.PVar name) pattern_names),
                       expression );
                   ],
                   Semantic_ir.Constructor
                     ( "Lg_edn_backend.Vector",
                       Some (Semantic_ir.Array (List.rev packed)) ) ))
        | element_ty :: rest_types, name :: rest_names ->
            Result.bind
              (pack_expression element_ty (Semantic_ir.Ident name))
              (fun packed_value ->
                pack_values (packed_value :: packed) rest_types rest_names)
        | _ -> assert false
      in
      pack_values [] element_types names
  | (TRecord fields | TNamed_record { fields; nominal = false; _ }) as record_ty ->
      let source_name = "__lg_edn_record_value" in
      let source_expression, wrap =
        match Semantic_ir.unlocated expression with
        | Semantic_ir.Ident _ -> (expression, Fun.id)
        | _ ->
            ( Semantic_ir.Ident source_name,
              fun converted ->
                Semantic_ir.Let
                  ([ (Semantic_ir.PVar source_name, expression) ], converted) )
      in
      let source = typed_ir record_ty source_expression in
      let rec pack_entries entries = function
        | [] ->
            Ok
              (wrap
                 (Semantic_ir.Apply
                    ( Semantic_ir.Ident "Lg_runtime.Runtime_metadata.of_entries",
                      [ Semantic_ir.List (List.rev entries) ] )))
        | (field : field) :: rest ->
            let key =
              Semantic_ir.Apply
                ( Semantic_ir.Ident "Lg_runtime.Runtime_metadata.of_keyword",
                  [ Semantic_ir.String field.keyword ] )
            in
            Result.bind
              (pack_expression field.ty (Structural_map.field_expr source field))
              (fun value ->
                pack_entries (Semantic_ir.Tuple [ key; value ] :: entries) rest)
      in
      pack_entries [] fields
  | map_ty -> (
      match Types.dynamic_map_types map_ty with
      | Some (key_ty, value_ty) -> (
          match (mapper key_ty, mapper value_ty) with
          | (Error _ as error), _ | _, (Error _ as error) -> error
          | Ok key_mapper, Ok value_mapper ->
              Ok
                (Semantic_ir.Apply
                   ( Semantic_ir.Ident "Lg_runtime.Runtime_metadata.of_map",
                     [ key_mapper; value_mapper; expression ] )))
      | None ->
          Error.error ~code:Error_code.Semantic
            ("value cannot be represented as closed EDN: "
            ^ Types.source_name ty))

and mapper ty =
  let value_name = "__lg_edn_value" in
  Result.map
    (fun body -> Semantic_ir.Fun ([ Semantic_ir.PVar value_name ], body))
    (pack_expression ty (Semantic_ir.Ident value_name))

let map_entries_argument expected_element argument =
  if
    is_value_type argument.ty
    && match expected_element with TTuple [ _; _ ] -> true | _ -> false
  then
    typed_ir (TSeq (TTuple [ value_ty; value_ty ]))
      (Semantic_ir.Apply
         ( Semantic_ir.Ident "Lg_runtime.Runtime_edn.map_entries",
           [ argument.semantic_expr ] ))
  else argument

let map_entry_mapper ~pack_constrained expected_element actual_element =
  let rec decode expected expression =
    if Types.equal expected value_ty then Ok expression
    else if Option.is_some (Types.printable_constraint_info expected) then
      pack_constrained expected (typed_ir value_ty expression)
    else
      match expected with
      | TBool ->
          Ok
            (Semantic_ir.Apply
               ( Semantic_ir.Ident "Lg_runtime.Runtime_edn.bool_value",
                 [ expression ] ))
      | expected when Option.is_some (Types.record_fields expected) ->
          let fields = Types.record_fields expected |> Option.get in
          let rec decode_fields decoded = function
            | [] ->
                Ok
                  (Structural_map.record_expr fields (List.rev decoded)
                  |> fun value -> value.semantic_expr)
            | (field : field) :: rest ->
                let found =
                  Semantic_ir.Apply
                    ( Semantic_ir.Ident
                        "Lg_runtime.Runtime_edn.find_keyword",
                      [ Semantic_ir.String field.keyword; expression ] )
                in
                let value_name = "__lg_edn_field_value" in
                let decoded_field =
                  match optional_payload field.ty with
                  | Some inner ->
                      Result.map
                        (fun value ->
                          Semantic_ir.Match
                            ( found,
                              [
                                ( Semantic_ir.PConstructor ("None", None),
                                  Semantic_ir.Constructor ("None", None) );
                                ( Semantic_ir.PConstructor
                                    ( "Some",
                                      Some (Semantic_ir.PVar value_name) ),
                                  Semantic_ir.Constructor
                                    ("Some", Some value) );
                              ] ))
                        (decode inner (Semantic_ir.Ident value_name))
                  | None ->
                      decode field.ty
                        (Semantic_ir.Apply
                           (Semantic_ir.Ident "Option.get", [ found ]))
                in
                Result.bind decoded_field (fun value ->
                    decode_fields ((field, value) :: decoded) rest)
          in
          decode_fields [] fields
      | _ ->
          Error.error ~code:Error_code.Semantic
            ("EDN value cannot be decoded as " ^ Types.source_name expected)
  in
  match (actual_element, expected_element) with
  | ( TTuple [ actual_key; actual_value ],
      TTuple [ expected_key; expected_value ] )
    when is_value_type actual_key && is_value_type actual_value ->
      let key_name = "__lg_edn_map_key" in
      let value_name = "__lg_edn_map_value" in
      Result.bind (decode expected_key (Semantic_ir.Ident key_name))
        (fun key ->
          Result.map
            (fun value ->
              Some
                (Semantic_ir.Fun
                   ( [
                       Semantic_ir.PTuple
                         [
                           Semantic_ir.PVar key_name;
                           Semantic_ir.PVar value_name;
                         ];
                     ],
                     Semantic_ir.Tuple [ key; value ] )))
            (decode expected_value (Semantic_ir.Ident value_name)))
  | _ -> Ok None
