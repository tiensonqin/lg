open Types

let apply name args = Semantic_ir.Apply (Semantic_ir.Ident name, args)

let find_counted env receiver_ty =
  match Receiver_id.of_type receiver_ty with
  | None -> None
  | Some receiver ->
      (match
         Protocol_registry.find_implementation_or_default
           Core_protocols.counted_id Core_protocols.count_method_id receiver
           (Compiler_environment.protocols env)
       with
      | Some _ as implementation -> implementation
      | None -> (
          match Compiler_environment.protocol_evidence env with
          | Some evidence ->
              Protocol_registry.find_implementation_or_default
                Core_protocols.counted_id Core_protocols.count_method_id
                receiver evidence
          | None -> None))
      |> Option.map (fun (implementation : binding) ->
             {
               implementation with
               ty =
                 instantiate_receiver_method_type receiver_ty
                   implementation.ty;
             })

let identifier_holds_packed_constraint name =
  String.starts_with ~prefix:"__lg_constrained_argument" name
  || String.starts_with ~prefix:"__lg_erased_seqable_item" name
  || String.starts_with ~prefix:"__lg_erased_optional_value" name
  || String.starts_with ~prefix:"__lg_optional_seqable_value" name
  || String.starts_with ~prefix:"__lg_reduce_first" name
  || String.starts_with ~prefix:"__lg_erased_callback_arg_" name
  || String.starts_with ~prefix:"__lg_callback_argument_" name
  || String.starts_with ~prefix:"__lg_nullable_callback_arg_" name
  || String.starts_with ~prefix:"__lg_apply_argument_" name
  || String.starts_with ~prefix:"__lg_apply_head_" name
  || String.starts_with ~prefix:"__lg_apply_rest_item" name
  || String.starts_with ~prefix:"__lg_static_argument_" name
  || String.starts_with ~prefix:"__lg_erased_protocol_arg_" name

let rec constraint_value_expression ty expression =
  let unwrap value_ty =
    let expression =
      match Semantic_ir.unlocated expression with
      | Semantic_ir.Ident name
        when not (identifier_holds_packed_constraint name) ->
          expression
      | _ -> Semantic_ir.Apply (Semantic_ir.Ident "snd", [ expression ])
    in
    constraint_value_expression value_ty expression
  in
  match Types.seqable_constraint_info ty with
  | Some (_, _, value_ty) -> unwrap value_ty
  | None -> (
      match Types.capability_constraint_value ty with
      | Some value_ty -> unwrap value_ty
      | None -> expression)

let valid_ocaml_type_name name =
  String.length name > 0
  && not (String.contains name ':')
  && not (String.contains name '/')

let local_record_source_name name =
  let after separator name =
    match String.rindex_opt name separator with
    | Some index when index < String.length name - 1 ->
        String.sub name (index + 1) (String.length name - index - 1)
    | _ -> name
  in
  name |> after ':' |> after '/'

let canonicalize_record_name record =
  if valid_ocaml_type_name record.type_name then record
  else
    let local_name = local_record_source_name (Type_id.name record.type_id) in
    let type_name = Names.sanitize_name local_name in
    { record with type_name; set_module_name = "Set_" ^ type_name }

let find_canonical_record env source_name =
  let local_name = local_record_source_name source_name in
  let ocaml_name = Names.sanitize_name local_name in
  let records =
    Compiler_environment.filter_record_bindings
      (fun key (binding : binding) ->
        if String.starts_with ~prefix:"__record/" key then
          match binding.ty with
          | TNamed_record record
            when valid_ocaml_type_name record.type_name
                 && (String.equal record.type_name ocaml_name
                    || String.equal (Type_id.name record.type_id) local_name) ->
              Some record
          | _ -> None
        else None)
      env
    |> List.sort_uniq (fun left right ->
           Type_id.compare left.type_id right.type_id)
  in
  let same_fields left right =
    List.length left.fields = List.length right.fields
    && List.for_all2
         (fun left right ->
           String.equal left.keyword right.keyword
           && Types.equal left.ty right.ty)
         left.fields right.fields
  in
  let exact =
    List.filter (fun record -> String.equal record.type_name ocaml_name) records
  in
  match exact with
  | record :: rest when List.for_all (same_fields record) rest -> Some record
  | _ -> (
      match records with [ record ] -> Some record | _ -> None)

let rec resolve_host_record env = function
  | TNamed_record _ as ty -> ty
  | TOcaml name
    when String.starts_with ~prefix:Types.record_marker_prefix name ->
      resolve_host_record env
        (TCompiler
           (Named_record_marker
              (String.sub name
                 (String.length Types.record_marker_prefix)
                 (String.length name
                 - String.length Types.record_marker_prefix))))
  | TCompiler (Named_record_marker source_name) as ty ->
      let local_name =
        match String.rindex_opt source_name '/' with
        | None -> source_name
        | Some index ->
            String.sub source_name (index + 1)
              (String.length source_name - index - 1)
      in
      let records =
        Compiler_environment.filter_record_bindings
          (fun key (binding : binding) ->
            if String.starts_with ~prefix:"__record/" key then
              match binding.ty with
              | TNamed_record record
                when record.type_name = source_name
                     || Type_id.name record.type_id = source_name
                     || Type_id.name record.type_id = local_name ->
                  Some record
              | _ -> None
            else None)
          env
        |> List.filter (fun record -> valid_ocaml_type_name record.type_name)
        |> List.sort_uniq (fun left right ->
               let by_id = Type_id.compare left.type_id right.type_id in
               if by_id <> 0 then by_id
               else String.compare left.type_name right.type_name)
      in
      (match
         List.find_opt
           (fun record -> String.equal record.type_name source_name)
           records
       with
      | Some record -> TNamed_record (canonicalize_record_name record)
      | None -> (
          match records with
          | [ record ] -> TNamed_record (canonicalize_record_name record)
          | _ -> ty))
  | ty -> Type_inference_core.host_record_type ty |> Option.value ~default:ty

let rec resolve_callback_record env = function
  | TNamed_record record as ty -> (
      match find_canonical_record env (Type_id.name record.type_id) with
      | Some canonical when Type_id.equal canonical.type_id record.type_id ->
          TNamed_record canonical
      | Some _ | None -> ty)
  | TNullable inner -> TNullable (resolve_callback_record env inner)
  | TArray inner -> TArray (resolve_callback_record env inner)
  | TRef inner -> TRef (resolve_callback_record env inner)
  | TList inner -> TList (resolve_callback_record env inner)
  | TVector inner -> TVector (resolve_callback_record env inner)
  | TSet inner -> TSet (resolve_callback_record env inner)
  | TSeq inner -> TSeq (resolve_callback_record env inner)
  | TOcaml_app (name, arguments) ->
      TOcaml_app (name, List.map (resolve_callback_record env) arguments)
  | TTuple items -> TTuple (List.map (resolve_callback_record env) items)
  | TCompiler (Named_record_marker source_name) as ty ->
      (match find_canonical_record env source_name with
      | Some record -> TNamed_record record
      | None -> resolve_host_record env ty)
  | TCompiler marker ->
      TCompiler
        (Semantic_type.map_compiler_marker (resolve_callback_record env) marker)
  | TOcaml name as ty
    when String.starts_with ~prefix:Types.record_marker_prefix name ->
      let source_name =
        String.sub name
          (String.length Types.record_marker_prefix)
          (String.length name - String.length Types.record_marker_prefix)
      in
      (match find_canonical_record env source_name with
      | Some record -> TNamed_record record
      | None -> resolve_host_record env ty)
  | ty -> resolve_host_record env ty

let rec to_seq_expr env collection =
  let collection = { collection with ty = resolve_host_record env collection.ty } in
  let value_ty = Types.constraint_value_type collection.ty in
  let record_values_to_seq values =
    match values with
    | [] ->
        Ok
          ( TTuple [ TKeyword; TUnknown ],
            apply "List.to_seq" [ Semantic_ir.List [] ] )
    | ((first_field : Types.field), _) :: rest ->
        let value_ty = first_field.ty in
        if
          List.for_all
            (fun ((field : Types.field), _) ->
              Types.equal value_ty field.ty)
            rest
        then
          let entries =
            List.map
              (fun ((field : Types.field), value) ->
                Semantic_ir.Tuple [ Semantic_ir.String field.keyword; value ])
              values
          in
          Ok
            ( TTuple [ TKeyword; value_ty ],
              apply "List.to_seq" [ Semantic_ir.List entries ] )
        else
          Error.error ~code:Error_code.Type_mismatch
            ("map literal sequence has heterogeneous values: "
           ^ String.concat " | "
               (List.map
                  (fun ((field : Types.field), _) ->
                    Types.source_name field.ty)
                  values))
  in
  let record_fields_to_seq fields =
    match fields with
    | [] ->
        Ok
          ( TTuple [ TKeyword; TUnknown ],
            apply "List.to_seq" [ Semantic_ir.List [] ] )
    | (first_field : Types.field) :: rest ->
        let value_ty = first_field.ty in
        if
          List.for_all
            (fun (field : Types.field) -> Types.equal value_ty field.ty)
            rest
        then
          let entries =
            Structural_map.values_for collection fields
            |> List.map (fun ((field : Types.field), value) ->
                   Semantic_ir.Tuple [ Semantic_ir.String field.keyword; value ])
          in
          Ok
            ( TTuple [ TKeyword; value_ty ],
              apply "List.to_seq" [ Semantic_ir.List entries ] )
        else
          Error.error ~code:Error_code.Type_mismatch
            ("record map sequence has heterogeneous values: "
           ^ String.concat " | "
               (List.map
                  (fun (field : Types.field) -> Types.source_name field.ty)
                  fields))
  in
  if
    Option.is_none (Types.seqable_constraint_info collection.ty)
    && not (Types.equal value_ty collection.ty)
  then
    to_seq_expr env
      (typed_ir value_ty
         (constraint_value_expression collection.ty collection.semantic_expr))
  else if Types.is_dynamic collection.ty then
    let element_ty = Types.dynamic_constraint TUnknown in
    Ok
      ( element_ty,
        apply "Lg_runtime.Runtime_dynamic.to_seq" [ collection.semantic_expr ]
      )
  else
  match collection.ty with
  | TNil -> Ok (TUnknown, Semantic_ir.Ident "Seq.empty")
  | TChar when Compiler_environment.target env = Target.Melange ->
      Ok
        ( TChar,
          apply "List.to_seq"
            [ Semantic_ir.List [ collection.semantic_expr ] ] )
  | (TRecord _ | TNamed_record { nominal = false; _ }) -> (
      match collection.record_values with
      | Some values -> record_values_to_seq values
      | None -> (
          match collection.ty with
          | TRecord fields | TNamed_record { fields; _ } ->
              record_fields_to_seq fields
          | _ -> Error.error ~code:Error_code.Type_mismatch "record map value is not seqable"))
  | TOcaml_app ("Lg_runtime.Runtime_map.t", [ key_ty; value_ty ]) ->
      Ok
        ( TTuple [ key_ty; value_ty ],
          apply "Lg_runtime.Runtime_map.to_seq" [ collection.semantic_expr ] )
  | TTuple [ key_ty; value_ty ]
    when Types.equal key_ty value_ty
         || (match key_ty with TUnknown | TMeta _ | TVar _ -> true | _ -> false)
         || (match value_ty with TUnknown | TMeta _ | TVar _ -> true | _ -> false)
    ->
      let element_ty = Type_inference_core.refine_type key_ty value_ty in
      Ok
        ( element_ty,
          apply "List.to_seq"
            [
              Semantic_ir.List
                [
                  apply "fst" [ collection.semantic_expr ];
                  apply "snd" [ collection.semantic_expr ];
                ];
            ] )
  | TNullable value_ty | TOcaml_app ("option", [ value_ty ]) -> (
      let value_name = "__lg_optional_seqable_value" in
      let value = typed_ir value_ty (Semantic_ir.Ident value_name) in
        match to_seq_expr env value with
      | Error _ ->
          Error.error ~code:Error_code.Type_mismatch
            ("optional value is not seqable: " ^ Types.source_name value_ty)
      | Ok (element_ty, sequence) ->
          Ok
            ( element_ty,
              Semantic_ir.NullableToSeq
                {
                  source_ty = collection.ty;
                  element_ty;
                  conversion =
                    Semantic_ir.Match
                      ( collection.semantic_expr,
                        [
                          ( Semantic_ir.PConstructor ("None", None),
                            Semantic_ir.Ident "Seq.empty" );
                          ( Semantic_ir.PConstructor
                              ("Some", Some (Semantic_ir.PVar value_name)),
                            sequence );
                        ] );
                } ))
    | _ -> (
  match Types.next_seq_element collection.ty with
  | Some inner -> Ok (inner, collection.semantic_expr)
        | None -> (
  match Types.seqable_constraint_info collection.ty with
  | Some (constraint_kind, declared_inner, value_ty) -> (
      let inner =
        match declared_inner with
        | TUnknown | TMeta _ | TVar _ when Types.is_dynamic value_ty ->
            Types.dynamic_constraint TUnknown
        | _ -> declared_inner
      in
      match Semantic_ir.unlocated collection.semantic_expr with
      | Semantic_ir.Ident name
        when not (identifier_holds_packed_constraint name) ->
          let adapter =
            match constraint_kind with
            | `Required -> Semantic_ir.Ident (name ^ "__seq")
            | `Optional | `Optional_sequential ->
                let adapter_name = "__lg_seqable_adapter" in
                Semantic_ir.Match
                  ( Semantic_ir.Ident (name ^ "__seq_optional"),
                              [
                                ( Semantic_ir.PConstructor ("None", None),
                        Semantic_ir.Fun
                                    ( [ Semantic_ir.PAny ],
                                      Semantic_ir.Ident "Seq.empty" ) );
                      ( Semantic_ir.PConstructor
                                    ( "Some",
                                      Some (Semantic_ir.PVar adapter_name) ),
                        Semantic_ir.Ident adapter_name );
                    ] )
          in
          Ok
            ( inner,
                        Semantic_ir.Apply (adapter, [ collection.semantic_expr ])
                      )
      | _ ->
          let packed_name = "__lg_seqable_value" in
          let packed = Semantic_ir.Ident packed_name in
                    let value =
                      Semantic_ir.Apply (Semantic_ir.Ident "snd", [ packed ])
                    in
          let sequence =
            match constraint_kind with
            | `Required ->
                Semantic_ir.Apply
                  ( Semantic_ir.Apply
                      (Semantic_ir.Ident "fst", [ packed ]),
                    [ value ] )
            | `Optional | `Optional_sequential ->
                let adapter_name = "__lg_seqable_adapter" in
                Semantic_ir.Match
                            ( Semantic_ir.Apply
                                (Semantic_ir.Ident "fst", [ packed ]),
                              [
                                ( Semantic_ir.PConstructor ("None", None),
                        Semantic_ir.Ident "Seq.empty" );
                      ( Semantic_ir.PConstructor
                                    ( "Some",
                                      Some (Semantic_ir.PVar adapter_name) ),
                        Semantic_ir.Apply
                                    (Semantic_ir.Ident adapter_name, [ value ])
                                );
                    ] )
          in
          Ok
            ( inner,
              Semantic_ir.Let
                          ( [
                              ( Semantic_ir.PVar packed_name,
                                collection.semantic_expr );
                            ],
                  sequence ) ))
            | None -> (
                match
                  Core_protocols.find_seqable collection.ty
                    (Compiler_environment.protocols env)
                with
  | None -> (
      match
        Compiler_environment.find_optional_sequential_adapter collection.ty env
      with
      | None ->
          Error.error ~code:Error_code.Invalid_form
            ("collection value is not seqable: "
            ^ Types.source_name collection.ty)
      | Some (element_ty, adapter) ->
          let items_name = "__lg_optional_sequential_items" in
          Ok
            ( element_ty,
              Semantic_ir.Match
                ( apply adapter [ collection.semantic_expr ],
                  [
                    ( Semantic_ir.PConstructor ("None", None),
                      apply "Stdlib.invalid_arg"
                        [ Semantic_ir.String "value is not sequential" ] );
                    ( Semantic_ir.PConstructor
                        ("Some", Some (Semantic_ir.PVar items_name)),
                      apply "Rrbvec.to_seq"
                        [ Semantic_ir.Ident items_name ] );
                  ] ) ))
  | Some implementation -> (
                    match implementation.ty with
                    | TFn ([ receiver_ty ], TSeq element_ty)
                      when Types.assignable ~policy:Host_boundary
                             ~expected:receiver_ty ~actual:collection.ty ->
                        Ok
                          ( element_ty,
                            apply implementation.ocaml_name
                              [ collection.semantic_expr ] )
                    | _ -> (
                        match
                          Core_sequence_transform.collection_to_seq_expr
                            collection
                        with
                        | Ok sequence -> Ok sequence
                        | Error _ -> (
          match implementation.ty with
          | TFn ([ receiver_ty ], return_ty)
                          when Types.assignable ~policy:Host_boundary
                                 ~expected:receiver_ty ~actual:collection.ty ->
              if Types.equal return_ty collection.ty then
                Error.error ~code:Error_code.Type_mismatch
                  "Seqable/-seq implementation cannot return its receiver type"
              else
                to_seq_expr env
                  (typed_ir return_ty
                     (apply implementation.ocaml_name
                        [ collection.semantic_expr ]))
          | _ ->
              Error.error ~code:Error_code.Type_mismatch
                              "Seqable/-seq implementation must return a \
                               seqable value"))))))

let accepts_seqable env ty =
  Result.is_ok
    (to_seq_expr env (typed_ir ty (Semantic_ir.Ident "__lg_seqable_probe")))

let accepts_contains = function
  | TSet _ | TVector _ | TMap_keys | TRecord _ | TNamed_record _ -> true
  | ty when Option.is_some (Types.dynamic_map_types ty) -> true
  | ty -> Option.is_some (Types.contains_constraint_info ty)

let contains_adapter ?key_ty argument =
  let key_name = "__lg_contains_key" in
  let key = Semantic_ir.Ident key_name in
  let witness body =
    Ok (Semantic_ir.Fun ([ Semantic_ir.PVar key_name ], body))
  in
  let key_ty =
    match key_ty with
    | Some _ as key_ty -> key_ty
    | None ->
        Option.map fst (Types.contains_constraint_info argument.ty)
  in
  match Types.contains_constraint_info argument.ty with
  | Some _ -> (
      match Semantic_ir.unlocated argument.semantic_expr with
      | Semantic_ir.Ident name
        when not (identifier_holds_packed_constraint name) ->
          Ok (Semantic_ir.Ident (name ^ "__contains"))
      | _ ->
          Ok
            (Semantic_ir.Apply
               (Semantic_ir.Ident "fst", [ argument.semantic_expr ])))
  | None -> (
      match argument.ty with
      | TSet element_ty ->
          Result.bind (Types.set_module_name element_ty) (fun set_module ->
              witness
                (apply (set_module ^ ".mem")
                   [ key; argument.semantic_expr ]))
      | TVector _ ->
          witness
            (Semantic_ir.Infix
               ( "&&",
                 Semantic_ir.Infix (">=", key, Semantic_ir.Int 0),
                 Semantic_ir.Infix
                   ( "<",
                     key,
                     apply "Rrbvec.length" [ argument.semantic_expr ] ) ))
      | TMap_keys ->
          witness
            (apply "Lg_runtime.Core_set.String_set.mem"
               [ key; argument.semantic_expr ])
      | TRecord fields | TNamed_record { fields; _ } ->
          let keys =
            fields
            |> List.map (fun (field : field) ->
                   Semantic_ir.String field.keyword)
            |> fun keys ->
            apply "Lg_runtime.Core_set.String_set.of_list"
              [ Semantic_ir.List keys ]
          in
          witness
            (apply "Lg_runtime.Core_set.String_set.mem" [ key; keys ])
      | TOcaml "Lg_edn_backend.t" -> (
          let packed_key =
            match key_ty with
            | Some (TOcaml "Lg_edn_backend.t") -> Some key
            | Some TNil ->
                Some (Semantic_ir.Ident "Lg_runtime.Runtime_metadata.nil")
            | Some TBool ->
                Some (apply "Lg_runtime.Runtime_metadata.of_bool" [ key ])
            | Some TInt ->
                Some (apply "Lg_runtime.Runtime_metadata.of_int" [ key ])
            | Some TFloat ->
                Some (apply "Lg_runtime.Runtime_metadata.of_float" [ key ])
            | Some TString ->
                Some (apply "Lg_runtime.Runtime_metadata.of_string" [ key ])
            | Some TChar ->
                Some (apply "Lg_runtime.Runtime_metadata.of_char" [ key ])
            | Some TSymbol ->
                Some (apply "Lg_runtime.Runtime_metadata.of_symbol" [ key ])
            | Some TKeyword ->
                Some (apply "Lg_runtime.Runtime_metadata.of_keyword" [ key ])
            | Some TRegex ->
                Some (apply "Lg_runtime.Runtime_metadata.of_regex" [ key ])
            | Some _ | None -> None
          in
          match packed_key with
          | Some packed_key ->
              witness
                (apply "Lg_runtime.Runtime_edn.contains"
                   [ argument.semantic_expr; packed_key ])
          | None ->
              Error.error ~code:Error_code.Type_mismatch
                "contains? cannot encode the key as a closed EDN value")
      | map_ty when Option.is_some (Types.dynamic_map_types map_ty) ->
          let key_ty, _ = Option.get (Types.dynamic_map_types map_ty) in
          let operation =
            if Types.is_dynamic key_ty then
              "Lg_runtime.Runtime_map.mem_dynamic"
            else if Option.is_some (Types.dynamic_map_types key_ty) then
              "Lg_runtime.Runtime_map.mem_map_key"
            else "Lg_runtime.Runtime_map.mem"
          in
          witness
            (apply operation [ argument.semantic_expr; key ])
      | ty ->
          Error.error ~code:Error_code.Arity
            ("contains? expects a map, set, or vector, got "
           ^ Types.source_name ty))

let contains_expr target key =
  match Types.contains_constraint_info target.ty with
  | None -> None
  | Some (expected_key, _) ->
      if
        not
          (Types.assignable ~policy:Host_boundary ~expected:expected_key
             ~actual:key.ty)
      then Some (Error.error ~code:Error_code.Type_mismatch "contains? key type does not match collection")
      else
        Some
          (Result.map
             (fun adapter ->
               typed_ir TBool
                 (Semantic_ir.Apply (adapter, [ key.semantic_expr ])))
             (contains_adapter target))

let element_type env collection =
  match to_seq_expr env collection with
  | Ok (inner, _) -> Some inner
  | Error _ -> None

let element_type_of_ty env ty =
  element_type env
    (typed_ir ty (Semantic_ir.Ident "__lg_seqable_type_probe"))

let seq_expr env collection =
  match to_seq_expr env collection with
  | Error _ ->
      Error.error ~code:Error_code.Arity
        ("seq expects a seqable value, got " ^ Types.source_name collection.ty)
  | Ok (inner, sequence) ->
      let sequence_type =
        match (Compiler_environment.target env, collection.ty) with
        | Target.Melange, TVector _ -> Types.reversible_next_seq inner
        | _ -> Types.next_seq inner
      in
      Ok (typed_ir sequence_type sequence)

let rest_expr env collection =
  match to_seq_expr env collection with
  | Error _ -> Error.error ~code:Error_code.Arity "rest expects a seqable value"
  | Ok (inner, sequence) ->
      Ok
        (typed_ir (TSeq inner)
           (apply "Lg_runtime.Runtime_seq.drop" [ Semantic_ir.Int 1; sequence ]))

let next_expr env collection =
  match to_seq_expr env collection with
  | Error _ -> Error.error ~code:Error_code.Arity "next expects a seqable value"
  | Ok (inner, sequence) ->
      Ok
        (typed_ir (Types.next_seq inner)
           (apply "Lg_runtime.Runtime_seq.drop" [ Semantic_ir.Int 1; sequence ]))

let second_expr env collection =
  match to_seq_expr env collection with
  | Error _ -> Error.error ~code:Error_code.Arity "second expects a seqable value"
  | Ok (inner, sequence) ->
      Ok (typed_ir inner (apply "Lg_runtime.Runtime_seq.second" [ sequence ]))

let drop_expr env name collection count =
  if not (Types.equal count.ty TInt) then
    Error.error ~code:Error_code.Type_mismatch (name ^ " count must be int")
  else
    match to_seq_expr env collection with
    | Error _ -> Error.error ~code:Error_code.Arity (name ^ " expects a seqable value")
    | Ok (inner, sequence) ->
        Ok
          (typed_ir (TSeq inner)
             (apply "Lg_runtime.Runtime_seq.drop"
                [ count.semantic_expr; sequence ]))

let seqable_adapter ?element_mapper env argument =
  let value_name = "seqable_value__" in
  let value = Semantic_ir.Ident value_name in
  let adapter =
    match Types.seqable_constraint_info argument.ty with
    | Some (constraint_kind, _, _) -> (
        match Semantic_ir.unlocated argument.semantic_expr with
        | Semantic_ir.Ident name
          when not (identifier_holds_packed_constraint name) ->
            let adapter =
              match constraint_kind with
              | `Required -> Semantic_ir.Ident (name ^ "__seq")
              | `Optional | `Optional_sequential ->
                  let adapter_name = "__lg_seqable_adapter" in
                  Semantic_ir.Match
                    ( Semantic_ir.Ident (name ^ "__seq_optional"),
                      [
                        ( Semantic_ir.PConstructor ("None", None),
                          Semantic_ir.Apply
                            ( Semantic_ir.Ident "invalid_arg",
                              [ Semantic_ir.String "value is not sequential" ]
                            ) );
                        ( Semantic_ir.PConstructor
                            ("Some", Some (Semantic_ir.PVar adapter_name)),
                          Semantic_ir.Ident adapter_name );
                      ] )
            in
            Ok adapter
        | _ ->
            let packed_name = "__lg_seqable_argument" in
            let packed = Semantic_ir.Ident packed_name in
            let adapter =
              match constraint_kind with
              | `Required ->
                  Semantic_ir.Apply (Semantic_ir.Ident "fst", [ packed ])
              | `Optional | `Optional_sequential ->
                  let adapter_name = "__lg_seqable_adapter" in
                  Semantic_ir.Match
                    ( Semantic_ir.Apply (Semantic_ir.Ident "fst", [ packed ]),
                      [
                        ( Semantic_ir.PConstructor ("None", None),
                          Semantic_ir.Apply
                            ( Semantic_ir.Ident "invalid_arg",
                              [ Semantic_ir.String "value is not sequential" ]
                            ) );
                        ( Semantic_ir.PConstructor
                            ("Some", Some (Semantic_ir.PVar adapter_name)),
                          Semantic_ir.Ident adapter_name );
                      ] )
            in
            Ok
              (Semantic_ir.Let
                 ( [ (Semantic_ir.PVar packed_name, argument.semantic_expr) ],
                   adapter )))
    | None
      when Types.equal argument.ty TUnknown
           || match argument.ty with TVar _ -> true | _ -> false ->
        Ok (Semantic_ir.Ident "Lg_runtime.Runtime_dynamic.to_seq")
    | None ->
        let parameter = typed_ir argument.ty value in
        to_seq_expr env parameter
        |> Result.map (fun (_, sequence) ->
               match Semantic_ir.unlocated sequence with
               | Semantic_ir.Apply (adapter, [ argument ]) -> (
                   match Semantic_ir.unlocated argument with
                   | Semantic_ir.Ident candidate
                     when String.equal candidate value_name ->
                       adapter
                   | _ ->
                       Semantic_ir.Fun
                         ([ Semantic_ir.PVar value_name ], sequence))
               | _ ->
                   Semantic_ir.Fun
                     ([ Semantic_ir.PVar value_name ], sequence))
  in
  match adapter with
  | Error _ as err -> err
  | Ok adapter ->
      let adapter =
        match element_mapper with
        | None -> adapter
        | Some mapper ->
            apply "Lg_runtime.Runtime_seq.map_adapter" [ mapper; adapter ]
      in
      Ok adapter

let pack_seqable_argument ?element_mapper env argument =
  seqable_adapter ?element_mapper env argument
  |> Result.map (fun adapter ->
         Semantic_ir.Tuple
           [
             adapter;
             constraint_value_expression argument.ty argument.semantic_expr;
           ])

let reduce_expr env ?(short_circuit = false) fn init collection sequence =
  if short_circuit then
    match collection.ty with
    | TList _ | TOcaml_app ("list", [ _ ]) ->
        apply "Lg_runtime.Runtime_reduced.fold_list"
          [ fn.semantic_expr; init.semantic_expr; collection.semantic_expr ]
    | TVector _ ->
        apply "Lg_runtime.Runtime_reduced.fold_vector"
          [ fn.semantic_expr; init.semantic_expr; collection.semantic_expr ]
    | TArray _ | TOcaml_app ("array", [ _ ]) ->
        apply "Lg_runtime.Runtime_reduced.fold_array"
          [ fn.semantic_expr; init.semantic_expr; collection.semantic_expr ]
    | TString ->
        apply "Lg_runtime.Runtime_reduced.fold_string"
          [ fn.semantic_expr; init.semantic_expr; collection.semantic_expr ]
    | TSeq _ | TOcaml_app (("Seq.t" | "Seq"), [ _ ]) ->
        apply "Lg_runtime.Runtime_reduced.fold_seq"
          [ fn.semantic_expr; init.semantic_expr; collection.semantic_expr ]
    | _ ->
        apply "Lg_runtime.Runtime_reduced.fold_seq"
          [ fn.semantic_expr; init.semantic_expr; sequence ]
  else
  let fallback () =
    apply "Lg_runtime.Runtime_seq.fold_left"
      [ fn.semantic_expr; init.semantic_expr; sequence ]
  in
  match
    Core_protocols.find_reducible collection.ty
      (Compiler_environment.protocols env)
  with
  | None -> fallback ()
  | Some implementation -> (
      match collection.ty with
      | TList _ | TOcaml_app ("list", [ _ ]) ->
          apply "List.fold_left"
            [ fn.semantic_expr; init.semantic_expr; collection.semantic_expr ]
      | TVector _ ->
          apply "Rrbvec.fold_left"
            [ fn.semantic_expr; init.semantic_expr; collection.semantic_expr ]
      | TSet inner -> (
          match Types.set_module_name inner with
          | Error _ -> fallback ()
          | Ok set_module ->
              let item_name = "__lg_set_fold_item" in
              let accumulator_name = "__lg_set_fold_accumulator" in
              let item = Semantic_ir.Ident item_name in
              let accumulator = Semantic_ir.Ident accumulator_name in
              let reducer =
                Semantic_ir.Fun
                    ( [ Semantic_ir.PVar item_name;
                        Semantic_ir.PVar accumulator_name;
                      ],
                      Semantic_ir.Apply (fn.semantic_expr, [ accumulator; item ])
                    )
              in
              apply (set_module ^ ".fold")
                [ reducer; collection.semantic_expr; init.semantic_expr ])
      | TArray _ | TOcaml_app ("array", [ _ ]) ->
          apply
            (match Compiler_environment.target env with
            | Target.Melange ->
                "Lg_runtime_melange.Runtime_array_melange.fold_left"
            | Target.Native | Target.Js_of_ocaml -> "Array.fold_left")
            [ fn.semantic_expr; init.semantic_expr; collection.semantic_expr ]
      | TString ->
          apply "String.fold_left"
            [ fn.semantic_expr; init.semantic_expr; collection.semantic_expr ]
      | TSeq _ | TOcaml_app (("Seq.t" | "Seq"), [ _ ]) ->
          apply "Seq.fold_left"
            [ fn.semantic_expr; init.semantic_expr; collection.semantic_expr ]
      | _ ->
          apply implementation.ocaml_name
              [ collection.semantic_expr; fn.semantic_expr; init.semantic_expr ]
        )

let rec count_expr env collection =
  let of_host_int expression = expression in
  match collection.ty with
  | TNullable inner | TOcaml_app ("option", [ inner ]) ->
      let value_name = "__lg_counted_value" in
      let value = typed_ir inner (Semantic_ir.Ident value_name) in
      Result.map
        (fun present ->
          Semantic_ir.Match
            ( collection.semantic_expr,
              [
                ( Semantic_ir.PConstructor ("None", None),
                  Semantic_ir.Int 0 );
                ( Semantic_ir.PConstructor
                    ("Some", Some (Semantic_ir.PVar value_name)),
                  present );
              ] ))
        (count_expr env value)
  | TOcaml_app ("Lg_runtime.Runtime_transient.vector", [ _ ]) ->
      Ok
        (of_host_int
           (apply "Lg_runtime.Runtime_transient.vector_count"
              [ collection.semantic_expr ]))
  | TOcaml_app ("Lg_runtime.Runtime_transient.map", [ _; _ ]) ->
      Ok
        (of_host_int
           (apply "Lg_runtime.Runtime_transient.map_count"
              [ collection.semantic_expr ]))
  | TOcaml_app ("Lg_runtime.Runtime_transient.set", [ _ ]) ->
      Ok
        (of_host_int
           (apply "Lg_runtime.Runtime_transient.set_count"
              [ collection.semantic_expr ]))
  | _ ->
  match find_counted env collection.ty with
  | Some implementation ->
      Ok
        (match collection.ty with
        | TList _ | TOcaml_app ("list", [ _ ]) ->
            of_host_int (apply "List.length" [ collection.semantic_expr ])
        | TVector _ ->
            of_host_int (apply "Rrbvec.length" [ collection.semantic_expr ])
        | TSet inner -> (
            match Types.set_module_name inner with
            | Ok set_module ->
                of_host_int
                  (apply (set_module ^ ".cardinal")
                     [ collection.semantic_expr ])
            | Error _ ->
                apply implementation.ocaml_name [ collection.semantic_expr ])
        | TArray _ | TOcaml_app ("array", [ _ ]) ->
            of_host_int (apply "Array.length" [ collection.semantic_expr ])
        | TString ->
            of_host_int (apply "String.length" [ collection.semantic_expr ])
        | _ -> apply implementation.ocaml_name [ collection.semantic_expr ])
  | None -> (
      match to_seq_expr env collection with
      | Ok (_, sequence) ->
          Ok (of_host_int (apply "Seq.length" [ sequence ]))
      | Error _ ->
          Error.error ~code:Error_code.Arity
            ("count expects a counted or seqable value, got "
           ^ Types.source_name collection.ty))

let is_counted env collection =
  find_counted env collection.ty |> Option.is_some

let first_expr env collection =
  match to_seq_expr env collection with
  | Error _ -> Error.error ~code:Error_code.Arity "first expects a seqable value"
    | Ok (inner, sequence) ->
      let expression =
        if Types.is_dynamic inner then
          let item_name = "__lg_first_item" in
          Semantic_ir.Match
            ( apply "Lg_runtime.Runtime_seq.first_opt" [ sequence ],
              [
                ( Semantic_ir.PConstructor ("None", None),
                  Semantic_ir.Ident "Lg_runtime.Runtime_dynamic.nil" );
                ( Semantic_ir.PConstructor
                    ("Some", Some (Semantic_ir.PVar item_name)),
                  Semantic_ir.Ident item_name );
              ] )
        else
          let optional expression =
            Semantic_ir.Constructor ("Some", Some expression)
          in
          match collection.ty with
          | TList _ | TOcaml_app ("list", [ _ ]) ->
              let head_name = "__lg_first_list_item" in
              Semantic_ir.Match
                ( collection.semantic_expr,
                  [
                    ( Semantic_ir.PList [],
                      Semantic_ir.Constructor ("None", None) );
                    ( Semantic_ir.PCons
                        (Semantic_ir.PVar head_name, Semantic_ir.PAny),
                      optional (Semantic_ir.Ident head_name) );
                  ] )
          | TVector _ -> apply "Rrbvec.peek_front" [ collection.semantic_expr ]
          | TSet element -> (
              match Types.set_module_name element with
              | Ok set_module ->
                  Semantic_ir.If
                    ( apply (set_module ^ ".is_empty")
                        [ collection.semantic_expr ],
                      Semantic_ir.Constructor ("None", None),
                      optional
                        (apply (set_module ^ ".min_elt")
                           [ collection.semantic_expr ]) )
              | Error _ ->
                  apply "Lg_runtime.Runtime_seq.first_opt" [ sequence ])
          | TArray _ | TOcaml_app ("array", [ _ ]) ->
              Semantic_ir.If
                ( Semantic_ir.Infix
                    ( "=",
                      apply "Array.length" [ collection.semantic_expr ],
                      Semantic_ir.Int 0 ),
                  Semantic_ir.Constructor ("None", None),
                  optional
                    (apply "Array.get"
                       [ collection.semantic_expr; Semantic_ir.Int 0 ]) )
          | TString ->
              Semantic_ir.If
                ( Semantic_ir.Infix
                    ( "=",
                      apply "String.length" [ collection.semantic_expr ],
                      Semantic_ir.Int 0 ),
                  Semantic_ir.Constructor ("None", None),
                  optional
                    (apply "String.get"
                       [ collection.semantic_expr; Semantic_ir.Int 0 ]) )
          | TSeq _ | TOcaml_app (("Seq.t" | "Seq"), [ _ ]) ->
              apply "Lg_runtime.Runtime_seq.first_opt"
                [ collection.semantic_expr ]
          | _ -> apply "Lg_runtime.Runtime_seq.first_opt" [ sequence ]
      in
      let expression, return_ty =
        if Types.is_dynamic inner then (expression, inner)
        else
          match inner with
          | TNullable _ | TOcaml_app ("option", [ _ ]) ->
              ( apply "Option.join" [ expression ],
                Types.normalize_nullable inner )
          | _ -> (expression, TNullable inner)
      in
      Ok (typed_ir return_ty expression)

let last_expr env collection =
  match to_seq_expr env collection with
  | Error _ -> Error.error ~code:Error_code.Arity "last expects a seqable value"
  | Ok (inner, sequence) ->
      let last_index length =
        Semantic_ir.Infix ("-", length, Semantic_ir.Int 1)
      in
      if Types.is_dynamic inner then
        let item_name = "__lg_last_item" in
        Ok
          (typed_ir inner
             (Semantic_ir.Match
                ( apply "Lg_runtime.Runtime_seq.last_opt" [ sequence ],
                  [
                    ( Semantic_ir.PConstructor ("None", None),
                      Semantic_ir.Ident "Lg_runtime.Runtime_dynamic.nil" );
                    ( Semantic_ir.PConstructor
                        ("Some", Some (Semantic_ir.PVar item_name)),
                      Semantic_ir.Ident item_name );
                  ] )))
      else
        let optional expression =
          Semantic_ir.Constructor ("Some", Some expression)
        in
        let expression =
          match collection.ty with
          | TList _ | TOcaml_app ("list", [ _ ]) ->
              apply "Lg_runtime.Runtime_seq.last_opt" [ sequence ]
          | TVector _ -> apply "Rrbvec.peek_back" [ collection.semantic_expr ]
          | TSet element -> (
              match Types.set_module_name element with
              | Ok set_module ->
                  Semantic_ir.If
                    ( apply (set_module ^ ".is_empty")
                        [ collection.semantic_expr ],
                      Semantic_ir.Constructor ("None", None),
                      optional
                        (apply (set_module ^ ".max_elt")
                           [ collection.semantic_expr ]) )
              | Error _ ->
                  apply "Lg_runtime.Runtime_seq.last_opt" [ sequence ])
          | TArray _ | TOcaml_app ("array", [ _ ]) ->
              let length = apply "Array.length" [ collection.semantic_expr ] in
              Semantic_ir.If
                ( Semantic_ir.Infix ("=", length, Semantic_ir.Int 0),
                  Semantic_ir.Constructor ("None", None),
                  optional
                    (apply "Array.get"
                       [ collection.semantic_expr; last_index length ]) )
          | TString ->
              let length = apply "String.length" [ collection.semantic_expr ] in
              Semantic_ir.If
                ( Semantic_ir.Infix ("=", length, Semantic_ir.Int 0),
                  Semantic_ir.Constructor ("None", None),
                  optional
                    (apply "String.get"
                       [ collection.semantic_expr; last_index length ]) )
          | TSeq _ | TOcaml_app (("Seq.t" | "Seq"), [ _ ]) ->
              apply "Lg_runtime.Runtime_seq.last_opt"
                [ collection.semantic_expr ]
          | _ -> apply "Lg_runtime.Runtime_seq.last_opt" [ sequence ]
        in
        Ok (typed_ir (TNullable inner) expression)

let nth_expr env collection index =
  let host_index = index.semantic_expr in
  match collection.ty with
  | TOcaml_app ("Lg_runtime.Runtime_transient.vector", [ inner ]) ->
      Ok
        (typed_ir inner
           (apply "Lg_runtime.Runtime_transient.vector_nth"
              [ collection.semantic_expr; host_index ]))
  | TOcaml "Lg_runtime.Runtime_string.regex_matcher" ->
      Ok
        (typed_ir (TNullable TString)
           (apply "Lg_runtime.Runtime_string.regex_matcher_nth"
              [ collection.semantic_expr; host_index ]))
  | _ ->
  let protocols = Compiler_environment.protocols env in
  match Core_protocols.find_indexed collection.ty protocols with
  | Some implementation -> (
      match collection.ty with
      | TList inner | TOcaml_app ("list", [ inner ]) ->
          Ok
            (typed_ir inner
               (apply "List.nth"
                  [ collection.semantic_expr; host_index ]))
      | TVector inner ->
          Ok
            (typed_ir inner
               (apply "Rrbvec.nth"
                  [ collection.semantic_expr; host_index ]))
      | TArray inner | TOcaml_app ("array", [ inner ]) ->
          Ok
            (typed_ir inner
               (apply "Array.get"
                  [ collection.semantic_expr; host_index ]))
      | TString ->
          Ok
            (typed_ir TChar
               (apply "String.get"
                  [ collection.semantic_expr; host_index ]))
      | _ -> (
          match implementation.ty with
          | TFn ([ receiver_ty; index_ty ], return_ty)
            when return_ty <> TUnknown
                 && Types.assignable ~policy:Host_boundary ~expected:receiver_ty
                      ~actual:collection.ty ->
              if
                not
                  (Types.assignable ~policy:Host_boundary ~expected:TInt
                     ~actual:index_ty)
              then Error.error ~code:Error_code.Type_mismatch "Indexed/-nth index parameter must be int"
              else
              Ok
                (typed_ir return_ty
                   (apply implementation.ocaml_name
                      [ collection.semantic_expr; index.semantic_expr ]))
          | _ ->
              Error.error ~code:Error_code.Type_mismatch
                "Indexed/-nth implementation must return a typed value"))
  | None -> (
      match collection.ty with
      | TSet _ -> Error.error ~code:Error_code.Arity "nth expects an indexed or sequential value"
      | _ -> (
          match to_seq_expr env collection with
          | Error _ -> Error.error ~code:Error_code.Arity "nth expects an indexed or sequential value"
          | Ok (inner, sequence) ->
              Ok
                (typed_ir inner
                   (apply "Lg_runtime.Runtime_seq.nth"
                      [ host_index; sequence ]))))
