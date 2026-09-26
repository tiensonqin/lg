open Types

let rec contains_unresolved_type = function
  | TPoly_variant row -> List.exists contains_unresolved_type (List.filter_map snd row.tags)
  | TUnknown | TMeta _ | TVar _ -> true
  | TNullable ty | TArray ty | TRef ty | TList ty | TVector ty | TSet ty
  | TSeq ty ->
      contains_unresolved_type ty
  | TOcaml_app (_, arguments) | TTuple arguments ->
      List.exists contains_unresolved_type arguments
  | TConstraint constraint_ ->
      List.exists contains_unresolved_type (constraint_children constraint_)
  | TFn (parameters, return_ty) ->
      List.exists contains_unresolved_type (return_ty :: parameters)
  | TOverloaded_fn arities ->
      List.exists
        (fun (arity : fn_arity) ->
          List.exists contains_unresolved_type
            (arity.return_ty :: arity.fixed_params)
          || Option.fold ~none:false ~some:contains_unresolved_type
               arity.rest_param)
        arities
  | TRecord fields ->
      List.exists
        (fun (field : field) -> contains_unresolved_type field.ty)
        fields
  | TNamed_record record ->
      List.exists contains_unresolved_type record.type_arguments
  | TInt | TFloat | TChar | TString | TRegex | TMap_keys | TSymbol | TKeyword
  | TBool | TUnit | TNil | TOcaml _ ->
      false

let validate_unique_keywords pairs =
  let rec loop seen = function
    | [] -> Ok ()
    | (keyword, _) :: rest ->
        if List.mem keyword seen then Error.error ("duplicate field " ^ keyword)
        else loop (keyword :: seen) rest
  in
  loop [] pairs

let record_type_application record =
  let type_name = Types.ocaml_record_type_name record.type_name in
  let argument_name = function
    | argument when contains_unresolved_type argument -> "_"
    | argument -> Types.ocaml_type_argument_name argument
  in
  match record.type_arguments with
  | [] -> type_name
  | [ argument ] -> argument_name argument ^ " " ^ type_name
  | arguments ->
      "(" ^ String.concat ", " (List.map argument_name arguments) ^ ") "
      ^ type_name

let record_projection_type record =
  let type_name = Types.ocaml_record_type_name record.type_name in
  match record.type_arguments with
  | [] -> type_name
  | [ _ ] -> "_ " ^ type_name
  | arguments ->
      "(" ^ String.concat ", " (List.map (Fun.const "_") arguments) ^ ") "
      ^ type_name

let field_expr target field =
  match target.record_values with
  | Some values -> (
      match
        List.find_opt
          (fun ((candidate : field), _) -> candidate.keyword = field.keyword)
          values
      with
      | Some (_, expression) -> expression
      | None -> Semantic_ir.Field (target.semantic_expr, field.ocaml_name))
  | None -> (
      match target.ty with
      | TRecord fields when Types.is_homogeneous_record fields ->
          Semantic_ir.Apply
            ( Semantic_ir.Ident "Lg_runtime.Runtime_map.get_exn",
              [ target.semantic_expr; Semantic_ir.String field.keyword ] )
      | TNamed_record record ->
          Semantic_ir.Field
            ( Semantic_ir.Constraint
                (target.semantic_expr, record_projection_type record),
              field.ocaml_name )
      | _ -> Semantic_ir.Field (target.semantic_expr, field.ocaml_name))

let values_for target fields =
  List.map (fun (field : field) -> (field, field_expr target field)) fields

let record_expr fields values =
  {
    ty = TRecord fields;
    semantic_expr =
      (if Types.is_homogeneous_record fields then
         Semantic_ir.annotate (TRecord fields)
           (Semantic_ir.Apply
              ( Semantic_ir.Ident "Lg_runtime.Runtime_map.of_list",
                [
                  Semantic_ir.List
                    (List.map
                       (fun ((field : field), value) ->
                         Semantic_ir.Tuple
                           [ Semantic_ir.String field.keyword; value ])
                       values);
                ] ))
       else
         match values with
         | [] -> Semantic_ir.Unit
         | _ ->
             Semantic_ir.annotate (TRecord fields)
               (Semantic_ir.Record
                  ( List.map
                      (fun ((field : field), value) ->
                        (field.ocaml_name, value))
                      values,
                    None )));
    record_values = Some values;
    return_param_index = None;
  }

let named_record_with_value_arguments record values =
  let value_type value =
    match Semantic_ir.type_annotations value with
    | ty :: _ -> Some ty
    | [] -> None
  in
  let rec argument_for parameter field_ty value_ty =
    match (field_ty, value_ty) with
    | TVar name, ty when name = parameter -> Some ty
    | (TUnknown | TMeta _ | TNil), ty when parameter = "a" -> Some ty
    | TNullable field_ty, TNullable value_ty
    | TArray field_ty, TArray value_ty
    | TRef field_ty, TRef value_ty
    | TList field_ty, TList value_ty
    | TVector field_ty, TVector value_ty
    | TSet field_ty, TSet value_ty
    | TSeq field_ty, TSeq value_ty ->
        argument_for parameter field_ty value_ty
    | TOcaml_app (_, field_args), TOcaml_app (_, value_args)
    | TTuple field_args, TTuple value_args
      when List.length field_args = List.length value_args ->
        let rec find = function
          | [], [] -> None
          | field_ty :: field_rest, value_ty :: value_rest -> (
              match argument_for parameter field_ty value_ty with
              | Some _ as result -> result
              | None -> find (field_rest, value_rest))
          | _ -> None
        in
        find (field_args, value_args)
    | _ -> None
  in
  let argument_for_value parameter ((field : field), value) =
    match value_type value with
    | None -> None
    | Some value_ty ->
        let value_ty =
          (* `field_expr` annotates a projection `(r : (_, _) record).f`
             with the record type, not the field type. Recover the
             field's actual type by instantiating field.ty with the
             projected record's arguments. *)
          match value_ty with
          | TNamed_record projected
            when String.equal projected.type_name record.type_name ->
              Types.instantiate_type
                ~templates:
                  (List.map (fun parameter -> TVar parameter)
                     record.type_parameters)
                ~actuals:projected.type_arguments field.ty
          | _ -> value_ty
        in
        argument_for parameter field.ty value_ty
  in
  if record.nominal || record.type_parameters = [] then record
  else
    let type_arguments =
      List.map2
        (fun parameter fallback ->
          values
          |> List.find_map (argument_for_value parameter)
          |> Option.value ~default:fallback)
        record.type_parameters record.type_arguments
    in
    { record with type_arguments }

let named_record_expr record values =
  let record = named_record_with_value_arguments record values in
  {
    ty = TNamed_record record;
    semantic_expr = Semantic_ir.annotate (TNamed_record record)
      (Semantic_ir.Record
        ( List.map
            (fun ((field : field), value) -> (field.ocaml_name, value))
            values,
          Some (record_type_application record) ));
    record_values = Some values;
    return_param_index = None;
  }

let as_named_record record target =
  named_record_expr record (values_for target record.fields)

let replace_field ?replacement_ty target fields keyword expression =
  let keyword =
    match find_field keyword fields with
    | Some field -> field.keyword
    | None -> keyword
  in
  let replacement_field (field : field) =
    match replacement_ty with
    | Some ty -> { field with ty }
    | None -> field
  in
  let replacement_values () =
    List.map
      (fun (field : field) ->
        if field.keyword = keyword then (replacement_field field, expression)
        else (field, field_expr target field))
      fields
  in
  let fields =
    List.map
      (fun (field : field) ->
        if field.keyword = keyword then replacement_field field else field)
      fields
  in
  match target.ty with
  | TRecord target_fields when Types.is_homogeneous_record target_fields ->
      typed_ir (TRecord fields)
        (Semantic_ir.Apply
           ( Semantic_ir.Ident "Lg_runtime.Runtime_map.assoc",
             [ target.semantic_expr; Semantic_ir.String keyword; expression ] ))
  | TNamed_record record -> named_record_expr record (replacement_values ())
  | _ -> record_expr fields (replacement_values ())

let extension_get target fields keyword =
  match Types.find_record_extension_field fields with
  | None -> None
  | Some field ->
      Some
        (typed_ir
           (Types.dynamic_constraint TUnknown)
           (Semantic_ir.Apply
              ( Semantic_ir.Ident "Lg_runtime.Runtime_map.get_default",
                [
                  field_expr target field;
                  Semantic_ir.String keyword;
                  Semantic_ir.Ident "Lg_runtime.Runtime_dynamic.nil";
                ] )))

let extension_assoc target fields keyword value =
  match Types.find_record_extension_field fields with
  | None -> None
  | Some field ->
      Some
        (replace_field target fields field.keyword
           (Semantic_ir.Apply
              ( Semantic_ir.Ident "Lg_runtime.Runtime_map.assoc",
                [
                  field_expr target field;
                  Semantic_ir.String keyword;
                  value;
                ] )))

let extension_with_record_metadata target fields keyword metadata =
  match Types.find_record_extension_field fields with
  | None -> None
  | Some field ->
      Some
        (replace_field target fields field.keyword
           (Semantic_ir.Apply
              ( Semantic_ir.Ident
                  "Lg_runtime.Runtime_map.with_record_metadata",
                [
                  field_expr target field;
                  Semantic_ir.String keyword;
                  metadata;
                ] )))

let extension_dissoc target fields keyword =
  match Types.find_record_extension_field fields with
  | None -> None
  | Some field ->
      Some
        (replace_field target fields field.keyword
           (Semantic_ir.Apply
              ( Semantic_ir.Ident "Lg_runtime.Runtime_map.dissoc",
                [ field_expr target field; Semantic_ir.String keyword ] )))

let extension_contains target fields keyword =
  match Types.find_record_extension_field fields with
  | None -> None
  | Some field ->
      Some
        (typed_ir TBool
           (Semantic_ir.Apply
              ( Semantic_ir.Ident "Lg_runtime.Runtime_map.mem",
                [ field_expr target field; Semantic_ir.String keyword ] )))

let unresolved_field (field : field) =
  match field.ty with TUnknown | TMeta _ | TVar _ -> true | _ -> false

let assoc target fields keyword value =
  match find_field keyword fields with
  | Some field
    when not
           (Types.equal field.ty value.ty
           || unresolved_field field
           || (Types.is_dynamic field.ty && Types.is_dynamic value.ty)
           || Types.assignable ~policy:Host_boundary ~expected:field.ty
                ~actual:value.ty)
    ->
      Error.error
        (Printf.sprintf "cannot assoc %s as %s because it is already %s" keyword
           (source_name value.ty) (source_name field.ty))
  | Some _ ->
      Ok (replace_field ~replacement_ty:value.ty target fields keyword value.semantic_expr)
  | None ->
      let runtime_map =
        fields <> []
        && List.for_all (fun (field : field) -> field.runtime_map) fields
      in
      let new_field = make_field ~runtime_map keyword value.ty in
      let old_fields = fields in
      let fields = old_fields @ [ new_field ] in
      if
        Types.is_homogeneous_record old_fields
        && Types.is_homogeneous_record fields
      then
        Ok
          (typed_ir (TRecord fields)
             (Semantic_ir.Apply
                ( Semantic_ir.Ident "Lg_runtime.Runtime_map.assoc",
                  [
                    target.semantic_expr;
                    Semantic_ir.String keyword;
                    value.semantic_expr;
                  ] )))
      else
        let values = values_for target old_fields in
        let values = values @ [ (new_field, value.semantic_expr) ] in
        Ok (record_expr fields values)

let rec assoc_many target pairs =
  match (target.ty, pairs) with
  | (TRecord _fields | TNamed_record { fields = _fields; _ }), [] -> Ok target
  | (TRecord fields | TNamed_record { fields; _ }), (keyword, value) :: rest -> (
      match assoc target fields keyword value with
      | Error _ as err -> err
      | Ok target -> assoc_many target rest)
  | _ -> Error.error "assoc expects a map"

let dissoc target fields keyword =
  match find_field keyword fields with
  | None -> Error.error ("cannot dissoc unknown field " ^ keyword)
  | Some removed
    when removed.runtime_map && List.length fields = 1 ->
      Ok
        (typed_ir (Types.dynamic_map TKeyword removed.ty)
           (Semantic_ir.Apply
              ( Semantic_ir.Ident "Lg_runtime.Runtime_map.dissoc",
                [ target.semantic_expr; Semantic_ir.String keyword ] )))
  | Some _ ->
      let target_is_runtime_map = Types.is_homogeneous_record fields in
      let fields =
        List.filter (fun (field : field) -> field.keyword <> keyword) fields
      in
      if target_is_runtime_map && Types.is_homogeneous_record fields then
        Ok
          (typed_ir (TRecord fields)
             (Semantic_ir.Apply
                ( Semantic_ir.Ident "Lg_runtime.Runtime_map.dissoc",
                  [ target.semantic_expr; Semantic_ir.String keyword ] )))
      else
        let values = values_for target fields in
        Ok (record_expr fields values)

let rec dissoc_many target keywords =
  match (target.ty, keywords) with
  | (TRecord _fields | TNamed_record { fields = _fields; _ }), [] -> Ok target
  | (TRecord fields | TNamed_record { fields; _ }), keyword :: rest -> (
      match dissoc target fields keyword with
      | Error _ as err -> err
      | Ok target -> dissoc_many target rest)
  | _ -> Error.error "dissoc expects a map"

let merge maps =
  let merge_one fields values right =
    match right.ty with
    | TRecord right_fields | TNamed_record { fields = right_fields; _ } ->
        let right_values = values_for right right_fields in
        let add_field (fields, values) (right_field : field) =
          match find_field right_field.keyword fields with
          | Some existing when not (Types.equal existing.ty right_field.ty) ->
              Error.error
                (Printf.sprintf "cannot merge %s as %s because it is already %s"
                   right_field.keyword (source_name right_field.ty)
                   (source_name existing.ty))
          | Some existing ->
              let values =
                values
                |> List.map (fun (field, expression) ->
                       if field.keyword = existing.keyword then
                         (field, List.assoc right_field right_values)
                       else (field, expression))
              in
              Ok (fields, values)
          | None ->
              Ok
                ( fields @ [ right_field ],
                  values @ [ (right_field, List.assoc right_field right_values) ] )
        in
        List.fold_left
          (fun acc field ->
            match acc with
            | Error _ as err -> err
            | Ok acc -> add_field acc field)
          (Ok (fields, values)) right_fields
    | _ -> Error.error "merge expects maps"
  in
  match maps with
  | [] -> Error.error "merge expects at least 1 map"
  | first :: rest -> (
      match first.ty with
      | TRecord fields | TNamed_record { fields; _ } -> (
          let values = values_for first fields in
          let result =
            List.fold_left
              (fun acc right ->
                match acc with
                | Error _ as err -> err
                | Ok (fields, values) -> merge_one fields values right)
              (Ok (fields, values)) rest
          in
          match result with
          | Error _ as err -> err
          | Ok (fields, values) ->
              let runtime_maps =
                Types.is_homogeneous_record fields
                && List.for_all
                     (fun map ->
                       match map.ty with
                       | TRecord map_fields ->
                           Types.is_homogeneous_record map_fields
                       | _ -> false)
                     maps
              in
              if runtime_maps then
                Ok
                  (typed_ir (TRecord fields)
                     (List.fold_left
                        (fun merged right ->
                          Semantic_ir.Apply
                            ( Semantic_ir.Ident "Lg_runtime.Runtime_map.merge",
                              [ merged; right.semantic_expr ] ))
                        first.semantic_expr rest))
              else Ok (record_expr fields values))
      | _ -> Error.error "merge expects maps")

let update_value target fields keyword value_ty value_expr =
  match find_field keyword fields with
  | None -> Error.error ("cannot update unknown field " ^ keyword)
  | Some field
    when not
           (Types.equal field.ty value_ty || unresolved_field field)
    ->
      Error.error
        (Printf.sprintf "cannot update %s as %s because it is already %s" keyword
           (source_name value_ty) (source_name field.ty))
  | Some _ ->
      Ok (replace_field target fields keyword value_expr)

let update_value_as target fields keyword value_ty value_expr =
  match find_field keyword fields with
  | None -> Error.error ("cannot update unknown field " ^ keyword)
  | Some field ->
      let keyword = field.keyword in
      let updated =
        {
          field with
          ty = value_ty;
          runtime_map = field.runtime_map || List.length fields = 1;
        }
      in
      let fields =
        List.map
          (fun (candidate : field) ->
            if candidate.keyword = keyword then updated else candidate)
          fields
      in
      let values =
        List.map
          (fun (field : field) ->
            if field.keyword = keyword then (field, value_expr)
            else (field, field_expr target field))
          fields
      in
      Ok (record_expr fields values)

let select_keys target fields keywords =
  if keywords = [] then Error.error "select-keys requires at least one key"
  else
    let rec collect acc = function
      | [] ->
          let selected = List.rev acc in
          let keyword_pairs =
            selected |> List.map (fun (field : field) -> (field.keyword, field))
          in
          validate_unique_keywords keyword_pairs
          |> Result.map (fun () ->
                 let values = values_for target selected in
                 record_expr selected values)
      | keyword :: rest -> (
          match find_field keyword fields with
          | Some field -> collect (field :: acc) rest
          | None -> collect acc rest)
    in
    collect [] keywords
