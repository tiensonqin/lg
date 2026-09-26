include Type_inference_core
open Ast
open Types

let literal_truthiness = function
  | FBool value -> Some value
  | FSymbol "nil" -> Some false
  | FInt _ | FFloat _ | FDecimal _ | FChar _ | FString _ | FRegex _
  | FKeyword _ ->
      Some true
  | FSymbol _ | FCoreSymbol _ | FList _ | FVector _ | FMap _ -> None

let optional_type = function
  | TNullable _ | TOcaml_app ("option", [ _ ]) -> true
  | _ -> false

let contextual_lookup_argument expected = function
  | FList ((FSymbol "__lg_get" | FCoreSymbol Core_get) :: _)
    when optional_type expected ->
      true
  | _ -> false

let builtin_poly_tag_payload_type = function
  | "String" -> Some TString
  | "Int" -> Some TInt
  | "Bool" -> Some TBool
  | "Float" -> Some TFloat
  | _ -> None

let rec stored_value_type ty =
  match Types.protocol_constraint_info ty with
  | Some (_, _, value_ty) -> stored_value_type value_ty
  | None -> ty

let static_seqable_element_type ty =
  match Types.constraint_value_type ty with
  | TList element_ty | TVector element_ty | TSet element_ty | TSeq element_ty
  | TArray element_ty ->
      Some element_ty
  | value_ty -> Types.seqable_constraint_element value_ty

let expected_seqable_element_type ty =
  match Types.seqable_constraint_element ty with
  | Some _ as element -> element
  | None -> static_seqable_element_type ty

let contextual_seqable_return_type expected_ty return_ty =
  match Types.seqable_constraint_element expected_ty with
  | None -> None
  | Some element_ty -> (
      match Types.constraint_value_type return_ty with
      | TList _ -> Some (TList element_ty)
      | TVector _ -> Some (TVector element_ty)
      | TSet _ -> Some (TSet element_ty)
      | TSeq _ -> Some (TSeq element_ty)
      | TArray _ -> Some (TArray element_ty)
      | _ -> None)

let static_sequential_element_type ty =
  match Types.constraint_value_type ty with
  | TList element_ty | TVector element_ty | TSeq element_ty ->
      Some element_ty
  | TConstraint
      (Seqable_constraint
        { requirement = Optional_sequential; element = element_ty; _ }) ->
      Some element_ty
  | _ -> None

let into_source_element_type ty =
  match Types.dynamic_map_types (Types.constraint_value_type ty) with
  | Some (key, value) -> Some (TTuple [ key; value ])
  | None -> (
      match ty with
      (* An empty keyword-map or open map target accepts any key-value
         pair entry; fresh metas let the source pin both sides. *)
      | TRecord [] | TMap_keys ->
          Some (TTuple [ Type_solver.fresh (); Type_solver.fresh () ])
      | _ -> static_seqable_element_type ty)

let nested_seqable_map_entry_type ty =
  Option.bind (Types.seqable_constraint_info ty)
    (fun (_, entry_ty, _) -> Types.seqable_constraint_element entry_ty)

let flatten_result_type collection_ty =
  match static_seqable_element_type collection_ty with
  | None -> TUnknown
  | Some item_ty -> (
      match static_sequential_element_type item_ty with
      | Some inner_ty -> TSeq inner_ty
      | None -> TSeq item_ty)

let record_field_type params receiver keyword =
  match string_assoc_opt receiver params with
  | None -> None
  | Some receiver_ty -> (
      let receiver_ty =
        host_record_type receiver_ty |> Option.value ~default:receiver_ty
      in
      match Types.record_fields receiver_ty with
      | None -> None
      | Some fields ->
          Option.map
            (fun (field : field) -> Expression_support.clj_function_type field.ty)
            (Types.find_field keyword fields))

let record_ref_field_value_type params receiver keyword =
  match record_field_type params receiver keyword with
  | Some (TRef value_ty) -> Some value_ty
  | Some _ | None -> None

let hinted_symbol_target resolve_named_record = function
  | FSymbol name -> Some (name, None)
  | FList [ FSymbol "__type-hint"; FSymbol annotation; FSymbol name ] -> (
      match Type_annotation.of_param_annotation annotation with
      | Ok hinted_ty -> Some (name, Some (resolve_named_record hinted_ty))
      | Error _ -> Some (name, None))
  | _ -> None

let hinted_target_name = function
  | FSymbol name -> Some name
  | FList [ FSymbol "__type-hint"; FSymbol _; FSymbol name ] -> Some name
  | _ -> None

let record_field_type_for_target params target keyword =
  match hinted_target_name target with
  | Some receiver -> record_field_type params receiver keyword
  | None -> None

let record_ref_field_value_type_for_target params target keyword =
  match hinted_target_name target with
  | Some receiver -> record_ref_field_value_type params receiver keyword
  | None -> None

let record_mutable_field_value_type params receiver keyword =
  match string_assoc_opt receiver params with
  | None -> None
  | Some receiver_ty -> (
      match Types.record_fields receiver_ty with
      | None -> None
      | Some fields -> (
          match Types.find_field keyword fields with
          | Some { mutable_ = true; ty; _ } -> Some ty
          | Some _ | None -> None))

let rec assoc_root_symbol = function
  | FSymbol name -> Some name
  | FList ((FSymbol "__lg_assoc" | FCoreSymbol Core_assoc) :: target :: _) ->
      assoc_root_symbol target
  | _ -> None

let constrain_seqable element_ty params name =
  let rec add_constraint = function
    | TUnknown | TMeta _ | TVar _ -> Types.seqable_constraint element_ty
    | TMap_keys ->
        Types.dynamic_map TKeyword (Types.dynamic_constraint TUnknown)
    | TRecord _ as map_ty ->
        Types.dynamic_constraint
          (Types.seqable_constraint_with_value
             (Types.seqable_constraint element_ty)
             map_ty)
    | TConstraint
        (Seqable_constraint
          ({ element = existing_element; _ } as constraint_)) ->
        let element_ty =
          if Types.equal existing_element TUnknown then element_ty
          else if Types.is_dynamic existing_element then existing_element
          else refine_type existing_element element_ty
        in
        TConstraint
          (Seqable_constraint { constraint_ with element = element_ty })
    | TNamed_record { type_parameters = [ parameter ]; _ } as record_ty ->
        Types.substitute_type_variables
          (Type_solver.of_list [ (Type_solver.Declared parameter, element_ty) ])
          record_ty
    | TVector existing_element ->
        TVector (refine_type existing_element element_ty)
    | TList existing_element ->
        TList (refine_type existing_element element_ty)
    | TSeq existing_element ->
        TSeq (refine_type existing_element element_ty)
    | TSet existing_element ->
        TSet (refine_type existing_element element_ty)
    | TArray existing_element ->
        TArray (refine_type existing_element element_ty)
    | existing when Option.is_some (Types.truthy_constraint_info existing) ->
        Types.truthy_constraint
          (add_constraint (Option.get (Types.truthy_constraint_info existing)))
    | existing
      when Option.is_some (Types.nil_predicate_constraint_info existing) ->
        Types.nil_predicate_constraint
          (add_constraint
             (Option.get (Types.nil_predicate_constraint_info existing)))
    | existing when Option.is_some (Types.printable_constraint_info existing) ->
        Types.printable_constraint
          (add_constraint
             (Option.get (Types.printable_constraint_info existing)))
    | existing
      when Option.is_some (Types.exception_data_constraint_info existing) ->
        Types.exception_data_constraint
          (add_constraint
             (Option.get (Types.exception_data_constraint_info existing)))
    | existing when Option.is_some (Types.hashable_constraint_info existing) ->
        Types.hashable_constraint
          (add_constraint
             (Option.get (Types.hashable_constraint_info existing)))
    | existing
      when Option.is_some (Types.comparable_constraint_info existing) ->
        Types.comparable_constraint
          (add_constraint
             (Option.get (Types.comparable_constraint_info existing)))
    | existing
      when Option.is_some (Types.array_index_constraint_info existing) ->
        Types.array_index_constraint
          (add_constraint
             (Option.get (Types.array_index_constraint_info existing)))
    | existing
      when Option.is_some (Types.symbol_predicate_constraint_info existing) ->
        Types.symbol_predicate_constraint
          (add_constraint
             (Option.get (Types.symbol_predicate_constraint_info existing)))
    | existing when Option.is_some (Types.contains_constraint_info existing) ->
        let key_ty, value_ty =
          Option.get (Types.contains_constraint_info existing)
        in
        Types.contains_constraint_with_value key_ty (add_constraint value_ty)
    | existing -> (
        match Types.protocol_constraint_info existing with
        | Some (_, _, value_ty) ->
            Types.protocol_constraint_with_value existing
              (add_constraint value_ty)
        | None -> existing)
  in
  match string_assoc_opt name params with
  | None -> Ok params
  | Some existing -> Ok (replace_param name (add_constraint existing) params)

let constrain_optional_sequential element_ty params name =
  let rec add_constraint = function
    | (TUnknown | TMeta _ | TVar _) as value_ty ->
        Types.optional_sequential_constraint element_ty (TNullable value_ty)
    | (TNullable _ | TOcaml_app ("option", [ _ ])) as value_ty ->
        Types.optional_sequential_constraint element_ty value_ty
    | existing -> (
        match Types.protocol_constraint_info existing with
        | Some (_, _, value_ty) ->
            Types.protocol_constraint_with_value existing
              (add_constraint value_ty)
        | None -> existing)
  in
  match string_assoc_opt name params with
  | None -> Ok params
  | Some existing -> Ok (replace_param name (add_constraint existing) params)

let constrain_contains key_ty params name =
  let rec add_constraint = function
    | TUnknown | TMeta _ | TVar _ -> Types.contains_constraint key_ty
    | existing -> (
        match Types.contains_constraint_info existing with
        | Some (existing_key, value_ty) ->
            Types.contains_constraint_with_value
              (refine_type existing_key key_ty)
              value_ty
        | None -> (
            match Types.protocol_constraint_info existing with
            | Some (_, _, value_ty) ->
                Types.protocol_constraint_with_value existing
                  (add_constraint value_ty)
            | None -> Types.contains_constraint_with_value key_ty existing))
  in
  match string_assoc_opt name params with
  | None -> Ok params
  | Some existing -> Ok (replace_param name (add_constraint existing) params)

let add_record_field_constraint name keyword field_ty params =
  let target_prefers_plain_storage =
    match string_assoc_opt name params with
    | Some ty
      when Option.is_some (Types.contains_constraint_info ty)
           || Option.is_some (Types.dynamic_map_types ty) ->
        true
    | Some (TOcaml_app ("Lg_runtime.Runtime_map.t", [ _; _ ])) -> true
    | Some _ | None -> false
  in
  let satisfies_field_constraint value constraint_ty =
    let payload =
      match Types.truthy_constraint_info constraint_ty with
      | Some _ as payload -> payload
      | None -> Types.nil_predicate_constraint_info constraint_ty
    in
    match payload with
    | Some payload -> Result.is_ok (Type_solver.unify Type_solver.empty payload value)
    | None -> (
        match value, Types.seqable_constraint_info constraint_ty with
        | TString, Some (_, element_ty, storage_ty) ->
            Result.bind (Type_solver.unify Type_solver.empty element_ty TChar)
              (fun substitutions -> Type_solver.unify substitutions storage_ty TString)
            |> Result.is_ok
        | _ -> false)
  in
  let merge_nested_fields fields inferred_fields =
    let rec same_open_shape left right =
      Types.equal left right
      ||
      match (left, right) with
      | (TUnknown | TMeta _ | TVar _), _
      | _, (TUnknown | TMeta _ | TVar _) ->
          true
      | left, right
        when Option.is_some (Types.seqable_constraint_info left)
             && Option.is_some (Types.seqable_constraint_info right) ->
          true
      | TNullable left, TNullable right
      | TNullable left, TOcaml_app ("option", [ right ])
      | TOcaml_app ("option", [ left ]), TNullable right ->
          same_open_shape left right
      | TArray left, TArray right
      | TRef left, TRef right
      | TList left, TList right
      | TVector left, TVector right
      | TSet left, TSet right
      | TSeq left, TSeq right ->
          same_open_shape left right
      | TOcaml_app (left_name, left_args), TOcaml_app (right_name, right_args) ->
          left_name = right_name
          && List.length left_args = List.length right_args
          && List.for_all2 same_open_shape left_args right_args
      | TConstraint left, TConstraint right ->
          Types.constraint_compatible
            (fun ~expected ~actual -> same_open_shape expected actual)
            left right
      | TTuple left, TTuple right ->
          List.length left = List.length right
          && List.for_all2 same_open_shape left right
      | _ -> false
    in
    let statically_seqable = function
      | TRecord _ | TNamed_record _ | TMap_keys | TSet _
      | TOcaml_app ("Lg_runtime.Runtime_map.t", [ _; _ ]) ->
          true
      | _ -> false
    in
    let merge_nested fields (inferred : field) =
      match find_field inferred.keyword fields with
      | None -> Ok (inferred :: fields)
      | Some existing when Types.equal existing.ty inferred.ty -> Ok fields
      | Some existing
        when (match existing.ty with
             | TUnknown | TMeta _ | TVar _ -> true
             | _ -> false) ->
          Ok
            (inferred
            :: List.filter
                 (fun field -> field.keyword <> inferred.keyword)
                 fields)
      | Some _
        when (match inferred.ty with
             | TUnknown | TMeta _ | TVar _ -> true
             | _ -> false) ->
          Ok fields
      | Some existing when satisfies_field_constraint existing.ty inferred.ty -> Ok fields
      | Some existing when satisfies_field_constraint inferred.ty existing.ty ->
          Ok (inferred :: List.filter (fun field -> field.keyword <> inferred.keyword) fields)
      | Some existing
        when inferred_row_compatible existing.ty inferred.ty
             || inferred_row_compatible inferred.ty existing.ty ->
          Ok
            ({ inferred with ty = refine_type existing.ty inferred.ty }
             :: List.filter (fun field -> field.keyword <> inferred.keyword) fields)
      | Some existing when same_open_shape existing.ty inferred.ty ->
          Ok
            ( { inferred with ty = refine_type existing.ty inferred.ty }
            :: List.filter
                 (fun field -> field.keyword <> inferred.keyword)
                 fields )
      | Some existing
        when statically_seqable existing.ty
             && Option.is_some
                  (Types.seqable_constraint_info inferred.ty) ->
          Ok fields
      | Some existing
        when statically_seqable inferred.ty
             && Option.is_some
                  (Types.seqable_constraint_info existing.ty) ->
          Ok
            (inferred
            :: List.filter
                 (fun field -> field.keyword <> inferred.keyword)
                 fields)
      | Some existing ->
          Error.error
            ("cannot infer " ^ inferred.keyword ^ " as "
           ^ Types.source_name inferred.ty ^ " because it is already "
            ^ Types.source_name existing.ty)
    in
    List.fold_left
      (fun result inferred ->
        Result.bind result (fun fields -> merge_nested fields inferred))
      (Ok fields) inferred_fields
  in
  let merge_fields fields =
    let runtime_map =
      match find_field keyword fields with
      | Some field -> field.runtime_map
      | None -> false
    in
    let make_constrained_field ty = make_field ~runtime_map keyword ty in
    let directly_seqable = function
      | TList _ | TVector _ | TSeq _ | TSet _
      | TOcaml_app ("Lg_runtime.Runtime_map.t", [ _; _ ]) ->
          true
      | _ -> false
    in
    let statically_printable = function
      | TInt | TFloat | TChar | TString | TRegex | TSymbol | TKeyword | TBool
      | TUnit | TNil | TOcaml "int" | TOcaml "Lg_edn_backend.t" ->
          true
      | _ -> false
    in
    let replace_field_type ty =
      Ok
        (make_constrained_field ty
        :: List.filter
             (fun candidate -> candidate.keyword <> keyword)
             fields)
    in
    match find_field keyword fields with
    | None -> Ok (make_constrained_field field_ty :: fields)
    | Some field when Types.equal field.ty field_ty -> Ok fields
    | Some field -> (
        match (field.ty, field_ty) with
        | (TUnknown | TMeta _ | TVar _), field_ty ->
            Ok
              (make_constrained_field field_ty
              :: List.filter
                   (fun candidate -> candidate.keyword <> keyword)
                   fields)
        | _, (TUnknown | TMeta _ | TVar _) -> Ok fields
        | existing, inferred when satisfies_field_constraint existing inferred -> Ok fields
        | existing, inferred when satisfies_field_constraint inferred existing ->
            replace_field_type inferred
        | existing, inferred
          when inferred_row_compatible existing inferred
               || inferred_row_compatible inferred existing ->
            replace_field_type (refine_type existing inferred)
        | existing, inferred
          when statically_printable existing
               && Option.is_some (Types.printable_constraint_info inferred) ->
            Ok fields
        | existing, inferred
          when Option.is_some (Types.printable_constraint_info existing)
               && statically_printable inferred ->
            replace_field_type inferred
        | TRef TUnknown, TRef value_ty ->
            Ok
              (make_constrained_field (TRef value_ty)
              :: List.filter
                   (fun candidate -> candidate.keyword <> keyword)
                   fields)
        | TRef _, TRef TUnknown -> Ok fields
        | ( TNullable (TRecord existing_fields),
            TNullable (TRecord inferred_fields) ) ->
            Result.bind
              (merge_nested_fields existing_fields inferred_fields)
              (fun nested_fields ->
                Ok
                  (make_constrained_field (TNullable (TRecord nested_fields))
                  :: List.filter
                       (fun candidate -> candidate.keyword <> keyword)
                       fields))
        | TRecord existing_fields, TNullable (TRecord inferred_fields) ->
            Result.map
              (fun nested_fields ->
                make_constrained_field (TNullable (TRecord nested_fields))
                :: List.filter
                     (fun candidate -> candidate.keyword <> keyword)
                     fields)
              (merge_nested_fields existing_fields inferred_fields)
        | TNullable (TRecord existing_fields), TRecord inferred_fields ->
            Result.map
              (fun nested_fields ->
                make_constrained_field (TNullable (TRecord nested_fields))
                :: List.filter
                     (fun candidate -> candidate.keyword <> keyword)
                     fields)
              (merge_nested_fields existing_fields inferred_fields)
        | TNamed_record _ as existing, TNullable (TRecord inferred_fields)
          when Types.row_compatible ~expected:(TRecord inferred_fields)
                 ~actual:existing ->
            replace_field_type (TNullable existing)
        | ( TNullable (TNamed_record _ as existing),
            (TRecord inferred_fields | TNullable (TRecord inferred_fields)) )
          when Types.row_compatible ~expected:(TRecord inferred_fields)
                 ~actual:existing ->
            Ok fields
        | existing, inferred
          when Types.is_dynamic existing || Types.is_dynamic inferred
               || Option.is_some (Types.protocol_constraint_info existing)
               || Option.is_some (Types.protocol_constraint_info inferred) ->
            Ok
              (make_constrained_field (refine_type existing inferred)
              :: List.filter
                   (fun candidate -> candidate.keyword <> keyword)
                   fields)
        | existing, inferred when same_refinable_wrapper existing inferred ->
            Ok
              (make_constrained_field (refine_type existing inferred)
              :: List.filter
                   (fun candidate -> candidate.keyword <> keyword)
                   fields)
        | (TNamed_record { type_parameters = [ parameter ]; _ } as existing),
          inferred
          when Option.is_some (Types.seqable_constraint_element inferred) ->
            let element_ty =
              Option.get (Types.seqable_constraint_element inferred)
            in
            Ok
              (make_constrained_field
                 (Types.substitute_type_variables
                    (Type_solver.of_list
                       [ (Type_solver.Declared parameter, element_ty) ])
                    existing)
              :: List.filter
                   (fun candidate -> candidate.keyword <> keyword)
                   fields)
        | ((TRecord _ | TNamed_record _) as existing), inferred
          when Option.is_some (Types.seqable_constraint_info inferred) ->
            Ok
              (make_constrained_field existing
              :: List.filter
                   (fun candidate -> candidate.keyword <> keyword)
                   fields)
        | concrete, seqable
          when directly_seqable concrete
               && Option.is_some (Types.seqable_constraint_info seqable) ->
            replace_field_type (refine_type concrete seqable)
        | seqable, concrete
          when directly_seqable concrete
               && Option.is_some (Types.seqable_constraint_info seqable) ->
            replace_field_type (refine_type concrete seqable)
        | existing, ((TRecord _ | TNamed_record _) as inferred)
          when Option.is_some (Types.seqable_constraint_info existing) ->
            Ok
              (make_constrained_field inferred
              :: List.filter
                   (fun candidate -> candidate.keyword <> keyword)
                   fields)
        | TMap_keys, inferred
          when Option.is_some (Types.seqable_constraint_info inferred) ->
            Ok
              (make_constrained_field (refine_type TMap_keys inferred)
              :: List.filter
                   (fun candidate -> candidate.keyword <> keyword)
                   fields)
        | existing, TMap_keys
          when Option.is_some (Types.seqable_constraint_info existing) ->
            Ok
              (make_constrained_field (refine_type existing TMap_keys)
              :: List.filter
                   (fun candidate -> candidate.keyword <> keyword)
                   fields)
        | _ ->
            Error.error
              ("cannot infer " ^ keyword ^ " as " ^ Types.source_name field_ty
             ^ " because it is already " ^ Types.source_name field.ty))
  in
  let rec add_constraint = function
    | TUnknown | TMeta _ | TVar _ ->
        Ok (TRecord [ make_field keyword field_ty ])
    | TMap_keys ->
        Ok
          (Types.dynamic_map TKeyword
             (Types.dynamic_constraint TUnknown))
    | existing when Option.is_some (Types.contains_constraint_info existing) ->
        let key_ty, value_ty =
          Types.contains_constraint_info existing |> Option.get
        in
        Result.map
          (Types.contains_constraint_with_value key_ty)
          (add_constraint value_ty)
    | TNullable inner ->
        Result.map (fun inner -> TNullable inner) (add_constraint inner)
    | TOcaml_app ("option", [ inner ]) ->
        Result.map
          (fun inner -> TOcaml_app ("option", [ inner ]))
          (add_constraint inner)
    | TRecord fields ->
        Result.map (fun fields -> TRecord fields) (merge_fields fields)
    | TNamed_record record as record_ty -> (
        let fields =
          Types.record_fields record_ty |> Option.value ~default:record.fields
        in
        match Types.find_field keyword fields with
        | None -> Ok record_ty
        | Some field -> (
            let constrained_parameters =
              Type_solver.variables field.ty
              |> List.filter (function
                   | Type_solver.Declared name ->
                       string_mem name record.type_parameters
                   | Type_solver.Metavariable _ -> false)
            in
            let inferred_ty =
              match
                (field.ty, Types.seqable_constraint_element field_ty)
              with
              | ( TNamed_record
                    { type_parameters = [ parameter ]; _ } as named,
                  Some element_ty ) ->
                  Types.substitute_type_variables
                    (Type_solver.of_list
                       [ (Type_solver.Declared parameter, element_ty) ])
                    named
              | (TRecord _ | TNamed_record _ | TMap_keys), Some _ ->
                  field.ty
              | _ -> stored_value_type field_ty
            in
            match (constrained_parameters, inferred_ty) with
            | [], inferred_ty
              when (match field.ty with
                   | TUnknown | TMeta _ | TVar _ -> true
                   | _ -> false)
                   &&
                   not
                     (match inferred_ty with
                     | TUnknown | TMeta _ | TVar _ -> true
                     | _ -> false) ->
                Result.map
                  (fun fields -> TNamed_record { record with fields })
                  (merge_fields record.fields)
            | [], _ -> Ok record_ty
            | _, (TUnknown | TMeta _ | TVar _) -> Ok record_ty
            | _,
              inferred_ty
              when (match field.ty with
                   | TOcaml_app ("Lg_runtime.Runtime_map.t", [ _; _ ]) ->
                       true
                   | _ -> false)
                   && Option.is_some
                        (Types.seqable_constraint_info inferred_ty) ->
                Ok record_ty
            | _, inferred_ty -> (
            let expected_ty =
              match Types.protocol_constraint_info field.ty with
              | Some (_, _, value_ty) -> value_ty
              | None -> field.ty
            in
            match Type_solver.unify Type_solver.empty expected_ty inferred_ty with
            | Ok substitutions ->
                Ok (Type_solver.apply substitutions record_ty)
            | Error _
              when (match field.ty with TNamed_record _ -> true | _ -> false)
                   && Types.row_compatible ~expected:field.ty
                        ~actual:
                          (match inferred_ty with
                          | TNullable ty -> ty
                          | ty -> ty) ->
                Ok record_ty
            | Error _ ->
                Error.error
                  ("cannot infer " ^ keyword ^ " as "
                 ^ Types.source_name inferred_ty ^ " because it is already "
                 ^ Types.source_name field.ty))))
    | ty when Option.is_some (Types.truthy_constraint_info ty) ->
        let value_ty = Types.truthy_constraint_info ty |> Option.get in
        let value_ty =
          match value_ty with
          | TNullable _ | TOcaml_app ("option", [ _ ]) -> value_ty
          | value_ty -> TNullable value_ty
        in
        if target_prefers_plain_storage then add_constraint value_ty
        else Result.map Types.truthy_constraint (add_constraint value_ty)
    | ty when Option.is_some (Types.nil_predicate_constraint_info ty) ->
        let value_ty = Types.nil_predicate_constraint_info ty |> Option.get in
        let value_ty =
          match value_ty with
          | TNullable _ | TOcaml_app ("option", [ _ ]) -> value_ty
          | value_ty -> TNullable value_ty
        in
        add_constraint value_ty
    | ty when Types.is_dynamic ty ->
        let capability =
          Types.dynamic_constraint_info ty |> Option.value ~default:TUnknown
        in
        Result.map Types.dynamic_constraint (add_constraint capability)
    | ty -> (
        match Types.protocol_constraint_info ty with
        | Some (_, _, value_ty) ->
            Result.map
              (Types.protocol_constraint_with_value ty)
              (add_constraint value_ty)
        | None -> Ok ty)
  in
  match string_assoc_opt name params with
  | None -> Ok params
  | Some existing_ty ->
      Result.map
        (fun ty -> replace_param name ty params)
        (add_constraint existing_ty)

let float_literal_type value =
  if String.contains value '/' then TOcaml "Lg_runtime.Runtime_ratio.t"
  else TFloat

let rec numeric_form_type params = function
  | FInt _ -> TInt
  | FFloat value -> float_literal_type value
  | FDecimal _ -> TOcaml "Lg_runtime.Runtime_decimal.t"
  | FSymbol name -> string_assoc_opt name params |> Option.value ~default:TUnknown
  | FList
      (FSymbol
         ( "__lg_add" | "__lg_subtract" | "__lg_multiply" | "__lg_max"
         | "__lg_min" )
      :: args)
    -> numeric_result_type params ~integer_result:TInt args
  | FList (FSymbol "__lg_divide" :: args) ->
      numeric_result_type params
        ~integer_result:(TOcaml "Lg_runtime.Runtime_ratio.t") args
  | FList (FSymbol "__lg_divide-melange" :: args) ->
      numeric_result_type params ~integer_result:TFloat args
  | FList [ FSymbol "__lg_abs"; value ] -> numeric_form_type params value
  | FList [ FSymbol "__lg_bigdec"; _ ] -> TFloat
  | FList [ FSymbol "__lg_bigint"; _ ] -> TInt
  | _ -> TUnknown

and numeric_result_type params ~integer_result args =
  let types = List.map (numeric_form_type params) args in
  if
    List.exists
      (Types.equal (TOcaml "Lg_runtime.Runtime_decimal.t"))
      types
  then TOcaml "Lg_runtime.Runtime_decimal.t"
  else if List.exists (Types.equal TFloat) types then TFloat
  else if
    List.exists
      (Types.equal (TOcaml "Lg_runtime.Runtime_ratio.t"))
      types
  then TOcaml "Lg_runtime.Runtime_ratio.t"
  else if List.exists (Types.equal TInt) types then integer_result
  else TUnknown

let rec inferred_form_type ?(lookup_binding = fun _ -> TUnknown) params = function
  | FInt _ -> TInt
  | FFloat value -> float_literal_type value
  | FDecimal _ -> TOcaml "Lg_runtime.Runtime_decimal.t"
  | FChar _ -> TChar
  | FString _ -> TString
  | FBool _ -> TBool
  | FSymbol "nil" -> TNil
  | FSymbol ("true" | "false") -> TBool
  | FList (FSymbol "tuple" :: items) ->
      TTuple (List.map (inferred_form_type ~lookup_binding params) items)
  | FList [ FSymbol "__lg_constantly"; result ] ->
      Types.constant_function (inferred_form_type ~lookup_binding params result)
  | FList (FSymbol "do" :: body_forms) -> (
      match List.rev body_forms with
      | result :: _ -> inferred_form_type ~lookup_binding params result
      | [] -> TNil)
  | FList [ FSymbol if_name; condition; then_form; else_form ]
    when has_source_name if_name "if" || has_source_name if_name "__lg_if" -> (
      match literal_truthiness condition with
      | Some true -> inferred_form_type ~lookup_binding params then_form
      | Some false -> inferred_form_type ~lookup_binding params else_form
      | None ->
          Expression_support.merge_branch_types
            (inferred_form_type ~lookup_binding params then_form)
            (inferred_form_type ~lookup_binding params else_form)
          |> Option.value ~default:TUnknown)
  | FList [ FSymbol if_name; _condition; then_form ]
    when has_source_name if_name "if" || has_source_name if_name "__lg_if" ->
      Expression_support.merge_branch_types
        (inferred_form_type ~lookup_binding params then_form)
        TNil
      |> Option.value ~default:TUnknown
  | FList (FSymbol "match" :: _target :: clauses) ->
      let rec result_types = function
        | _pattern :: result :: rest ->
            inferred_form_type ~lookup_binding params result :: result_types rest
        | [] | [ _ ] -> []
      in
      result_types clauses
      |> List.filter (fun ty ->
             match ty with TUnknown | TMeta _ | TVar _ -> false | _ -> true)
      |> (function
           | [] -> TUnknown
           | first :: rest ->
               List.fold_left
                 (fun merged ty ->
                   Expression_support.merge_branch_types merged ty
                   |> Option.value ~default:TUnknown)
                 first rest)
  | FKeyword _ -> TKeyword
  | FList [ FSymbol "#uuid"; FString _ ] ->
      TOcaml "Lg_runtime.Runtime_uuid.t"
  | FList [ FSymbol "#inst"; FString _ ] ->
      TOcaml "Lg_runtime.Runtime_instant.t"
  | FList
      [
        FSymbol ("quote" | "clojure.core/quote");
        FSymbol _;
      ] ->
      TSymbol
  | FList
      [
        FSymbol ("quote" | "clojure.core/quote");
        FList [];
      ] ->
      TList TUnknown
  | FList [ FSymbol ("__lg_atom" | "__lg_volatile!"); FVector [] ] ->
      TRef (TVector (Type_solver.fresh ()))
  | FList [ FSymbol ("__lg_atom" | "__lg_volatile!"); FSymbol "nil" ] ->
      TRef (TNullable TUnknown)
  | FList [ FSymbol "__lg_add-watch"; reference; _key; _callback ] ->
      inferred_form_type ~lookup_binding params reference
  | FList [ FSymbol "__lg_remove-watch"; reference; _key ] ->
      inferred_form_type ~lookup_binding params reference
  | FList [ FSymbol "__lg_reset-meta!"; _reference; _metadata ] ->
      TOcaml "Lg_edn_backend.t"
  | FList (FSymbol "delay" :: body_forms) -> (
      match List.rev body_forms with
      | result :: _ ->
          TOcaml_app ("Lazy.t", [ inferred_form_type ~lookup_binding params result ])
      | [] -> TOcaml_app ("Lazy.t", [ TUnknown ]))
  | FList
      [
        FSymbol "IDeref/-deref";
        FList [ FSymbol field_access; target ];
      ]
    when String.starts_with ~prefix:".-" field_access ->
      let keyword =
        ":" ^ String.sub field_access 2 (String.length field_access - 2)
      in
      record_ref_field_value_type_for_target params target keyword
      |> Option.value ~default:TUnknown
  | FList
      [ FSymbol "IDeref/-deref"; FList [ FKeyword keyword; FSymbol receiver ] ] ->
      record_ref_field_value_type params receiver keyword
      |> Option.value ~default:TUnknown
  | FList [ FSymbol "IDeref/-deref"; FSymbol reference ] -> (
      match string_assoc_opt reference params with
      | Some (TRef value_ty) -> value_ty
      | Some (TOcaml_app ("Lazy.t", [ value_ty ])) -> value_ty
      | Some _ | None -> TUnknown)
  | FSymbol name -> (
      match string_assoc_opt name params with
      | Some ty -> ty
      | None -> (
          match lookup_binding name with
          | TFn ([], result) when Expression_support.is_constructor_name name ->
              result
          | ty -> ty))
  | FList [ FSymbol field_access; target ]
    when String.starts_with ~prefix:".-" field_access ->
      let keyword =
        ":" ^ String.sub field_access 2 (String.length field_access - 2)
      in
      record_field_type_for_target params target keyword
      |> Option.value ~default:TUnknown
  | FList [ FKeyword keyword; FSymbol receiver ] ->
      record_field_type params receiver keyword
      |> Option.value ~default:TUnknown
  | FList
      (FSymbol
         ( "__lg_add" | "__lg_subtract" | "__lg_multiply" | "__lg_divide"
         | "__lg_divide-melange" | "__lg_max" | "__lg_min" )
      :: _)
    as form ->
      numeric_form_type params form
  | FList [ FSymbol "__lg_abs"; value ] -> numeric_form_type params value
  | FList [ FSymbol "__lg_ex-message"; _ ] -> TNullable TString
  | FList [ FSymbol "__lg_ex-cause"; _ ] -> TNullable (TOcaml "exn")
  | FList [ FSymbol "__lg_ex-data"; _ ] -> TOcaml "Lg_edn_backend.t"
  | FList [ FSymbol "__lg_exec-tap-fn"; _ ] -> TBool
  | FList [ FSymbol predicate; _ ] when has_source_name predicate "__lg_empty-predicate" ->
      TBool
  | FList [ FSymbol "__lg_add-tap"; _ ] -> TUnit
  | FList [ FSymbol "__lg_remove-tap"; _ ] -> TUnit
  | FList [ FSymbol "__lg_tap"; _ ] -> TBool
  | FList [ FSymbol "__lg_cljs-test-report"; _reporter; _event ] -> TUnit
  | FList [ FSymbol "__lg_multimethod-methods"; _multifn ] ->
      Types.dynamic_constraint TUnknown
  | FList [ FSymbol "__lg_multimethod-dispatch-fn"; _multifn ] ->
      Types.dynamic_constraint TUnknown
  | FList [ FSymbol "__lg_multimethod-get-method"; _multifn; _dispatch ] ->
      Types.dynamic_constraint TUnknown
  | FList [ FSymbol "__lg_multimethod-remove-method"; _multifn; _dispatch ] ->
      Types.dynamic_constraint TUnknown
  | FList [ FSymbol "__lg_multimethod-remove-all-methods"; _multifn ] ->
      Types.dynamic_constraint TUnknown
  | FList [ FSymbol "__lg_multimethod-default-dispatch-val"; _multifn ] ->
      Types.dynamic_constraint TUnknown
  | FList
      [
        FSymbol "__lg_multimethod-prefer-method";
        _multifn;
        _preferred;
        _other;
      ] ->
      Types.dynamic_constraint TUnknown
  | FList [ FSymbol "__lg_multimethod-prefers"; _multifn ] ->
      Types.dynamic_constraint TUnknown
  | FList [ FSymbol "__lg_re-pattern"; _ ] -> TRegex
  | FList [ FSymbol "__lg_re-matcher"; _; _ ] ->
      TOcaml "Lg_runtime.Runtime_string.regex_matcher"
  | FList [ FSymbol "__lg_re-find"; _ ] ->
      TOcaml "Lg_edn_backend.t"
  | FList [ FSymbol "__lg_flatten"; collection ] ->
      (match returned_vector_type ~lookup_binding params collection with
      | Some vector_ty -> vector_ty
      | None -> inferred_form_type ~lookup_binding params collection)
      |> flatten_result_type
  | FList [ FSymbol "__lg_memoize"; function_form ] ->
      inferred_form_type ~lookup_binding params function_form
  | FList [ FSymbol "ordering-compare"; _; _ ] -> TOcaml "int"
  | FList [ FSymbol "as-ordering"; FSymbol fn ] -> (
      match string_assoc_opt fn params with
      | Some (TFn (parameter_tys, _)) ->
          TFn (parameter_tys, TOcaml "int")
      | _ -> TUnknown)
  | FList [ FSymbol "__lg_count"; _ ] -> TInt
  | FList [ FSymbol operation; FSymbol receiver ]
    when has_source_name operation "__lg_vals" -> (
      match string_assoc_opt receiver params with
      | Some receiver_ty -> (
          match Types.dynamic_map_types (Types.constraint_value_type receiver_ty) with
          | Some (_, value_ty) -> TVector value_ty
          | None -> TUnknown)
      | None -> TUnknown)
  | FList [ FSymbol "__lg_reduce"; _reducer; collection ] -> (
      let collection_ty = inferred_form_type ~lookup_binding params collection in
      let element_ty =
        match collection_ty with
        | TList element_ty | TVector element_ty | TSet element_ty
        | TSeq element_ty | TArray element_ty ->
            element_ty
        | ty ->
            Types.seqable_constraint_element ty
            |> Option.value ~default:TUnknown
      in
      TNullable element_ty)
  | FList
      [
        FSymbol "__lg_with-meta";
        FMap pairs;
        _metadata;
      ] ->
      let homogeneous_type forms =
        match List.map (inferred_form_type ~lookup_binding params) forms with
        | [] -> TUnknown
        | first :: rest
          when List.for_all (fun ty -> Types.equal first ty) rest ->
            first
        | _ -> TUnknown
      in
      let keys, values = List.split pairs in
      Types.dynamic_map (homogeneous_type keys) (homogeneous_type values)
  | FList
      [
        FSymbol "__lg_with-meta";
        value;
        _metadata;
      ] ->
      inferred_form_type ~lookup_binding params value
  | FList
      (FSymbol ("__lg_str" | "__lg_print_str" | "__lg_pr_str") :: _) ->
      TString
  | FList [ FSymbol "Ok"; value ] ->
      TOcaml_app ("result", [ inferred_form_type ~lookup_binding params value; TUnknown ])
  | FList [ FSymbol "Error"; value ] ->
      TOcaml_app ("result", [ TUnknown; inferred_form_type ~lookup_binding params value ])
  | FList
      (FSymbol "__lg_apply"
      :: FSymbol operation :: _)
    when has_source_name operation "str"
         || has_source_name operation "__lg_str"
         || has_source_name operation "print-str"
         || has_source_name operation "__lg_print_str"
         || has_source_name operation "pr-str"
         || has_source_name operation "__lg_pr_str" ->
      TString
  | FList [ FSymbol ("__lg_first" | "__lg_second"); FSymbol receiver ] -> (
      match string_assoc_opt receiver params with
      | Some ty -> (
          match Types.seqable_constraint_element ty with
          | Some element_ty -> element_ty
          | None -> (
              match Types.next_seq_element ty with
              | Some element_ty -> element_ty
              | None -> if Types.is_dynamic ty then ty else TUnknown))
      | None -> TUnknown)
  | FList [ FSymbol "__lg_next"; FSymbol receiver ] -> (
      match string_assoc_opt receiver params with
      | Some receiver_ty -> (
          match Types.seqable_constraint_element receiver_ty with
          | Some element_ty -> TSeq element_ty
          | None -> (
              match Types.next_seq_element receiver_ty with
              | Some element_ty -> TSeq element_ty
              | None -> TUnknown))
      | None -> TUnknown)
  | FList (FSymbol "__lg_list" :: values) -> (
      match List.map (inferred_collection_item_type lookup_binding params) values with
      | [] -> TList TUnknown
      | first :: rest
        when List.for_all (fun ty -> Types.equal first ty) rest ->
          TList first
      | _ -> TList (Types.dynamic_constraint TUnknown))
  | FVector values -> (
      let types = List.map (inferred_collection_item_type lookup_binding params) values in
      let non_nil = List.filter (fun ty -> not (Types.equal ty TNil)) types in
      match non_nil with
      | [] -> if types = [] then TVector TUnknown else TVector TNil
      | first :: rest
        when List.for_all (fun ty -> Types.equal first ty) rest ->
          if List.exists (Types.equal TNil) types then
            TVector
              (match first with
              | TNullable _ | TOcaml_app ("option", [ _ ]) -> first
              | _ -> TNullable first)
          else TVector first
      | _ -> TUnknown)
  | FList (FSymbol "__lg_hash-set" :: values) -> (
      match List.map (inferred_collection_item_type lookup_binding params) values with
      | [] -> TSet TUnknown
      | first :: rest
        when List.for_all (fun ty -> Types.equal first ty) rest ->
          TSet first
      | _ -> TSet (Types.dynamic_constraint TUnknown))
  | FList [ FSymbol operation; _ ]
    when String.equal operation "Array.length" ->
      TInt
  | FList [ FSymbol operation; FSymbol array; _from; _to ]
    when String.equal operation "Array.sub" -> (
      match string_assoc_opt array params with
      | Some (TArray _ as ty) | Some (TOcaml_app ("array", [ _ ]) as ty) -> ty
      | Some _ | None -> TArray TUnknown)
  | FList
      [ FSymbol operation; FSymbol array; _index ]
    when has_source_name operation "__lg_aget"
         || has_source_name operation "unsafe-aget" -> (
      match string_assoc_opt array params with
      | Some (TArray element_ty | TOcaml_app ("array", [ element_ty ])) ->
          element_ty
      | _ -> TUnknown)
  | FList [ FSymbol "__lg_nth"; FSymbol collection; _index ] -> (
      match string_assoc_opt collection params with
      | Some
          (TList element_ty | TVector element_ty | TSet element_ty
          | TSeq element_ty | TArray element_ty
          | TOcaml_app (("list" | "List.t" | "Seq.t" | "Seq" | "array"),
              [ element_ty ])) ->
          element_ty
      | Some collection_ty ->
          Types.seqable_constraint_element collection_ty
          |> Option.value ~default:TUnknown
      | None -> TUnknown)
  | FList
      [
        FSymbol "__lg_get";
        FSymbol target;
        _key;
        default;
      ] ->
      let default_ty = inferred_form_type ~lookup_binding params default in
      (match
         string_assoc_opt target params
         |> Option.map Types.constraint_value_type
         |> fun target_ty -> Option.bind target_ty Types.dynamic_map_types
       with
      | Some (_, value_ty) -> refine_type value_ty default_ty
      | None -> default_ty)
  | FList
      [
        FSymbol "__lg_get";
        FSymbol target;
        _key;
      ] -> (
      match
        string_assoc_opt target params
        |> Option.map Types.constraint_value_type
        |> fun target_ty -> Option.bind target_ty Types.dynamic_map_types
      with
      | Some (_, value_ty) -> TNullable value_ty
      | None -> TUnknown)
  | FList (FSymbol "__lg_conj" :: (FList [ FSymbol "__lg_get"; _; _ ] as target) :: values)
    ->
      let value_tys = List.map (inferred_form_type ~lookup_binding params) values in
      let element_ty = List.fold_left refine_type TUnknown value_tys in
      (match inferred_form_type ~lookup_binding params target with
      | TList inner -> TList (refine_type inner element_ty)
      | TSeq inner -> TSeq (refine_type inner element_ty)
      | TSet inner -> TSet (refine_type inner element_ty)
      | TVector inner -> TVector (refine_type inner element_ty)
      | _ -> TVector element_ty)
  | FList (FSymbol "__lg_conj" :: target :: values) ->
      let value_tys = List.map (inferred_form_type ~lookup_binding params) values in
      let refine_element element_ty =
        List.fold_left refine_type element_ty value_tys
      in
      (match inferred_form_type ~lookup_binding params target with
      | TList element_ty -> TList (refine_element element_ty)
      | TVector element_ty -> TVector (refine_element element_ty)
      | TSet element_ty -> TSet (refine_element element_ty)
      | TSeq element_ty -> TSeq (refine_element element_ty)
      | target_ty -> target_ty)
  | FList (FSymbol "__lg_list-star" :: arguments) -> (
      match List.rev arguments with
      | tail :: prefix ->
          let element_ty =
            static_seqable_element_type (inferred_form_type ~lookup_binding params tail)
            |> Option.value ~default:TUnknown
          in
          let list_ty = TList (List.fold_left
            (fun ty value -> refine_type ty (inferred_form_type ~lookup_binding params value))
            element_ty prefix) in
          if prefix = [] then TNullable list_ty else list_ty
      | [] -> TList TUnknown)
  | FList [ FSymbol "__lg_cons"; value; collection ] ->
      let value_ty = inferred_form_type ~lookup_binding params value in
      let element_ty =
        match inferred_form_type ~lookup_binding params collection with
        | TList inner | TVector inner | TSet inner | TSeq inner ->
            refine_type inner value_ty
        | collection_ty ->
            Types.seqable_constraint_element collection_ty
            |> Option.map (fun inner -> refine_type inner value_ty)
            |> Option.value ~default:value_ty
      in
      TSeq element_ty
  | FList
      [
        FSymbol ("__lg_if-some" | "__lg_if-let");
        FVector [ FSymbol binding; option_form ];
        then_form;
        else_form;
      ] ->
      let payload_ty =
        match inferred_form_type ~lookup_binding params option_form with
        | TNullable payload | TOcaml_app ("option", [ payload ]) -> payload
        | _ -> TUnknown
      in
      let branch_params =
        (binding, payload_ty) :: string_remove_assoc binding params
      in
      refine_type
        (inferred_form_type ~lookup_binding branch_params then_form)
        (inferred_form_type ~lookup_binding params else_form)
  | FList
      [
        FSymbol "__lg_some-thread";
        FVector [ FSymbol binding; option_form ];
        then_form;
      ] ->
      let option_ty = inferred_form_type ~lookup_binding params option_form in
      let payload_ty =
        match option_ty with
        | TNullable payload | TOcaml_app ("option", [ payload ]) -> payload
        | TNil | TUnknown | TMeta _ | TVar _ -> TUnknown
        | ty -> ty
      in
      let branch_params =
        (binding, payload_ty) :: string_remove_assoc binding params
      in
      let threaded_ty = inferred_form_type ~lookup_binding branch_params then_form in
      (match option_ty with
      | TNullable _ | TOcaml_app ("option", [ _ ]) | TNil | TUnknown | TMeta _
      | TVar _ -> (
          match threaded_ty with
          | TNullable _ | TOcaml_app ("option", [ _ ]) | TNil -> threaded_ty
          | ty -> TNullable ty)
      | _ -> threaded_ty)
  | FList ((FSymbol "__lg_get" | FSymbol "__lg_find") :: _) -> TUnknown
  | FMap pairs ->
      let homogeneous_type forms =
        let types = List.map (inferred_form_type ~lookup_binding params) forms in
        let non_nil = List.filter (fun ty -> not (Types.equal ty TNil)) types in
        match non_nil with
        | [] -> Some (if types = [] then TUnknown else TNil)
        | first :: rest
          when List.for_all (fun ty -> Types.equal first ty) rest ->
            if List.exists (Types.equal TNil) types then
              Some
                (match first with
                | TNullable _ | TOcaml_app ("option", [ _ ]) -> first
                | _ -> TNullable first)
            else Some first
        | _ -> None
      in
      if
        List.for_all
          (fun (key, _value) ->
            match key with FKeyword _ -> true | _ -> false)
          pairs
      then
        TRecord
          (List.map
             (fun (key, value) ->
               match key with
               | FKeyword keyword ->
                   make_map_field keyword (inferred_form_type ~lookup_binding params value)
               | _ -> assert false)
             pairs)
      else
        let keys, values = List.split pairs in
        (match (homogeneous_type keys, homogeneous_type values) with
        | Some key_ty, Some value_ty -> Types.dynamic_map key_ty value_ty
        | _ -> TUnknown)
  | FList (_function :: FSymbol receiver :: _) -> (
      match string_assoc_opt receiver params with
      | Some ty when Types.is_dynamic ty -> ty
      | _ -> TUnknown)
  | _ -> TUnknown

and inferred_collection_item_type lookup_binding params form =
  match inferred_form_type ~lookup_binding params form with
  | TUnknown | TMeta _ | TVar _ -> (
      match form with
      | FList (FSymbol name :: arguments) -> (
          let actual_tys =
            List.map
              (inferred_collection_item_type lookup_binding params)
              arguments
          in
          match lookup_binding name with
          | TFn (parameter_tys, return_ty)
            when List.length parameter_tys = List.length actual_tys ->
              Types.instantiate_type ~templates:parameter_tys
                ~actuals:actual_tys return_ty
          | TOverloaded_fn arities -> (
              match
                List.find_opt
                  (fun (arity : fn_arity) ->
                    Option.is_none arity.rest_param
                    && List.length arity.fixed_params
                       = List.length actual_tys)
                  arities
              with
              | Some arity ->
                  Types.instantiate_type ~templates:arity.fixed_params
                    ~actuals:actual_tys arity.return_ty
              | None -> TUnknown)
          | _ -> TUnknown)
      | _ -> TUnknown)
  | ty -> ty

and returned_vector_type ?(lookup_binding = fun _ -> TUnknown) params = function
  | FVector items ->
      let item_tys = List.map (inferred_form_type ~lookup_binding params) items in
      let edn_scalar_element = function
        | TInt | TOcaml "int" | TBool | TNil -> true
        | TNullable inner | TOcaml_app ("option", [ inner ]) -> (
            match inner with TInt | TOcaml "int" | TBool -> true | _ -> false)
        | _ -> false
      in
      let element_ty =
        match item_tys with
        | [] -> TUnknown
        | first :: rest
          when List.for_all (fun ty -> Types.equal first ty) rest ->
            first
        | _ when List.for_all edn_scalar_element item_tys ->
            TOcaml "Lg_edn_backend.t"
        | _ -> Types.dynamic_constraint TUnknown
      in
      Some (TVector element_ty)
  | FList [ FSymbol "__lg_subvec"; collection; _ ]
  | FList [ FSymbol "__lg_subvec"; collection; _; _ ] -> (
      match returned_vector_type ~lookup_binding params collection with
      | Some vector_ty -> Some vector_ty
      | None -> Some (TVector (Types.dynamic_constraint TUnknown)))
  | FList [ FSymbol "if"; condition; then_form; else_form ] -> (
      match literal_truthiness condition with
      | Some true -> returned_vector_type ~lookup_binding params then_form
      | Some false -> returned_vector_type ~lookup_binding params else_form
      | None -> (
          match
            ( returned_vector_type ~lookup_binding params then_form,
              returned_vector_type ~lookup_binding params else_form )
          with
          | Some left, Some right -> Some (refine_type left right)
          | Some vector_ty, None | None, Some vector_ty -> Some vector_ty
          | None, None -> None))
  | FList (FSymbol "loop" :: _bindings :: body_forms) -> (
      match List.rev body_forms with
      | result :: _ -> returned_vector_type ~lookup_binding params result
      | [] -> None)
  | FList (FSymbol ("let" | "let*" | "do") :: forms) -> (
      match List.rev forms with
      | result :: _ -> returned_vector_type ~lookup_binding params result
      | [] -> None)
  | form -> (
      match inferred_form_type ~lookup_binding params form with
      | TVector _ as vector_ty -> Some vector_ty
      | _ -> None)

let select_fn_arity arities argument_count =
  match
    List.find_opt
      (fun (arity : fn_arity) ->
        Option.is_none arity.rest_param
        && List.length arity.fixed_params = argument_count)
      arities
  with
  | Some arity -> Some arity
  | None ->
      List.find_opt
        (fun (arity : fn_arity) ->
          Option.is_some arity.rest_param
          && argument_count >= List.length arity.fixed_params)
        arities

let rec inferred_call_return_type ~lookup_function_ty params = function
  | FList [ FKeyword keyword; target ] ->
      let target_ty =
        match inferred_form_type params target with
        | ty when Type_solver.is_open ty ->
            inferred_call_return_type ~lookup_function_ty params target
        | ty -> ty
      in
      (match Types.record_fields target_ty with
      | Some fields ->
          (match Types.find_field keyword fields with
          | Some field -> Expression_support.clj_function_type field.ty
          | None -> TUnknown)
      | None ->
          (match Types.dynamic_map_types target_ty with
          | Some (_, value_ty) -> TNullable value_ty
          | None -> TUnknown))
  | FList
      [ FSymbol ("__lg_if-some" | "__lg_if-let");
        FVector [ FSymbol binding; option_form ]; then_form; else_form ] ->
      let infer params form =
        match inferred_form_type params form with
        | ty when Type_solver.is_open ty ->
            inferred_call_return_type ~lookup_function_ty params form
        | ty -> ty
      in
      let payload_ty =
        match infer params option_form with
        | TNullable payload | TOcaml_app ("option", [ payload ]) -> payload
        | _ -> TUnknown
      in
      let branch_params =
        (binding, payload_ty) :: string_remove_assoc binding params
      in
      Expression_support.merge_branch_types
        (infer branch_params then_form) (infer params else_form)
      |> Option.value ~default:TUnknown
  | FList [ FSymbol "Ok"; value ] ->
      let value_ty =
        match inferred_form_type params value with
        | ty when Type_solver.is_open ty ->
            inferred_call_return_type ~lookup_function_ty params value
        | ty -> ty
      in
      TOcaml_app ("result", [ value_ty; TUnknown ])
  | FList [ FSymbol "Error"; value ] ->
      let value_ty =
        match inferred_form_type params value with
        | ty when Type_solver.is_open ty ->
            inferred_call_return_type ~lookup_function_ty params value
        | ty -> ty
      in
      TOcaml_app ("result", [ TUnknown; value_ty ])
  | FList (FSymbol "do" :: body_forms) -> (
      match List.rev body_forms with
      | result :: _ ->
          (match inferred_form_type params result with
          | ty when Type_solver.is_open ty ->
              inferred_call_return_type ~lookup_function_ty params result
          | ty -> ty)
      | [] -> TNil)
  | FList (FSymbol "for" :: FVector bindings :: body_forms) ->
      let infer params form =
        match inferred_form_type params form with
        | ty when Type_solver.is_open ty ->
            inferred_call_return_type ~lookup_function_ty params form
        | ty -> ty
      in
      let bind_pattern params pattern source_ty =
        let bindings =
          match Destructure.pattern_type_hints pattern source_ty with
          | [] ->
              Destructure.pattern_names pattern
              |> List.map (fun name -> (name, TUnknown))
          | bindings -> bindings
        in
        let names = List.map fst bindings in
        bindings
        @ List.filter (fun (name, _) -> not (string_mem name names)) params
      in
      let bind_let params bindings =
        let rec loop params = function
          | pattern :: value :: rest ->
              let value_ty = infer params value in
              loop (bind_pattern params pattern value_ty) rest
          | [] | [ _ ] -> params
        in
        loop params bindings
      in
      let rec bind_generators params = function
        | [] -> params
        | FKeyword ":let" :: FVector bindings :: rest ->
            bind_generators (bind_let params bindings) rest
        | FKeyword (":when" | ":while") :: _condition :: rest ->
            bind_generators params rest
        | ((FSymbol _ | FVector _ | FMap _) as pattern) :: collection :: rest ->
            let collection_ty = infer params collection in
            let element_ty =
              into_source_element_type collection_ty
              |> Option.value ~default:TUnknown
            in
            bind_generators (bind_pattern params pattern element_ty) rest
        | _ -> params
      in
      let params = bind_generators params bindings in
      let element_ty =
        match List.rev body_forms with
        | result :: _ -> infer params result
        | [] -> TNil
      in
      TSeq element_ty
  | FList [ FSymbol "if"; condition; then_form; else_form ] -> (
      let infer form =
        match inferred_form_type params form with
        | ty when Type_solver.is_open ty ->
            inferred_call_return_type ~lookup_function_ty params form
        | ty -> ty
      in
      match literal_truthiness condition with
      | Some true -> infer then_form
      | Some false -> infer else_form
      | None ->
          Expression_support.merge_branch_types (infer then_form)
            (infer else_form)
          |> Option.value ~default:TUnknown)
  | FList [ FSymbol "if"; _condition; then_form ] ->
      let then_ty =
        match inferred_form_type params then_form with
        | ty when Type_solver.is_open ty ->
            inferred_call_return_type ~lookup_function_ty params then_form
        | ty -> ty
      in
      Expression_support.merge_branch_types then_ty TNil
      |> Option.value ~default:TUnknown
  | FList (FSymbol when_name :: _condition :: body_forms)
    when has_source_name when_name "__lg_when" -> (
      match List.rev body_forms with
      | [] -> TNil
      | result :: _ ->
          let result_ty =
            match inferred_form_type params result with
            | ty when Type_solver.is_open ty ->
                inferred_call_return_type ~lookup_function_ty params result
            | ty -> ty
          in
          Expression_support.merge_branch_types result_ty TNil
          |> Option.value ~default:TUnknown)
  | FList (FSymbol ("let" | "let*" | "binding") :: FVector bindings :: body_forms)
    ->
      let infer params form =
        match inferred_form_type params form with
        | ty when Type_solver.is_open ty ->
            inferred_call_return_type ~lookup_function_ty params form
        | ty -> ty
      in
      let rec bind params = function
        | FSymbol name :: value :: rest ->
            let value_ty = infer params value in
            bind ((name, value_ty) :: string_remove_assoc name params) rest
        | _ :: _ :: rest -> bind params rest
        | [] | [ _ ] -> params
      in
      let params = bind params bindings in
      (match List.rev body_forms with
      | result :: _ -> infer params result
      | [] -> TNil)
  | FList ((FSymbol "__lg_assoc" | FCoreSymbol Core_assoc) :: target :: pairs) ->
      let target_ty =
        match inferred_form_type params target with
        | ty when Type_solver.is_open ty ->
            inferred_call_return_type ~lookup_function_ty params target
        | ty -> ty
      in
      (match Types.record_fields target_ty with
      | Some fields ->
          let rec updates_existing_fields = function
            | [] -> true
            | FKeyword keyword :: _value :: rest ->
                Option.is_some (Types.find_field keyword fields)
                && updates_existing_fields rest
            | _ -> false
          in
          if updates_existing_fields pairs then target_ty else TUnknown
      | None -> TUnknown)
  | FList (FSymbol "match" :: target :: clauses) ->
      let infer params form =
        match inferred_form_type params form with
        | ty when Type_solver.is_open ty ->
            inferred_call_return_type ~lookup_function_ty params form
        | ty -> ty
      in
      let target_ty = infer params target in
      let bind_payload payload_ty pattern params =
        match pattern with
        | FSymbol "_" -> params
        | FSymbol name -> (name, payload_ty) :: string_remove_assoc name params
        | _ -> params
      in
      let branch_params pattern =
        match (pattern, target_ty) with
        | FList [ FSymbol "Some"; payload ],
          (TNullable payload_ty | TOcaml_app ("option", [ payload_ty ])) ->
            bind_payload payload_ty payload params
        | FList [ FSymbol "Ok"; payload ],
          TOcaml_app ("result", [ ok_ty; _ ]) ->
            bind_payload ok_ty payload params
        | FList [ FSymbol "Error"; payload ],
          TOcaml_app ("result", [ _; error_ty ]) ->
            bind_payload error_ty payload params
        | _ -> params
      in
      let rec result_types = function
        | pattern :: result :: rest ->
            infer (branch_params pattern) result :: result_types rest
        | [] | [ _ ] -> []
      in
      result_types clauses
      |> List.filter (fun ty ->
             not
               (Types.equal ty TUnknown
               || Type_solver.is_open ty && not (Types.is_dynamic ty)))
      |> (function
           | [] -> TUnknown
           | first :: rest ->
               List.fold_left
                 (fun merged ty ->
                   Expression_support.merge_branch_types merged ty
                   |> Option.value ~default:TUnknown)
                 first rest)
  | FList
      (FSymbol "__lg_apply" :: FSymbol operation :: _)
    when has_source_name operation "str"
         || has_source_name operation "__lg_str"
         || has_source_name operation "print-str"
         || has_source_name operation "__lg_print_str"
         || has_source_name operation "pr-str"
         || has_source_name operation "__lg_pr_str" ->
      TString
  | FList
      [
        FSymbol "__lg_into";
        target;
        transducer;
        source;
      ] ->
      inferred_call_return_type ~lookup_function_ty params
        (FList
           [
             FSymbol "__lg_into";
             target;
             FList [ FSymbol "sequence"; transducer; source ];
           ])
  | FList [ FSymbol reduce_name; _reducer; collection ]
    when has_source_name reduce_name "__lg_reduce" ->
      let collection_ty = inferred_form_type params collection in
      let element_ty =
        match collection_ty with
        | TList element_ty | TVector element_ty | TSet element_ty
        | TSeq element_ty | TArray element_ty ->
            element_ty
        | ty ->
            Types.seqable_constraint_element ty
            |> Option.value ~default:TUnknown
      in
      TNullable element_ty
  | FList [ FSymbol "__lg_reduce"; _reducer; FMap []; _collection ] ->
      Types.dynamic_map (Type_solver.fresh ()) (Type_solver.fresh ())
  | FList [ FSymbol "__lg_reduce"; _reducer; init; _collection ] ->
      inferred_form_type params init
  | FList [ FSymbol group_by_name; key_fn; collection ]
    when has_source_name group_by_name "group-by" ->
      let infer params form =
        match inferred_form_type params form with
        | ty when Type_solver.is_open ty ->
            inferred_call_return_type ~lookup_function_ty params form
        | ty -> ty
      in
      let collection_ty =
        infer params collection
      in
      let input_ty =
        match into_source_element_type collection_ty with
        | Some input_ty -> input_ty
        | None -> (
            match collection with
            | FVector values | FList (FSymbol "__lg_list" :: values) -> (
                match List.map (infer params) values with
                | [] -> TUnknown
                | first :: rest
                  when not
                         (match first with
                         | TUnknown | TMeta _ | TVar _ -> true
                         | _ -> false)
                       && List.for_all (Types.equal first) rest ->
                    first
                | _ -> TUnknown)
            | _ -> TUnknown)
      in
      let key_ty =
        match key_fn with
        | FKeyword keyword -> (
            match Types.record_fields input_ty with
            | Some fields -> (
                match Types.find_field keyword fields with
                | Some field -> field.ty
                | None -> TUnknown)
            | None -> TUnknown)
        | FSymbol name -> (
            match string_assoc_opt name params with
            | Some (TFn ([ _ ], return_ty)) -> return_ty
            | Some _ | None -> (
                match lookup_function_ty name with
                | Ok (TFn ([ _ ], return_ty)) -> return_ty
                | _ -> TUnknown))
        | _ -> TUnknown
      in
      Types.dynamic_map key_ty (TVector input_ty)
  | FList (FSymbol map_name :: fn :: collection_forms)
    when (has_source_name map_name "__lg_map"
         || has_source_name map_name "map"
         || has_source_name map_name "__lg_mapv")
         && List.length collection_forms >= 2 ->
      let infer params form =
        match inferred_form_type params form with
        | ty when Type_solver.is_open ty ->
            inferred_call_return_type ~lookup_function_ty params form
        | ty -> ty
      in
      let variadic_vector_constructor = function
        | FSymbol name -> (
            let function_ty =
              match string_assoc_opt name params with
              | Some ty -> Ok ty
              | None -> lookup_function_ty name
            in
            match function_ty with
            | Ok
                (TOverloaded_fn
                  [
                    {
                      fixed_params = [];
                      rest_param = Some element_ty;
                      return_ty = TVector return_element_ty;
                    };
                  ]) ->
                Types.equal element_ty return_element_ty
            | Ok _ | Error _ -> false)
        | _ -> false
      in
      let collection_element_ty collection =
        infer params collection
        |> into_source_element_type
        |> Option.value ~default:TUnknown
      in
      let element_tys = List.map collection_element_ty collection_forms in
      let same_known_element =
        match
          List.filter
            (function TUnknown | TMeta _ | TVar _ -> false | _ -> true)
            element_tys
        with
        | [] -> None
        | first :: rest when List.for_all (Types.equal first) rest ->
            Some first
        | _ -> None
      in
      let callback_return =
        match (fn, same_known_element) with
        | _, Some element_ty when variadic_vector_constructor fn ->
            TVector element_ty
        | FSymbol name, _ -> (
            let function_ty =
              match string_assoc_opt name params with
              | Some ty -> Ok ty
              | None -> lookup_function_ty name
            in
            match function_ty with
            | Ok (TFn (parameter_tys, return_ty))
              when List.length parameter_tys = List.length element_tys ->
                return_ty
            | Ok (TOverloaded_fn arities) ->
                arities
                |> List.find_map (fun (arity : fn_arity) ->
                       let fixed_count = List.length arity.fixed_params in
                       if fixed_count = List.length element_tys then
                         Some arity.return_ty
                       else
                         match arity.rest_param with
                         | Some _ when fixed_count <= List.length element_tys ->
                             Some arity.return_ty
                         | Some _ | None -> None)
                |> Option.value ~default:TUnknown
            | Ok _ | Error _ -> TUnknown)
        | FList (FSymbol "fn" :: (FVector _ as params_form) :: body_forms), _
        | FList
            (FSymbol "fn" :: FSymbol _ :: (FVector _ as params_form)
            :: body_forms),
          _ -> (
            match (Destructure.parse_param_specs params_form, List.rev body_forms) with
            | Ok specs, result :: reversed_prefix
              when List.length specs = List.length element_tys ->
                let local_bindings =
                  List.combine specs element_tys
                  |> List.concat_map
                       (fun ((spec : Destructure.param_spec), element_ty) ->
                         (spec.source_name, element_ty)
                         ::
                         (if spec.destructured then
                            Destructure.pattern_type_hints spec.pattern
                              element_ty
                          else []))
                in
                let local_names = List.map fst local_bindings in
                let function_params =
                  local_bindings
                  @ List.filter
                      (fun (name, _) -> not (string_mem name local_names))
                      params
                in
                let _ = reversed_prefix in
                infer function_params result
            | (Ok _ | Error _), _ -> TUnknown)
        | _ -> TUnknown
      in
      if has_source_name map_name "__lg_mapv" then TVector callback_return
      else TSeq callback_return
  | FList [ FSymbol map_name; fn; collection ]
    when has_source_name map_name "__lg_map"
         || has_source_name map_name "map"
         || has_source_name map_name "__lg_mapv" ->
      let collection_ty =
        match inferred_form_type params collection with
        | ty when Type_solver.is_open ty ->
            inferred_call_return_type ~lookup_function_ty params collection
        | ty -> ty
      in
      let element_ty =
        into_source_element_type collection_ty
        |> Option.value ~default:TUnknown
      in
      let callback_return =
        let infer params form =
          match inferred_form_type params form with
          | ty when Type_solver.is_open ty ->
              inferred_call_return_type ~lookup_function_ty params form
          | ty -> ty
        in
        match fn with
        | FSymbol name -> (
            match string_assoc_opt name params with
            | Some (TFn ([ _ ], return_ty)) -> return_ty
            | Some _ | None -> (
                match lookup_function_ty name with
                | Ok (TFn ([ _ ], return_ty)) -> return_ty
                | _ -> TUnknown))
        | FKeyword keyword -> (
            match Types.record_fields element_ty with
            | Some fields -> (
                match Types.find_field keyword fields with
                | Some field -> field.ty
                | None -> TUnknown)
            | None -> TUnknown)
        | FList (FSymbol "fn" :: (FVector _ as params_form) :: body_forms)
        | FList
            (FSymbol "fn" :: FSymbol _ :: (FVector _ as params_form)
            :: body_forms) -> (
            match (Destructure.parse_param_specs params_form, List.rev body_forms) with
            | Ok [ (spec : Destructure.param_spec) ], result :: reversed_prefix ->
                let local_bindings =
                  (spec.source_name, element_ty)
                  ::
                  (if spec.destructured then
                     Destructure.pattern_type_hints spec.pattern element_ty
                   else [])
                in
                let local_names = List.map fst local_bindings in
                let function_params =
                  local_bindings
                  @ List.filter
                      (fun (name, _) -> not (string_mem name local_names))
                      params
                in
                let _ = reversed_prefix in
                infer function_params result
            | (Ok _ | Error _), _ -> TUnknown)
        | _ -> TUnknown
      in
      if has_source_name map_name "__lg_mapv" then TVector callback_return
      else TSeq callback_return
  | FList
      [
        FSymbol "__lg_into";
        target;
        source;
      ] ->
      let infer form =
        match inferred_form_type params form with
        | TUnknown ->
            inferred_call_return_type ~lookup_function_ty params form
        | ty -> ty
      in
      let target_ty = infer target in
      let source_ty =
        match infer source with
        | TUnknown ->
            returned_vector_type params source
            |> Option.value ~default:TUnknown
        | ty -> ty
      in
      let source_element =
        match source_ty with
        | TVector element_ty | TList element_ty | TSet element_ty
        | TArray element_ty | TSeq element_ty ->
            Some element_ty
        | source_ty -> Types.seqable_constraint_element source_ty
      in
      (match (target_ty, source_element) with
      | TRecord [], Some (TTuple [ key_ty; value_ty ]) ->
          Types.dynamic_map key_ty value_ty
      | TRecord [], Some (TVector element_ty) ->
          Types.dynamic_map element_ty element_ty
      | TRecord [], _ -> (
          match Types.dynamic_map_types source_ty with
          | Some (key_ty, value_ty) -> Types.dynamic_map key_ty value_ty
          | None -> Types.dynamic_map (Type_solver.fresh ()) (Type_solver.fresh ()))
      | TVector (TUnknown | TMeta _ | TVar _), Some element_ty ->
          TVector element_ty
      | TList (TUnknown | TMeta _ | TVar _), Some element_ty ->
          TList element_ty
      | TSet (TUnknown | TMeta _ | TVar _), Some element_ty ->
          TSet element_ty
      | TArray (TUnknown | TMeta _ | TVar _), Some element_ty ->
          TArray element_ty
      | _ -> target_ty)
  | FList (callee :: arguments) ->
      let inferred_argument_type = function
        | FList (FSymbol "fn" :: (FVector _ as params_form) :: body_forms)
        | FList
            (FSymbol "fn" :: FSymbol _ :: (FVector _ as params_form)
            :: body_forms) -> (
            let lookup_binding name =
              lookup_function_ty name |> Result.value ~default:TUnknown
            in
            inferred_inline_function_type ~lookup_function_ty ~lookup_binding
              params params_form body_forms)
        | argument -> (
            match inferred_form_type params argument with
            | ty when Type_solver.is_open ty ->
                inferred_call_return_type ~lookup_function_ty params argument
            | ty -> ty)
      in
      let actual_tys =
        List.map inferred_argument_type arguments
      in
      let instantiate parameter_tys return_ty =
        if List.length parameter_tys <> List.length actual_tys then TUnknown
        else
          Types.instantiate_type ~templates:parameter_tys ~actuals:actual_tys
            return_ty
      in
      let callee_ty =
        match callee with
        | FSymbol function_name -> (
            match string_assoc_opt function_name params with
            | Some ty -> Ok ty
            | None -> lookup_function_ty function_name)
        | FList _ as call ->
            Ok (inferred_call_return_type ~lookup_function_ty params call)
        | form -> Ok (inferred_form_type params form)
      in
      (match callee_ty with
      | Ok (TFn (parameter_tys, return_ty)) ->
          instantiate parameter_tys return_ty
      | Ok (TOverloaded_fn arities) -> (
          match select_fn_arity arities (List.length arguments) with
          | None -> TUnknown
          | Some arity ->
              let parameter_tys =
                arity.fixed_params
                @
                match arity.rest_param with
                | None -> []
                | Some rest_ty ->
                    List.init
                      (List.length arguments - List.length arity.fixed_params)
                      (fun _ -> rest_ty)
              in
              instantiate parameter_tys arity.return_ty)
      | Ok ty when Option.is_some (Types.constant_function_result ty) ->
          Types.constant_function_result ty |> Option.get
      | Ok _ | Error _ -> TUnknown)
  | _ -> TUnknown

and inferred_inline_function_type ~lookup_function_ty ~lookup_binding params
    params_form body_forms =
  match (Destructure.parse_param_specs params_form, List.rev body_forms) with
  | Ok specs, result :: _ ->
      let parameter_tys =
        List.map
          (fun (spec : Destructure.param_spec) ->
            Option.value spec.explicit_ty ~default:TUnknown)
          specs
      in
      let local_bindings =
        List.map2
          (fun (spec : Destructure.param_spec) parameter_ty ->
            let destructured =
              if spec.destructured then
                Destructure.pattern_names spec.pattern
                |> List.map (fun name -> (name, TUnknown))
              else []
            in
            (spec.source_name, parameter_ty) :: destructured)
          specs parameter_tys
        |> List.concat
      in
      let local_names = List.map fst local_bindings in
      let local_params =
        local_bindings
        @ List.filter
            (fun (name, _) -> not (string_mem name local_names))
            params
      in
      let result_ty =
        match inferred_form_type ~lookup_binding local_params result with
        | ty when Type_solver.is_open ty -> (
            match
              inferred_call_return_type ~lookup_function_ty local_params
                result
            with
            | TUnknown -> ty
            | inferred -> inferred)
        | ty -> ty
      in
      TFn (parameter_tys, result_ty)
  | (Ok _ | Error _), _ -> TUnknown

let inferred_form_or_call_type ~lookup_function_ty params form =
  let lookup_binding name =
    lookup_function_ty name |> Result.value ~default:TUnknown
  in
  match form, inferred_form_type ~lookup_binding params form with
  | FList (FSymbol "fn" :: (FVector _ as params_form) :: body_forms), _
  | FList
      (FSymbol "fn" :: FSymbol _ :: (FVector _ as params_form)
      :: body_forms),
    _ ->
      inferred_inline_function_type ~lookup_function_ty ~lookup_binding params
        params_form body_forms
  | FSymbol name, TUnknown when not (string_mem_assoc name params) ->
      (match lookup_function_ty name with
      | Ok (TFn ([], result)) when Expression_support.is_constructor_name name ->
          result
      | Ok ty -> ty
      | Error _ -> TUnknown)
  | _, ty when Type_solver.is_open ty -> (
      match inferred_call_return_type ~lookup_function_ty params form with
      | TUnknown -> ty
      | inferred -> (
          match Expression_support.merge_branch_types ty inferred with
          | Some merged -> merged
          | None -> inferred))
  | _, ty -> ty

let rec form_checks_reduced name = function
  | FList [ FSymbol predicate; FSymbol candidate ] ->
      candidate = name
      && (has_source_name predicate "__lg_reduced-predicate"
         || has_source_name predicate "reduced?")
  | FList forms | FVector forms -> List.exists (form_checks_reduced name) forms
  | FMap pairs ->
      List.exists
        (fun (key, value) ->
          form_checks_reduced name key || form_checks_reduced name value)
        pairs
  | _ -> false

let constrain_maybe_reduced_callbacks params forms =
  let rec visit params = function
    | FList (FSymbol binding_form :: FVector bindings :: body_forms)
      when binding_form = "let" || binding_form = "let*"
           || String.ends_with ~suffix:"/let" binding_form
           || String.ends_with ~suffix:"/let*" binding_form ->
        let rec visit_bindings params = function
          | FSymbol local_name :: FList (FSymbol fn_name :: args) :: rest ->
              let params =
                if List.exists (form_checks_reduced local_name) body_forms then
                  constrain_symbol
                    (TFn
                       ( List.map (fun _ -> TUnknown) args,
                         Types.maybe_reduced_callback_result TUnknown ))
                    params fn_name
                  |> Result.value ~default:params
                else params
              in
              visit_bindings params rest
          | _ :: _ :: rest -> visit_bindings params rest
          | _ -> params
        in
        let params = visit_bindings params bindings in
        List.fold_left visit params body_forms
    | FList nested | FVector nested -> List.fold_left visit params nested
    | FMap pairs ->
        List.fold_left
          (fun params (key, value) -> visit (visit params key) value)
          params pairs
    | _ -> params
  in
  List.fold_left visit params forms

let rec rewrite_simple_aliases aliases = function
  | FSymbol name as form -> (
      match string_assoc_opt name aliases with
      | Some ((FSymbol _ | FKeyword _) as alias) ->
          rewrite_simple_aliases (string_remove_assoc name aliases) alias
      | _ -> form)
  | FList (FSymbol binding_form :: FVector bindings :: body_forms)
    when binding_form = "let" || binding_form = "let*"
         || binding_form = "loop"
         || String.ends_with ~suffix:"/let" binding_form
         || String.ends_with ~suffix:"/let*" binding_form ->
      let rec rewrite_bindings aliases rewritten = function
        | pattern :: value :: rest ->
            let value = rewrite_simple_aliases aliases value in
            let aliases = List.fold_left (fun aliases name -> string_remove_assoc name aliases)
              aliases (Destructure.pattern_names pattern) in
            rewrite_bindings aliases
              (value :: pattern :: rewritten)
              rest
        | rest -> (aliases, List.rev_append rewritten rest)
      in
      let body_aliases, bindings = rewrite_bindings aliases [] bindings in
      FList
        (FSymbol binding_form :: FVector bindings
        :: List.map (rewrite_simple_aliases body_aliases) body_forms)
  | FList (FSymbol "fn" :: FVector parameters :: body_forms) ->
      let aliases =
        List.fold_left
          (fun aliases name -> string_remove_assoc name aliases)
          aliases (List.concat_map Destructure.pattern_names parameters)
      in
      FList
        (FSymbol "fn" :: FVector parameters
        :: List.map (rewrite_simple_aliases aliases) body_forms)
  | FList
      (FSymbol "fn" :: FSymbol function_name :: FVector parameters
      :: body_forms) ->
      let aliases = string_remove_assoc function_name aliases in
      let aliases =
        List.fold_left
          (fun aliases name -> string_remove_assoc name aliases)
          aliases (List.concat_map Destructure.pattern_names parameters)
      in
      FList
        (FSymbol "fn" :: FSymbol function_name :: FVector parameters
        :: List.map (rewrite_simple_aliases aliases) body_forms)
  | FList [ FSymbol ("quote" | "__lg_quote"); _ ] as form -> form
  | FList forms -> FList (List.map (rewrite_simple_aliases aliases) forms)
  | FVector forms -> FVector (List.map (rewrite_simple_aliases aliases) forms)
  | FMap pairs ->
      FMap
        (List.map
           (fun (key, value) ->
             ( rewrite_simple_aliases aliases key,
               rewrite_simple_aliases aliases value ))
           pairs)
  | form -> form

let restore_explicit_parameter_types ~resolve_named_record specs inferred =
  let rigid_bindings =
    specs
    |> List.filter_map (fun (spec : Destructure.param_spec) ->
           match spec.explicit_ty with
           | Some ty when not (Types.equal ty TUnknown) ->
               Some (spec.source_name, resolve_named_record ty)
           | Some _ | None -> None)
  in
  List.map
    (fun (name, ty) ->
      match string_assoc_opt name rigid_bindings with
      | Some rigid_ty -> (name, rigid_ty)
      | None -> (name, ty))
    inferred

let infer_params ?expected_return_ty ?(materialize_open_equality = false)
    ?observe_constraint ?observe_call
    ?(lookup_closed_sum_candidates = fun _ -> [])
    ?(lookup_closed_sum_constructors = fun _ -> [])
    ?(lookup_successful_call_refinement = fun _ -> None)
    ?(lookup_call_ty = fun _ _ -> None)
    ?(expand_form = fun form -> Ok form)
    ~lookup_function_ty
    ~lookup_protocol_constraint ~lookup_dynamic_key_record_type
    ~resolve_named_record params body_forms =
  let record_constructor_type name =
    let clojure_record_constructor_name name =
      String.length name > 2 && name.[0] = '-' && name.[1] = '>'
    in
    let constructor_type_name name =
      if String.ends_with ~suffix:"." name then
        Some (String.sub name 0 (String.length name - 1))
      else
        match String.rindex_opt name '/' with
        | Some separator ->
            let qualifier = String.sub name 0 (separator + 1) in
            let member =
              String.sub name (separator + 1)
                (String.length name - separator - 1)
            in
            if clojure_record_constructor_name member then
              Some
                (qualifier
                ^ String.sub member 2 (String.length member - 2))
            else None
        | None when clojure_record_constructor_name name ->
            Some (String.sub name 2 (String.length name - 2))
        | None -> None
    in
    match constructor_type_name name with
    | None -> None
    | Some type_name -> (
        match resolve_named_record (TOcaml ("__lg_record:" ^ type_name)) with
        | TNamed_record record ->
            Some
              (TFn
                 ( List.map
                     (fun (field : field) -> field.ty)
                     (Types.record_constructor_fields record.fields),
                   TNamed_record record ))
        | _ -> None)
  in
  let lookup_function_ty name =
    match string_assoc_opt name params with
    | Some ty -> Ok ty
    | None -> (
        match lookup_function_ty name with
        | Ok _ as result -> result
        | Error _ as error -> (
            match record_constructor_type name with
            | Some ty -> Ok ty
            | None -> error))
  in
  let lookup_loop_initializer_type =
    let lookup = lookup_function_ty in
    fun name ->
      match lookup name with
      | Ok _ as result -> result
      | Error _ as error when String.ends_with ~suffix:"." name ->
          let type_name = String.sub name 0 (String.length name - 1) in
          (match
             resolve_named_record (TOcaml ("__lg_record:" ^ type_name))
           with
          | TNamed_record record ->
              Ok
                (TFn
                   ( List.map
                       (fun (field : field) -> field.ty)
                       (Types.record_constructor_fields record.fields),
                     TNamed_record record ))
          | _ -> error)
      | Error _ as error -> error
  in
  let inferred_binding_form_type params form =
    let direct_ty =
      match form with
      | FList (FSymbol "record" :: FSymbol name :: _) ->
          resolve_named_record (TOcaml name)
      | _ -> inferred_form_type
          ~lookup_binding:(fun name -> lookup_function_ty name |> Result.value ~default:TUnknown)
          params form
    in
    if Type_solver.is_open direct_ty then
      inferred_call_return_type ~lookup_function_ty params form
    else direct_ty
  in
  let core_keep_name name =
    String.equal name "__lg_keep" || String.equal name "keep"
    || String.equal name "clojure.core/keep"
    || String.equal name "cljs.core/keep"
  in
  let core_keep_function_name name =
    String.equal name "__lg_keep"
    || (core_keep_name name
       &&
       match lookup_function_ty name with
       | Ok (TFn (TFn _ :: _, _)) -> true
       | Ok (TOverloaded_fn arities) ->
           List.exists
             (fun (arity : fn_arity) ->
               match arity.fixed_params with
               | TFn _ :: _ -> true
               | _ -> false)
             arities
       | Ok _ | Error _ -> false)
  in
  let specialize_accumulating_hof_parameter_types name parameter_types =
    if has_source_name name "group-by" then
      match parameter_types with
      | _key_fn :: collection_ty :: rest -> (
          match static_seqable_element_type collection_ty with
          | Some element_ty ->
              TFn ([ element_ty ], Type_solver.fresh ())
              :: collection_ty :: rest
          | None -> parameter_types)
      | _ -> parameter_types
    else if core_keep_function_name name then
      match parameter_types with
      | _callback_ty :: collection_ty :: rest -> (
          match static_seqable_element_type collection_ty with
          | Some element_ty ->
              TFn
                ( [ element_ty ],
                  TNullable (Type_solver.fresh ()) )
              :: collection_ty :: rest
          | None -> parameter_types)
      | _ -> parameter_types
    else if not (can_accumulate_overloaded_function_parameter name) then
      parameter_types
    else
      match parameter_types with
      | map_ty :: collection_ty :: rest
        when Option.is_some (Types.dynamic_map_types map_ty)
             || (match map_ty with
                | TRecord _ | TNamed_record _ -> true
                | _ -> false) -> (
          match static_seqable_element_type collection_ty with
          | Some element_ty ->
              TFn ([ element_ty ], TBool) :: collection_ty :: rest
          | None -> parameter_types)
      | TFn ([ parameter_ty ], return_ty) :: collection_ty :: rest -> (
          match static_seqable_element_type collection_ty with
          | Some element_ty ->
              let element_ty =
                (* An open element type (e.g. an empty collection literal)
                   carries no information; keep the callback's own parameter
                   type so capability constraints survive. *)
                if Type_solver.is_open element_ty then parameter_ty
                else element_ty
              in
              let return_ty =
                Types.instantiate_type ~templates:[ parameter_ty ]
                  ~actuals:[ element_ty ] return_ty
              in
              let return_ty =
                match Types.truthy_constraint_info return_ty with
                | Some _ -> return_ty
                | None -> Types.truthy_constraint return_ty
              in
              TFn ([ element_ty ], return_ty) :: collection_ty :: rest
          | None -> parameter_types)
      | (TUnknown | TMeta _ | TVar _) :: collection_ty :: rest -> (
          match static_seqable_element_type collection_ty with
          | Some element_ty ->
              TFn
                ( [ element_ty ],
                  Types.truthy_constraint TUnknown
                )
              :: collection_ty :: rest
          | None -> parameter_types)
      | _ -> parameter_types
  in
  let constrain_protocol_symbol constraint_ty params receiver =
    let value_ty =
      string_assoc_opt receiver params |> Option.value ~default:TUnknown
    in
    match value_ty with
    | TNamed_record _ -> Ok params
    | _ ->
        constrain_symbol
          (Types.protocol_constraint_with_value constraint_ty value_ty)
          params receiver
  in
  let refine_protocol_call_constraint params constraint_ty actual_arguments =
    match Types.protocol_constraint_info constraint_ty with
    | None -> constraint_ty
    | Some (protocol_id, witness_ty, value_ty) -> (
        match Types.protocol_witness_method_types witness_ty with
        | None -> constraint_ty
        | Some methods ->
            let actual_tys =
              List.map (inferred_form_type params) actual_arguments
            in
            let refine_method = function
              | TFn (receiver :: parameters, return_ty)
                when List.length parameters = List.length actual_tys ->
                  let parameters =
                    List.map2
                      (fun expected actual ->
                        match (expected, actual) with
                        | (TUnknown | TMeta _ | TVar _),
                          actual
                          when not
                                 (match actual with
                                 | TUnknown | TMeta _ | TVar _ -> true
                                 | _ -> false) ->
                            actual
                        | expected, _ -> expected)
                      parameters actual_tys
                  in
                  TFn (receiver :: parameters, return_ty)
              | method_ty -> method_ty
            in
            Types.protocol_constraint protocol_id
              (List.map refine_method methods)
              value_ty)
  in
  let branch_depth = ref 0 in
  let branch_hint_symbols = ref [] in
  let with_branch inference =
    incr branch_depth;
    match inference () with
    | result ->
        decr branch_depth;
        result
    | exception exn ->
        decr branch_depth;
        raise exn
  in
  let restore_branch_hints base inferred previous_hints =
    let new_hints =
      List.filter
        (fun name -> not (string_mem name previous_hints))
        !branch_hint_symbols
    in
    List.map
      (fun (name, base_ty) ->
        let inferred_ty =
          string_assoc_opt name inferred |> Option.value ~default:base_ty
        in
        if string_mem name new_hints then
          let restored_ty =
            match
              ( Types.truthy_constraint_info base_ty,
                Types.truthy_constraint_info inferred_ty )
            with
            | Some _, Some _ -> inferred_ty
            | _ -> base_ty
          in
          (name, restored_ty)
        else (name, inferred_ty))
      base
  in
  let rec guarded_protocol_receivers = function
    | FList
        [ FSymbol "satisfies?"; FSymbol _protocol_name; FSymbol receiver ] ->
        [ receiver ]
    | FList
        (FSymbol ("__lg_logical-and" | "__lg_logical-or") :: forms) ->
        List.concat_map guarded_protocol_receivers forms
    | _ -> []
  in
  let restore_guarded_protocol_receivers base inferred condition =
    let guarded = guarded_protocol_receivers condition in
    let rec optionalize_seqable = function
      | TConstraint
          (Seqable_constraint
            ({ requirement = Required; _ } as constraint_)) ->
          TConstraint
            (Seqable_constraint { constraint_ with requirement = Optional })
      | ty -> (
          match Types.protocol_constraint_info ty with
          | Some (_, _, value_ty) ->
              Types.protocol_constraint_with_value ty
                (optionalize_seqable value_ty)
          | None -> ty)
    in
    List.map
      (fun (name, base_ty) ->
        let inferred_ty =
          string_assoc_opt name inferred |> Option.value ~default:base_ty
        in
        if not (string_mem name guarded) then (name, inferred_ty)
        else
          let restored_ty =
            match Types.protocol_constraint_info base_ty with
            | None -> base_ty
            | Some (base_protocol, _, base_value_ty) ->
                let inferred_value_ty =
                  match Types.protocol_constraint_info inferred_ty with
                  | Some (inferred_protocol, _, inferred_value_ty)
                    when Protocol_id.equal base_protocol inferred_protocol ->
                      inferred_value_ty
                  | Some _ -> base_value_ty
                  | None -> inferred_ty
                in
                Types.protocol_constraint_with_value base_ty
                  (refine_type base_value_ty inferred_value_ty
                  |> optionalize_seqable)
          in
          (name, restored_ty))
      base
  in
  let restore_branch_evidence base inferred previous_hints condition =
    restore_branch_hints base inferred previous_hints
    |> fun inferred ->
    restore_guarded_protocol_receivers base inferred condition
  in
  let fresh_type_variable _prefix =
    Type_solver.fresh ()
  in
  let instance_branch_params ~matching params = function
    | FList
        [
          FSymbol "instance?";
          FSymbol record_name;
          FSymbol value_name;
        ] -> (
        match
          ( resolve_named_record (TOcaml record_name),
            string_assoc_opt value_name params )
        with
        | (TNamed_record _ as record_ty), Some value_ty ->
            let stored_ty = Types.constraint_value_type value_ty in
            let narrowed_ty =
              if matching then Some record_ty
              else
                match stored_ty with
                | TNamed_record actual ->
                    let excluded =
                      match record_ty with
                      | TNamed_record record -> record
                      | _ -> assert false
                    in
                    if Type_id.equal excluded.type_id actual.type_id then None
                    else Some stored_ty
                | sum_ty -> (
                    match
                      lookup_closed_sum_constructors sum_ty
                      |> List.filter_map
                           (fun (_constructor, payload_types) ->
                             match payload_types with
                             | [ payload_ty ]
                               when not (Types.equal payload_ty record_ty) ->
                                 Some payload_ty
                             | [] | [ _ ] | _ :: _ :: _ -> None)
                    with
                    | [ payload_ty ] -> Some payload_ty
                    | [] | _ :: _ :: _ -> None)
            in
            Option.fold ~none:params
              ~some:(fun ty -> replace_param value_name ty params)
              narrowed_ty
        | _ -> params)
    | _ -> params
  in
  let restore_instance_branch_param base inferred = function
    | FList [ FSymbol "instance?"; _; FSymbol value_name ] -> (
        match string_assoc_opt value_name base with
        | Some original -> replace_param value_name original inferred
        | None -> inferred)
    | _ -> inferred
  in
  let rec successful_call_refined_symbols = function
    | FList (FSymbol function_name :: arguments) -> (
        match lookup_successful_call_refinement function_name with
        | Some (parameter_index, refined_ty) -> (
            match List.nth_opt arguments parameter_index with
            | Some (FSymbol value_name) -> [ (value_name, refined_ty) ]
            | Some _ | None -> [])
        | None ->
            if
              function_name = "__lg_logical-and"
              || String.ends_with ~suffix:"/__lg_logical-and" function_name
            then List.concat_map successful_call_refined_symbols arguments
            else [])
    | _ -> []
  in
  let successful_call_branch_params params condition =
    successful_call_refined_symbols condition
    |> List.fold_left
         (fun params (value_name, refined_ty) ->
           match string_assoc_opt value_name params with
           | Some _ -> replace_param value_name refined_ty params
           | None -> params)
         params
  in
  let restore_successful_call_branch_params base inferred condition =
    successful_call_refined_symbols condition
    |> List.fold_left
         (fun inferred (value_name, _) ->
           match string_assoc_opt value_name base with
           | Some original -> replace_param value_name original inferred
           | None -> inferred)
         inferred
  in
  let freshen_call_type name ty =
    let _ = name in
    let substitutions =
      Type_solver.variables ty
      |> List.map (fun variable -> (variable, fresh_type_variable "call"))
      |> Type_solver.of_list
    in
    Type_solver.apply substitutions ty
  in
  let inference_function_type params name =
    match string_assoc_opt name params with
    | Some (TFn _ as ty) -> Some ty
    | Some _ | None -> None
  in
  (* A few `__lg_*` builtins have no dedicated inference case and reuse
     their source function's signature (comp/juxt/partial/rest/concat).
     All other `__lg_*` names either have a dedicated case below (which
     encodes the builtin's real, usually looser, semantics) or get plain
     inference; borrowing the source signature there would over-constrain
     them (e.g. `__lg_some`'s callback must not inherit `some`'s
     option-returning predicate signature). *)
  let signature_fallback_builtin = function
    | "__lg_comp" | "__lg_concat" | "__lg_juxt" | "__lg_partial"
    | "__lg_rest" -> true
    | _ -> false
  in
  let lookup_inference_function_type params name args =
    let inferred = inference_function_type params name in
    match inferred with
    | Some ty -> Ok (freshen_call_type name ty)
    | None ->
        (match lookup_call_ty name args with
         | Some ty -> Ok (freshen_call_type name ty)
         | None ->
             let ty =
               match
                 ( lookup_function_ty name,
                   signature_fallback_builtin name )
               with
               | Error _, true -> (
                   let source_name =
                     String.sub name 5 (String.length name - 5)
                   in
                   match lookup_function_ty source_name with
                   | Error _ ->
                       lookup_function_ty ("clojure.core/" ^ source_name)
                   | ok -> ok)
               | result, _ -> result
             in
             Result.map (freshen_call_type name) ty)
  in
  let inferred_hof_argument_type params form =
    let inferred =
      inferred_form_or_call_type ~lookup_function_ty params form
    in
    if not (Type_solver.is_open inferred) then inferred
    else
      match form with
      | FSymbol name when not (string_mem_assoc name params) -> (
          match lookup_function_ty name with
          | Ok ty -> freshen_call_type name ty
          | Error _ -> inferred)
      | _ -> inferred
  in
  let source_sequence_filter_name name =
    (has_source_name name "filter"
    || has_source_name name "filterv"
    || has_source_name name "remove")
    &&
    match lookup_function_ty name with
    | Ok (TFn (TFn _ :: _, _)) -> true
    | Ok (TOverloaded_fn arities) ->
        List.exists
          (fun (arity : fn_arity) ->
            match arity.fixed_params with
            | TFn _ :: _ -> true
            | _ -> false)
          arities
    | Ok _ | Error _ -> false
  in
  let branch_expected_type params expected branch other =
    let branch_is_nullable =
      match inferred_form_type params branch with
      | TNullable _ | TOcaml_app ("option", [ _ ]) -> true
      | _ -> false
    in
    match (other, expected) with
    | FSymbol "nil", (TNullable payload | TOcaml_app ("option", [ payload ]))
      when not branch_is_nullable ->
        payload
    | _ -> expected
  in
  let rec infer_expected expected_ty params = function
    | FList
        [
          FSymbol apply_name;
          FSymbol list_name;
          collection;
        ]
      when (has_source_name apply_name "apply" || String.equal apply_name "__lg_apply")
           && (has_source_name list_name "list"
           || has_source_name list_name "__lg_list") -> (
        match expected_ty with
        | TList element_ty ->
            infer_sequence_form element_ty params collection
        | _ -> (
            match expected_seqable_element_type expected_ty with
            | Some element_ty -> infer_sequence_form element_ty params collection
            | None -> infer_form params collection))
    | (FList (FSymbol apply_name :: FSymbol name :: arguments) as form)
      when has_source_name apply_name "apply"
           || String.equal apply_name "__lg_apply" -> (
        match List.rev arguments, lookup_inference_function_type params name [] with
        | collection :: reversed_fixed, Ok (TOverloaded_fn arities) ->
            let fixed = List.rev reversed_fixed in
            let candidates = List.filter (fun arity ->
              Option.is_some arity.rest_param
              && List.length arity.fixed_params <= List.length fixed) arities in
            (match candidates with
            | [arity] -> (
                match Type_solver.unify Type_solver.empty arity.return_ty expected_ty with
                | Error _ -> infer_form params form
                | Ok substitutions ->
                    let rest_ty = Type_solver.apply substitutions (Option.get arity.rest_param) in
                    let fixed_types = List.map (Type_solver.apply substitutions) arity.fixed_params in
                    let fixed_types = fixed_types @ List.init
                      (List.length fixed - List.length fixed_types) (fun _ -> rest_ty) in
                    Result.bind
                      (List.fold_left2 (fun result expected argument ->
                         Result.bind result (fun params -> infer_expected expected params argument))
                         (Ok params) fixed_types fixed)
                      (fun params ->
                        let actual = inferred_form_or_call_type ~lookup_function_ty params collection in
                        match static_seqable_element_type actual with
                        | Some known when not (Type_solver.is_open known)
                                          && (match known with TRecord _ -> false | _ -> true) ->
                            infer_form params collection
                        | _ -> infer_sequence_form rest_ty params collection))
            | _ -> infer_form params form)
        | _ -> infer_form params form)
    | FList (FSymbol "__lg_concat" :: collections) -> (
        match expected_seqable_element_type expected_ty with
        | Some element_ty when not (Type_solver.is_open element_ty)
                               && (match element_ty with TRecord _ -> false | _ -> true) ->
            List.fold_left
              (fun result collection ->
                Result.bind result (fun params ->
                  let actual = inferred_form_or_call_type ~lookup_function_ty params collection in
                  match static_seqable_element_type actual with
                  | Some known when not (Type_solver.is_open known)
                                    && (match known with TRecord _ -> false | _ -> true) ->
                      infer_form params collection
                  | _ -> infer_expected (Types.seqable_constraint element_ty) params collection))
              (Ok params) collections
        | Some _ | None ->
            let element_ty = fresh_type_variable "concat_element" in
            List.fold_left
              (fun result collection ->
                Result.bind result (fun params ->
                    let actual =
                      inferred_form_or_call_type ~lookup_function_ty params
                        collection
                    in
                    match static_seqable_element_type actual with
                    | Some known
                      when not (Type_solver.is_open known)
                           &&
                           (match known with TRecord _ -> false | _ -> true) ->
                        infer_form params collection
                    | _ ->
                        infer_expected
                          (Types.optional_seqable_constraint element_ty
                             (fresh_type_variable "concat_storage"))
                          params collection))
              (Ok params) collections)
    | FSymbol name ->
        Option.iter (fun observe ->
            Option.iter (observe expected_ty) (string_assoc_opt name params))
          observe_constraint;
        constrain_symbol expected_ty params name
    | FList (FSymbol "__lg_logical-or" :: forms) ->
        let infer_optional_operand result form =
          Result.bind result (fun params ->
              match literal_truthiness form with
              | Some false -> Ok params
              | _ -> infer_expected expected_ty params form)
        in
        let infer_result =
          if optional_type expected_ty then
            List.fold_left infer_optional_operand (Ok params) forms
          else
            match List.rev forms with
            | [] -> Ok params
            | last :: _ -> infer_expected expected_ty params last
        in
        Result.bind infer_result (fun params ->
            infer_truthy params (FList (FSymbol "__lg_logical-or" :: forms)))
    | FList (FSymbol "do" :: body_forms) -> (
        match List.rev body_forms with
        | result :: reversed_prefix ->
            Result.bind
              (infer_all params (List.rev reversed_prefix))
              (fun params -> infer_expected expected_ty params result)
        | [] -> Ok params)
    | FList (FSymbol "tuple" :: items) -> (
        match expected_ty with
        | TTuple item_tys when List.length item_tys = List.length items ->
            List.fold_left2
              (fun result item_ty item ->
                Result.bind result (fun params ->
                    infer_expected item_ty params item))
              (Ok params) item_tys items
        | _ -> infer_all params items)
    | FList [ FSymbol "tag"; FSymbol tag; payload ] ->
        let expected_ty =
          match expected_ty with
          | TOcaml name ->
              Ocaml_signature.of_compiler_type
                (Lg_compiler_support.Ocaml_value.Constructor (name, []))
          | ty -> ty
        in
        (match expected_ty with
        | TPoly_variant row -> (
            match List.assoc_opt tag row.tags with
            | Some (Some payload_ty) -> infer_expected payload_ty params payload
            | _ -> infer_form params payload)
        | _ -> (
            match builtin_poly_tag_payload_type tag with
            | Some payload_ty -> infer_expected payload_ty params payload
            | None -> infer_form params payload))
    | FList [ FSymbol "__lg_nth"; collection; index ] ->
        Result.bind (infer_sequence_form expected_ty params collection)
          (fun params -> infer_expected TInt params index)
    | FList [ FSymbol "__lg_nth"; collection; index; default ] ->
        Result.bind (infer_sequence_form expected_ty params collection)
          (fun params ->
            Result.bind (infer_expected TInt params index) (fun params ->
                infer_expected expected_ty params default))
    | FList [ FSymbol map_name; fn; collection ]
      when has_source_name map_name "__lg_map" || has_source_name map_name "map"
      -> (
        match expected_seqable_element_type expected_ty with
        | Some return_ty
          when not
                 (match return_ty with
                 | TUnknown | TMeta _ | TVar _ -> true
                 | _ -> false)
               && not (Types.is_dynamic return_ty) ->
            let inferred_element_ty = inferred_unary_function_param params fn in
            let inferred_element_ty =
              match inferred_element_ty with
              | TUnknown | TMeta _ | TVar _ ->
                  inferred_literal_collection_item params collection
              | ty -> ty
            in
            let element_ty =
              match inferred_element_ty with
              | TUnknown | TMeta _ | TVar _ ->
                  fresh_type_variable "unary_map_item"
              | ty -> ty
            in
            let element_ty =
              match expected_unary_function_param params return_ty fn with
              | Some expected_param_ty ->
                  refine_type element_ty expected_param_ty
              | None -> element_ty
            in
            Result.bind
              (infer_expected (TFn ([ element_ty ], return_ty)) params fn)
              (fun params -> infer_sequence_form element_ty params collection)
        | Some _ | None -> infer_form params (FList [ FSymbol map_name; fn; collection ]))
    | FList [ FSymbol filter_name; predicate; collection ]
      when source_sequence_filter_name filter_name -> (
        match expected_seqable_element_type expected_ty with
        | Some element_ty when not (Types.is_dynamic element_ty) ->
            let element_ty =
              filter_predicate_parameter_type params predicate element_ty TBool
            in
            Result.bind
              (infer_sequence_form element_ty params collection)
              (fun params ->
                infer_expected (TFn ([ element_ty ], TBool)) params
                  predicate)
        | Some _ | None ->
            infer_form params
              (FList [ FSymbol filter_name; predicate; collection ]))
    | FList [ FSymbol keep_name; fn; collection ]
      when core_keep_function_name keep_name ->
        let result_ty =
          expected_seqable_element_type expected_ty
          |> Option.value ~default:(fresh_type_variable "keep_result")
        in
        let inferred_element_ty = inferred_unary_function_param params fn in
        let inferred_element_ty =
          match inferred_element_ty with
          | TUnknown | TMeta _ | TVar _ ->
              inferred_literal_collection_item params collection
          | ty -> ty
        in
        let element_ty =
          match inferred_element_ty with
          | TUnknown | TMeta _ | TVar _ -> fresh_type_variable "keep_item"
          | ty -> ty
        in
        Result.bind
          (infer_sequence_form element_ty params collection)
          (fun params ->
            infer_expected (TFn ([ element_ty ], TNullable result_ty))
              params fn)
    | FList [ FSymbol "__lg_into"; target; source ] -> (
        match into_source_element_type expected_ty with
        | Some element when not (Types.is_dynamic element) ->
            let element =
              let source_ty =
                match inferred_form_type params source with
                | TUnknown ->
                    inferred_call_return_type ~lookup_function_ty params source
                | ty -> ty
              in
              match into_source_element_type source_ty with
              | Some source_element when not (Types.is_dynamic source_element) ->
                  refine_type element source_element
              | Some _ | None -> element
            in
            Result.bind (infer_expected expected_ty params target)
              (fun params -> infer_sequence_form element params source)
        | _ -> infer_form params (FList [ FSymbol "__lg_into"; target; source ]))
    | FList
        (FSymbol "__lg_conj"
        :: (FList [ FSymbol "__lg_get"; _; _ ] as target)
        :: values) -> infer_conj_get params target values
    | FList (FSymbol "__lg_conj" :: target :: values) -> (
        match expected_ty with
        | TList element_ty | TVector element_ty | TSet element_ty
        | TSeq element_ty ->
            Result.bind (infer_expected expected_ty params target)
              (fun params -> infer_expected_all element_ty params values)
        | _ -> infer_all params (target :: values))
    | FList [ FSymbol "__lg_complement"; predicate ] -> (
        match expected_ty with
        | TFn (parameter_tys, _return_ty)
          when List.for_all Expression_support.concrete_constraint_type
                 parameter_tys ->
            infer_expected
              (TFn
                 ( parameter_tys,
                   Types.truthy_constraint
                     (fresh_type_variable "complement_result") ))
              params predicate
        | _ -> infer_form params predicate)
    | FList (FSymbol "__lg_list-star" :: arguments) -> (
        match List.rev arguments with
        | tail :: prefix ->
            let element_ty =
              List.fold_left
                (fun ty value -> refine_type ty (inferred_binding_form_type params value))
                (static_seqable_element_type expected_ty
                 |> Option.value ~default:TUnknown) prefix
            in
            let element_ty = match element_ty with
              | TUnknown | TMeta _ | TVar _ -> Type_solver.fresh ()
              | ty -> ty
            in
            Result.bind (infer_expected_all element_ty params prefix) (fun params ->
                infer_expected (Types.seqable_constraint element_ty) params tail)
        | [] -> Ok params)
    | FList [ FSymbol "__lg_cons"; value; collection ] ->
        let element_ty =
          match expected_ty with
          | TSeq inner | TList inner | TVector inner | TSet inner -> inner
          | _ -> inferred_form_type params value
        in
        Result.bind (infer_expected element_ty params value) (fun params ->
            infer_expected (Types.seqable_constraint element_ty) params
              collection)
    | FList [ FSymbol predicate; value ]
      when has_source_name predicate "__lg_reduced-predicate"
           || has_source_name predicate "reduced?" ->
        infer_form params value
    | FList
        (FSymbol "fn" :: FSymbol _name :: (FVector _ as fn_params)
        :: body_forms) ->
        infer_expected expected_ty params
          (FList (FSymbol "fn" :: fn_params :: body_forms))
    | FList (FSymbol "fn" :: (FVector _ as fn_params) :: body_forms) -> (
        match (expected_ty, Destructure.parse_param_specs fn_params) with
        | TFn (parameter_tys, return_ty), Ok specs
          when List.length parameter_tys = List.length specs ->
            let local_bindings =
              List.map2
                (fun (spec : Destructure.param_spec) parameter_ty ->
                  let parameter_ty =
                    match parameter_ty with
                    | TUnknown | TMeta _ | TVar _ -> TUnknown
                    | ty -> ty
                  in
                  let destructured =
                    if spec.destructured then
                      let hints =
                        Destructure.pattern_type_hints spec.pattern parameter_ty
                      in
                      Destructure.pattern_names spec.pattern
                      |> List.map (fun name ->
                             ( name,
                               List.assoc_opt name hints
                               |> Option.value ~default:TUnknown ))
                    else []
                  in
                  (spec.source_name, parameter_ty) :: destructured)
                specs parameter_tys
              |> List.concat
            in
            let local_names = List.map fst local_bindings in
            let shadowed =
              List.filter (fun (name, _) -> string_mem name local_names) params
            in
            let function_params =
              local_bindings
              @ List.filter
                  (fun (name, _) -> not (string_mem name local_names))
                  params
            in
            let infer_body =
              match List.rev body_forms with
              | [] -> Ok function_params
              | result :: reversed_prefix ->
                  Result.bind
                    (infer_all function_params (List.rev reversed_prefix))
                    (fun params ->
                      match return_ty with
                      | TUnknown | TMeta _ | TVar _ -> infer_form params result
                      | TRecord _ as ty -> (
                          match
                            inferred_form_or_call_type ~lookup_function_ty params
                              result
                            |> resolve_named_record
                          with
                          | TNamed_record _ -> infer_form params result
                          | _ -> infer_expected ty params result)
                      | ty -> infer_expected ty params result)
            in
            Result.map
              (fun inferred ->
                let inferred =
                  restore_explicit_parameter_types ~resolve_named_record specs
                    inferred
                in
                let substitutions =
                  List.fold_left2
                    (fun substitutions (spec : Destructure.param_spec) expected ->
                      let lookup name =
                        string_assoc_opt name inferred
                        |> Option.value ~default:TUnknown
                      in
                      let actual =
                        if spec.destructured then
                          (match expected with
                          | TTuple _ ->
                              Destructure.infer_generator_pattern_type spec.pattern lookup
                          | _ -> Destructure.infer_pattern_type spec.pattern lookup)
                          |> Result.value ~default:TUnknown
                        else lookup spec.source_name
                      in
                      Type_solver.unify substitutions expected actual
                      |> Result.value ~default:substitutions)
                    Type_solver.empty specs parameter_tys
                in
                shadowed
                @ List.filter
                    (fun (name, _) -> not (string_mem name local_names))
                    (List.map (fun (name, ty) -> name, Type_solver.apply substitutions ty)
                       inferred))
              infer_body
        | _ -> infer_all params body_forms)
    | FList
        [
          FSymbol "__lg_some-thread";
          FVector [ FSymbol binding; option_form ];
          then_form;
        ] -> (
        let inferred_option_ty =
          inferred_binding_form_type params option_form
        in
        let initial_payload_ty =
          match inferred_option_ty with
          | TNullable inner | TOcaml_app ("option", [ inner ]) -> inner
          | _ -> fresh_type_variable "option"
        in
        let shadowed = string_assoc_opt binding params in
        let branch_params =
          (binding, initial_payload_ty) :: string_remove_assoc binding params
        in
        match infer_expected expected_ty branch_params then_form with
        | Error _ as error -> error
        | Ok branch_params ->
            let payload_ty =
              string_assoc_opt binding branch_params
              |> Option.value ~default:initial_payload_ty
            in
            let params = string_remove_assoc binding branch_params in
            let params =
              match shadowed with
              | None -> params
              | Some ty -> (binding, ty) :: params
            in
            infer_expected (TNullable payload_ty) params option_form)
    | FList [ FSymbol "if"; condition; then_form; else_form ] ->
        Result.bind (infer_truthy params condition) (fun params ->
            match literal_truthiness condition with
            | Some true -> infer_expected expected_ty params then_form
            | Some false -> infer_expected expected_ty params else_form
            | None ->
                let previous_hints = !branch_hint_symbols in
                let then_params =
                  instance_branch_params ~matching:true params condition
                  |> fun params ->
                  successful_call_branch_params params condition
                in
                let then_expected =
                  branch_expected_type then_params expected_ty then_form
                    else_form
                in
                Result.bind
                  (with_branch (fun () ->
                       infer_expected then_expected then_params then_form))
                  (fun inferred ->
                    let inferred =
                      restore_instance_branch_param params inferred condition
                      |> fun inferred ->
                      restore_successful_call_branch_params params inferred
                        condition
                    in
                    let else_params =
                      instance_branch_params ~matching:false inferred condition
                    in
                    let else_expected =
                      branch_expected_type else_params expected_ty else_form
                        then_form
                    in
                    Result.map
                      (fun inferred ->
                        let inferred =
                          restore_instance_branch_param params inferred condition
                          |> fun inferred ->
                          restore_successful_call_branch_params params inferred
                            condition
                        in
                        restore_branch_evidence params inferred previous_hints
                          condition)
                      (with_branch (fun () ->
                           infer_expected else_expected else_params else_form))))
    | FList [ FSymbol "if"; condition; then_form ] ->
        Result.bind (infer_truthy params condition) (fun params ->
            let previous_hints = !branch_hint_symbols in
            let then_params =
              successful_call_branch_params params condition
            in
            let then_expected =
              branch_expected_type then_params expected_ty then_form
                (FSymbol "nil")
            in
            Result.map
              (fun inferred ->
                restore_successful_call_branch_params params inferred condition
                |> fun inferred ->
                restore_branch_evidence params inferred previous_hints condition)
              (with_branch (fun () ->
                   infer_expected then_expected then_params then_form)))
    | ( FList
          [
            FSymbol ("__lg_if-some" | "__lg_if-let");
            FVector [ FSymbol _binding; _option_form ];
            _then_form;
            else_form;
          ] as form ) ->
        Result.bind (infer_form params form) (fun params ->
            infer_expected expected_ty params else_form)
    | FList [ FSymbol "Some"; value ] -> (
        match expected_ty with
        | TNullable value_ty | TOcaml_app ("option", [ value_ty ]) ->
            infer_expected value_ty params value
        | _ -> infer_form params value)
    | FList [ FSymbol ("__lg_atom" | "__lg_volatile!"); value ] -> (
        match expected_ty with
        | TRef value_ty -> infer_expected value_ty params value
        | _ -> infer_form params value)
    | FList [ FSymbol "__lg_reset-meta!"; reference; metadata ] ->
        Result.bind (infer_form params reference) (fun params ->
            infer_form params metadata)
    | FList [ FSymbol "__lg_add-watch"; reference; key; callback ] -> (
        let value_ty =
          match inferred_form_type params reference with
          | TRef value_ty -> value_ty
          | _ -> (
              match expected_ty with
              | TRef value_ty -> value_ty
              | _ -> Type_solver.fresh ())
        in
        Result.bind (infer_expected (TRef value_ty) params reference)
          (fun params ->
            Result.bind (infer_expected TKeyword params key) (fun params ->
                infer_expected
                  (TFn
                     ([ TKeyword; TRef value_ty; value_ty; value_ty ], TUnknown))
                  params callback)))
    | FList [ FSymbol "__lg_remove-watch"; reference; key ] ->
        let value_ty =
          match inferred_form_type params reference with
          | TRef value_ty -> value_ty
          | _ -> (
              match expected_ty with
              | TRef value_ty -> value_ty
              | _ -> Type_solver.fresh ())
        in
        Result.bind (infer_expected (TRef value_ty) params reference)
          (fun params -> infer_expected TKeyword params key)
    | FList (FSymbol "__lg_list" :: values) -> (
        let element_ty =
          match expected_ty with
          | TList element_ty -> Some element_ty
          | _ -> Types.seqable_constraint_element expected_ty
        in
        match element_ty with
        | Some element_ty when not (Types.is_dynamic element_ty) ->
            infer_expected_all element_ty params values
        | Some _ | None -> infer_all params values)
    | FVector values -> (
        let element_ty =
          match expected_ty with
          | TVector element_ty -> Some element_ty
          | _ -> Types.seqable_constraint_element expected_ty
        in
        match (element_ty, expected_ty) with
        | _, TTuple item_tys when List.length item_tys = List.length values ->
            (* A vector literal may stand in for a pair/entry value
               (e.g. map-entry results feeding `into`), so constrain
               its elements pairwise. *)
            List.fold_left2
              (fun result item_ty value ->
                Result.bind result (fun params ->
                    infer_expected item_ty params value))
              (Ok params) item_tys values
        | Some element_ty, _ -> infer_expected_all element_ty params values
        | None, _ -> infer_all params values)
    | FList [ FSymbol "weak-ref"; value ] -> (
        match Types.weak_element expected_ty with
        | Some value_ty -> infer_expected value_ty params value
        | None -> infer_form params value)
    | FList [ FSymbol "__lg_weak-deref"; reference ] -> (
        match expected_ty with
        | TNullable value_ty | TOcaml_app ("option", [ value_ty ]) ->
            infer_expected (Types.weak_type value_ty) params reference
        | _ -> infer_form params reference)
    | FList (FSymbol "delay" :: body_forms) -> (
        match List.rev body_forms with
        | result :: reversed_prefix ->
            Result.bind (infer_all params (List.rev reversed_prefix)) (fun params ->
                infer_expected expected_ty params result)
        | [] -> Ok params)
    | FList
        [
          FSymbol "IDeref/-deref";
          FList [ FSymbol field_access; target ];
        ]
      when String.starts_with ~prefix:".-" field_access ->
        let keyword =
          ":" ^ String.sub field_access 2 (String.length field_access - 2)
        in
        let field_ty = TRef expected_ty in
        (match hinted_symbol_target resolve_named_record target with
        | Some (name, Some hinted_ty) ->
            Result.bind (constrain_symbol hinted_ty params name) (fun params ->
                add_record_field_constraint name keyword field_ty params)
        | Some (name, None) ->
            add_record_field_constraint name keyword field_ty params
        | None ->
            infer_expected (TRecord [ make_field keyword field_ty ]) params
              target)
    | FList
        [ FSymbol "IDeref/-deref"; FList [ FKeyword keyword; FSymbol receiver ] ] ->
        add_record_field_constraint receiver keyword (TRef expected_ty) params
    | (FList [ FSymbol "IDeref/-deref"; FSymbol reference ] as form) -> (
        match string_assoc_opt reference params with
        | _ when Option.is_some (Types.seqable_constraint_info expected_ty) ->
            (* A sequence view does not determine the mutable cell's storage type. *)
            infer_form params form
        | Some (TOcaml_app ("Lazy.t", [ _ ])) ->
            constrain_symbol
              (TOcaml_app ("Lazy.t", [ expected_ty ]))
              params reference
        | Some _ | None -> constrain_symbol (TRef expected_ty) params reference)
    | FList (FSymbol let_name :: bindings :: body_forms)
      when let_name = "let" || let_name = "let*"
           || String.ends_with ~suffix:"/let" let_name
           || String.ends_with ~suffix:"/let*" let_name ->
        infer_let ~expected_body:expected_ty params bindings body_forms
    | FList
        ((FSymbol "__lg_assoc" | FCoreSymbol Core_assoc) :: target :: pairs) -> (
        match Types.record_fields expected_ty with
        | None -> infer_assoc params target pairs
        | Some expected_fields ->
            let rec assigned_keywords assigned = function
              | FKeyword keyword :: _value :: rest ->
                  assigned_keywords (keyword :: assigned) rest
              | _key :: _value :: rest -> assigned_keywords assigned rest
              | _ -> assigned
            in
            let assigned = assigned_keywords [] pairs in
            let preserved =
              List.filter
                (fun (field : field) ->
                  not (string_mem field.keyword assigned))
                expected_fields
            in
            let infer_target =
              match target with
              | FSymbol name ->
                  List.fold_left
                    (fun result (field : field) ->
                      Result.bind result (fun params ->
                          add_record_field_constraint name field.keyword
                            field.ty params))
                    (Ok params) preserved
              | target when preserved = [] -> infer_form params target
              | target -> infer_expected (TRecord preserved) params target
            in
            Result.bind infer_target (fun params ->
                infer_assoc ~constrain_assigned:false ~expected_fields params
                  target pairs))
    | FList [ FSymbol operation; array; from; length ]
      when String.equal operation "Array.sub"
           && (match expected_ty with
              | TArray _ | TOcaml_app ("array", [ _ ]) -> true
              | _ -> false) ->
        let element_ty =
          match expected_ty with
          | TArray element_ty | TOcaml_app ("array", [ element_ty ]) ->
              element_ty
          | _ -> assert false
        in
        Result.bind (infer_expected (TArray element_ty) params array)
          (fun params ->
            Result.bind (infer_expected TInt params from) (fun params ->
                infer_expected TInt params length))
    | FList [ FSymbol operation; FSymbol array; index ]
      when has_source_name operation "__lg_aget"
           || has_source_name operation "unsafe-aget" -> (
        match constrain_symbol (TArray expected_ty) params array with
        | Error _ as error -> error
        | Ok params -> (
            match (operation, index) with
            | "__lg_aget", FSymbol index ->
                constrain_array_index_symbol params index
            | _ ->
                let index_ty = inferred_form_type params index in
                infer_expected
                  (if Types.equal index_ty TFloat then TFloat else TInt)
                  params index))
    | FList [ FSymbol operation; FSymbol name ]
      when string_mem_assoc name params
           && (has_source_name operation "__lg_keys"
              || has_source_name operation "__lg_vals") ->
        let element_ty =
          Types.seqable_constraint_element expected_ty
          |> Option.value
               ~default:(fresh_type_variable "map_projection_element")
        in
        let other_ty = fresh_type_variable "map_projection_other" in
        let map_ty =
          if has_source_name operation "__lg_keys" then
            Types.dynamic_map element_ty other_ty
          else Types.dynamic_map other_ty element_ty
        in
        constrain_symbol map_ty params name
    | FList (FSymbol name :: args) when string_mem_assoc name params -> (
        let parameter_types =
          List.mapi
            (fun index argument ->
              let argument_ty =
                if can_accumulate_overloaded_function_parameter name then
                  inferred_hof_argument_type params argument
                else
                  inferred_form_or_call_type ~lookup_function_ty params
                    argument
              in
              let argument_ty =
                if Types.equal argument_ty TUnknown then
                  inferred_call_return_type ~lookup_function_ty params argument
                else argument_ty
              in
              match argument_ty with
              | TUnknown ->
                  fresh_type_variable
                    ("call_" ^ Names.sanitize_name name ^ "_"
                   ^ string_of_int index)
              | ty -> ty)
            args
        in
        let parameter_types =
          match string_assoc_opt name params with
          | Some (TFn (existing_parameter_types, _))
            when List.length existing_parameter_types = List.length args ->
              List.map2
                (fun existing (argument, inferred) ->
                  if
                    Types.is_dynamic inferred
                    && contextual_lookup_argument existing argument
                  then existing
                  else inferred)
                existing_parameter_types
                (List.combine args parameter_types)
          | Some _ | None -> parameter_types
        in
        let parameter_types =
          specialize_accumulating_hof_parameter_types name parameter_types
          |> List.map resolve_named_record
        in
        match
          constrain_symbol (TFn (parameter_types, expected_ty)) params name
        with
        | Error _ as error -> error
        | Ok params ->
            let params =
              match (expected_ty, string_assoc_opt name params) with
              | ( (TOcaml _ | TOcaml_app _ | TNamed_record _),
                  Some (TFn _ as current_ty) ) ->
                  let expected_fn_ty = TFn (parameter_types, expected_ty) in
                  let refined = refine_type current_ty expected_fn_ty in
                  if Types.equal refined current_ty then params
                  else replace_param name refined params
              | _, (Some _ | None) -> params
            in
            List.fold_left2
              (fun result expected argument ->
                Result.bind result (fun params ->
                    infer_expected expected params
                      argument))
              (Ok params) parameter_types args)
    | FList
      (FSymbol
         ( "__lg_add" | "__lg_subtract" | "__lg_multiply" | "__lg_divide"
         | "__lg_divide-melange" | "__lg_max" | "__lg_min" )
      :: args)
      when Types.equal expected_ty TInt
           || Types.equal expected_ty TFloat
           || Types.equal expected_ty (TOcaml "Lg_runtime.Runtime_decimal.t") ->
        infer_expected_all expected_ty params args
    | FList
        [ FKeyword nested_keyword; FList [ FKeyword keyword; FSymbol name ] ] ->
        add_record_field_constraint name keyword
          (TRecord [ make_field nested_keyword expected_ty ])
          params
    | FList [ FKeyword keyword; FSymbol name ] ->
        add_record_field_constraint name keyword expected_ty params
    | FList [ FKeyword keyword; FSymbol name; default ]
      when Option.is_some (Types.printable_constraint_info expected_ty) ->
        let field_ty = inferred_form_type params default in
        Result.bind
          (add_record_field_constraint name keyword (TNullable field_ty) params)
          (fun params -> infer_expected field_ty params default)
    | FList [ FKeyword keyword; FSymbol name; default ] ->
        Result.bind
          (add_record_field_constraint name keyword (TNullable expected_ty) params)
          (fun params -> infer_expected expected_ty params default)
    | FList
        [
          FKeyword keyword;
          FList
            [ FSymbol "__lg_first"; collection ];
        ] ->
        let target_ty = TRecord [ make_field keyword expected_ty ] in
        infer_sequence_form target_ty params collection
    | FList [ FKeyword keyword; target ] ->
        let target_ty = inferred_form_or_call_type ~lookup_function_ty params target in
        (match Types.dynamic_map_types target_ty with
        | Some _ -> infer_form params target
        | None -> infer_expected (TRecord [make_field keyword expected_ty]) params target)
      | FList
          [
            FSymbol "__lg_first";
            FSymbol collection;
        ] -> (
        let expected_element_ty =
          match expected_ty with
          | TNullable inner | TOcaml_app ("option", [ inner ]) -> inner
          | ty -> ty
        in
        match string_assoc_opt collection params with
        | Some _ | None -> constrain_seqable expected_element_ty params collection)
    | FList [ FSymbol "__lg_first"; collection ] ->
        let expected_element_ty =
          match expected_ty with
          | TNullable inner | TOcaml_app ("option", [ inner ]) -> inner
          | ty -> ty
        in
        infer_sequence_form expected_element_ty params collection
    | FList [ FSymbol field_access; target ]
      when String.starts_with ~prefix:".-" field_access ->
        let keyword =
          ":"
          ^ String.sub field_access 2 (String.length field_access - 2)
        in
        let field_ty =
          if Types.is_dynamic expected_ty then TUnknown else expected_ty
        in
        (match hinted_symbol_target resolve_named_record target with
        | Some (name, Some hinted_ty) ->
            Result.bind (constrain_symbol hinted_ty params name) (fun params ->
                add_record_field_constraint name keyword field_ty params)
        | Some (name, None) ->
            add_record_field_constraint name keyword field_ty params
        | None ->
            infer_expected (TRecord [ make_field keyword field_ty ]) params
              target)
    | FList
        [
          (FSymbol "__lg_get" | FCoreSymbol Core_get);
          FSymbol name;
          FKeyword keyword;
        ] ->
        add_record_field_constraint name keyword expected_ty params
    | FList [ FSymbol name; key_fn; collection ]
      when has_source_name name "group-by"
           && Option.is_some (Types.dynamic_map_types expected_ty) -> (
        let key_ty, value_ty =
          Types.dynamic_map_types expected_ty |> Option.get
        in
        let bucket_element_ty =
          match value_ty with
          | TVector element_ty | TList element_ty | TSeq element_ty
          | TSet element_ty ->
              Some element_ty
          | ty -> Types.seqable_constraint_element ty
        in
        match bucket_element_ty with
        | Some element_ty ->
            let key_param_ty =
              match key_fn with
              | FKeyword keyword ->
                  TRecord [ make_field keyword key_ty ]
              | _ -> inferred_unary_function_param params key_fn
            in
            let collection_element_ty =
              refine_type element_ty key_param_ty
            in
            Result.bind
              (infer_sequence_form collection_element_ty params collection)
              (fun params ->
                match key_fn with
                | FKeyword _ -> Ok params
                | _ ->
                    infer_expected
                      (TFn ([ collection_element_ty ], key_ty))
                      params key_fn)
        | None -> infer_form params (FList [ FSymbol name; key_fn; collection ]))
    | FList [ FSymbol "__lg_find"; target; key ] ->
        Result.bind (infer_form params target) (fun params ->
            infer_form params key)
    | FList
        [
          (FSymbol "__lg_get" | FCoreSymbol Core_get);
          target;
          key;
          default;
        ] ->
        Result.bind (infer_form params target) (fun params ->
            Result.bind (infer_form params key) (fun params ->
                infer_expected expected_ty params default))
    | FList
        [
          (FSymbol "__lg_get" | FCoreSymbol Core_get);
          FSymbol target;
          key;
        ] -> (
        let record_ty = lookup_dynamic_key_record_type expected_ty in
        match record_ty with
        | Some record_ty ->
            let constrain_target =
              match string_assoc_opt target params with
              | Some inferred_ty
                when Types.is_dynamic inferred_ty ->
                  let capability =
                    Types.dynamic_constraint_info inferred_ty
                    |> Option.value ~default:TUnknown
                  in
                  Ok
                    (replace_param target
                       (refine_type capability record_ty)
                       params)
              | Some _ | None -> constrain_symbol record_ty params target
            in
            Result.bind constrain_target (fun params ->
                infer_expected TKeyword params key)
        | None ->
            let value_ty =
              match expected_ty with
              | TNullable inner | TOcaml_app ("option", [ inner ]) -> inner
              | ty -> ty
            in
            (match
               Option.bind
                 (string_assoc_opt target params)
                 Types.dynamic_map_types
             with
            | Some (key_ty, existing_value_ty) ->
                let value_ty = refine_type existing_value_ty value_ty in
                Result.bind
                  (constrain_symbol
                     (Types.dynamic_map key_ty value_ty)
                     params target)
                  (fun params -> infer_expected key_ty params key)
            | None ->
                let key_ty =
                  match inferred_form_type params key with
                  | TUnknown -> fresh_type_variable "map_key"
                  | ty -> ty
                in
                Result.bind
                  (constrain_symbol
                     (Types.dynamic_map key_ty value_ty)
                     params target)
                  (fun params -> infer_expected key_ty params key)))
    | FList
        [
          (FSymbol "__lg_get" | FCoreSymbol Core_get);
          target;
          key;
        ] ->
        let target_ty = inferred_form_type params target in
        if match target_ty with TVector _ -> true | _ -> false then
          Result.bind
            (infer_expected (TVector expected_ty) params target)
            (fun params -> infer_expected TInt params key)
        else
          let key_ty =
            match inferred_form_type params key with
            | TUnknown -> fresh_type_variable "map_key"
            | ty -> ty
          in
          let value_ty =
            match expected_ty with
            | TNullable inner | TOcaml_app ("option", [ inner ]) -> inner
            | ty -> ty
          in
          Result.bind
            (infer_expected (Types.dynamic_map key_ty value_ty) params target)
            (fun params -> infer_expected key_ty params key)
    | FMap pairs
      when Option.is_some (nested_seqable_map_entry_type expected_ty) ->
        let entry_ty = Option.get (nested_seqable_map_entry_type expected_ty) in
        pairs
        |> List.fold_left
             (fun result (key, value) ->
               Result.bind result (fun params ->
                   Result.bind (infer_expected entry_ty params key) (fun params ->
                       infer_expected entry_ty params value)))
             (Ok params)
    | FMap pairs when Option.is_some (Types.dynamic_map_types expected_ty) ->
        let key_ty, value_ty =
          Option.get (Types.dynamic_map_types expected_ty)
        in
        pairs
        |> List.fold_left
             (fun result (key, value) ->
               Result.bind result (fun params ->
                   Result.bind (infer_expected key_ty params key) (fun params ->
                       infer_expected value_ty params value)))
             (Ok params)
    | FMap pairs when Option.is_some (Types.record_fields expected_ty) ->
        let fields =
          Types.record_fields expected_ty |> Option.value ~default:[]
        in
        pairs
        |> List.fold_left
             (fun result (key, value) ->
               Result.bind result (fun params ->
                   match key with
                   | FKeyword keyword -> (
                       match Types.find_field keyword fields with
                       | Some field -> infer_expected field.ty params value
                       | None -> infer_form params value)
                   | key ->
                       Result.bind (infer_form params key) (fun params ->
                           infer_form params value)))
             (Ok params)
    | FMap pairs when Types.is_dynamic expected_ty ->
        pairs
        |> List.fold_left
             (fun result (key, value) ->
               match result with
               | Error _ as error -> error
               | Ok params -> (
                   match infer_expected expected_ty params key with
                   | Error _ as error -> error
                   | Ok params -> infer_expected expected_ty params value))
             (Ok params)
    | (FList [ FSymbol "__lg_contains"; _target; _key ] as form) ->
        infer_form params form
    | FList (FSymbol method_name :: args)
      when Option.is_some (lookup_protocol_constraint method_name) ->
        infer_known_call ~expected_return_ty:expected_ty method_name params args
    | FList (FSymbol name :: args) -> (
        let form = FList (FSymbol name :: args) in
        let infer_call parameter_tys return_ty =
          Option.iter (fun observe -> observe return_ty expected_ty) observe_constraint;
          Option.iter (fun observe ->
              observe name args (List.map (inferred_form_type params) args)) observe_call;
          if List.length parameter_tys <> List.length args then
            infer_form params form
          else
            let return_ty_for_unification =
              match (return_ty, expected_ty) with
              | ( (TNullable payload_ty
                  | TOcaml_app ("option", [ payload_ty ])),
                  expected_ty )
                when not
                       (match expected_ty with
                       | TNullable _ | TOcaml_app ("option", [ _ ]) -> true
                       | _ -> false) ->
                  payload_ty
              | return_ty, _ -> return_ty
            in
            let expected_return_ty =
              match
                contextual_seqable_return_type expected_ty
                  return_ty_for_unification
              with
              | Some expected_return_ty -> expected_return_ty
              | None -> (
              match (expected_ty, parameter_tys, return_ty_for_unification) with
              | ( TConstraint
                    (Seqable_constraint
                      { requirement = Required; element = element_ty; _ }),
                  [ TArray parameter_ty ],
                  TSeq return_ty )
                when Result.is_ok
                          (Type_solver.unify Type_solver.empty parameter_ty
                             return_ty) ->
                  TSeq element_ty
              | _ -> expected_ty)
            in
            let expected_return_ty =
              Expression_support.contextual_variant_type expected_return_ty
                return_ty_for_unification
            in
            (* Callback inputs and the expected result can constrain the same row. *)
            let callback_substitutions =
              List.fold_left2
                (fun substitutions parameter_ty argument ->
                  match parameter_ty with
                  | TFn (expected_params, _) ->
                      let actual_params = inferred_function_parameter_types params argument in
                      if List.length expected_params <> List.length actual_params then substitutions
                      else List.fold_left2
                        (fun substitutions expected actual ->
                          Type_solver.unify substitutions expected actual
                          |> Result.value ~default:substitutions)
                        substitutions expected_params actual_params
                  | _ -> substitutions)
                Type_solver.empty parameter_tys args
            in
            let expected_return_ty =
              refine_type expected_return_ty
                (Type_solver.apply callback_substitutions return_ty_for_unification)
            in
            let substitutions =
              match
                Type_solver.unify Type_solver.empty return_ty_for_unification
                  expected_return_ty
              with
              | Ok substitutions -> Some substitutions
              | Error _
                when Types.row_compatible ~expected:expected_return_ty
                       ~actual:return_ty_for_unification ->
                  Some Type_solver.empty
              | Error _ -> None
            in
            match substitutions with
            | None -> infer_form params form
            | Some substitutions ->
                let substitutions =
                  List.fold_left2
                    (fun substitutions parameter_ty argument ->
                      let actual_ty =
                        inferred_form_or_call_type ~lookup_function_ty params argument
                      in
                      if
                        Types.equal actual_ty TUnknown
                        || Types.is_dynamic actual_ty
                        || match actual_ty with TMeta _ | TVar _ -> true | _ -> false
                      then substitutions
                      else
                        Type_solver.unify substitutions parameter_ty actual_ty
                        |> Result.value ~default:substitutions)
                    substitutions parameter_tys args
                in
                let parameter_tys =
                  List.map
                    (fun ty -> Type_solver.apply substitutions ty |> resolve_named_record)
                    parameter_tys
                in
                let return_ty = Type_solver.apply substitutions return_ty in
                let params =
                  match inference_function_type params name with
                  | Some existing
                    when Type_solver.variables existing = [] ->
                      replace_param name (TFn (parameter_tys, return_ty)) params
                  | Some _ | None -> params
                in
                List.fold_left2
                  (fun result expected argument ->
                    Result.bind result (fun params ->
                        infer_expected expected params argument))
                  (Ok params) parameter_tys args
        in
        match lookup_inference_function_type params name args with
        | Ok (TFn (parameter_tys, return_ty)) ->
            infer_call parameter_tys return_ty
        | Ok (TOverloaded_fn arities) -> (
            match select_fn_arity arities (List.length args) with
            | None -> infer_form params form
            | Some arity ->
                let parameter_tys =
                  arity.fixed_params
                  @
                  match arity.rest_param with
                  | None -> []
                  | Some rest_ty ->
                      List.init
                        (List.length args - List.length arity.fixed_params)
                        (fun _ -> rest_ty)
                in
                infer_call parameter_tys arity.return_ty)
        | Ok ty when Option.is_some (Types.constant_function_result ty) ->
            infer_all params args
        | _ -> infer_form params form)
    | form -> infer_form params form
  and infer_all params forms =
    let rec loop params = function
      | [] -> Ok params
      | form :: rest -> (
          match infer_form params form with
          | Error _ as err -> err
          | Ok params -> loop params rest)
    in
    Result.bind (infer_record_constraints_all params forms) (fun params -> loop params forms)
  and infer_record_constraints params = function
    | (FList (FSymbol "record" :: FSymbol _ :: _) as form) -> infer_form params form
    | FList (FSymbol "try" :: forms) ->
        let body_or_finally, catch_bodies =
          forms
          |> List.fold_left
               (fun (body, catches) -> function
                 | FList (FSymbol "catch" :: _pattern :: body_forms) ->
                     (body, body_forms :: catches)
                 | FList (FSymbol "finally" :: body_forms) ->
                     (body @ body_forms, catches)
                 | form -> (body @ [ form ], catches))
               ([], [])
        in
        infer_record_constraints_all params
          (body_or_finally @ List.concat (List.rev catch_bodies))
    | FList
        (FSymbol ("fn" | "match" | "if" | "__lg_if-some" | "__lg_if-let"
                 | "__lg_logical-and" | "__lg_logical-or") :: _) -> Ok params
    | FList (FSymbol ("let" | "let*" | "loop") :: FVector bindings :: body) ->
        let rec bindings_constraints params hidden = function
          | pattern :: value :: rest ->
              Result.bind (infer_record_constraints params value) (fun params ->
                  let names = Destructure.pattern_names pattern in
                  let shadowed = List.filter (fun (name, _) -> List.mem name names) params in
                  bindings_constraints
                    (List.filter (fun (name, _) -> not (List.mem name names)) params)
                    (shadowed @ hidden) rest)
          | _ ->
              Result.map (fun inferred -> hidden @ inferred)
                (infer_record_constraints_all params body)
        in
        bindings_constraints params [] bindings
    | FList forms | FVector forms -> infer_record_constraints_all params forms
    | FMap entries ->
        infer_record_constraints_all params
          (List.concat_map (fun (key, value) -> [key; value]) entries)
    | _ -> Ok params
  and infer_record_constraints_all params forms =
    List.fold_left
      (fun result form -> Result.bind result (fun params -> infer_record_constraints params form))
      (Ok params) forms
  and infer_expected_all expected_ty params forms =
    let rec loop params = function
      | [] -> Ok params
      | form :: rest -> (
          match infer_expected expected_ty params form with
          | Error _ as err -> err
          | Ok params -> loop params rest)
    in
    loop params forms
  and infer_exception_data_literal params = function
    | FSymbol "nil" | FBool _ | FInt _ | FFloat _ | FChar _ | FString _
    | FRegex _ | FKeyword _ ->
        Ok params
    | FSymbol name -> constrain_exception_data_symbol params name
    | FList [ FSymbol ("quote" | "clojure.core/quote"); FSymbol _ ] ->
        Ok params
    | FVector values -> infer_exception_data_values params values
    | FMap entries -> infer_exception_data_entries params entries
    | form -> infer_form params form
  and infer_exception_data_values params = function
    | [] -> Ok params
    | value :: rest ->
        Result.bind
          (infer_exception_data_literal params value)
          (fun params -> infer_exception_data_values params rest)
  and infer_exception_data_entries params = function
    | [] -> Ok params
    | (key, value) :: rest ->
        Result.bind
          (infer_exception_data_literal params key)
          (fun params ->
            Result.bind
              (infer_exception_data_literal params value)
              (fun params -> infer_exception_data_entries params rest))
  and infer_truthy params = function
    | FList (FSymbol "__lg_logical-and" :: conditions) ->
        let optionalize_guard params = function
          | FSymbol name -> (
              match string_assoc_opt name params with
              | Some ty -> (
                  match Types.truthy_constraint_info ty with
                  | Some (TBool | TUnknown | TMeta _ | TVar _
                         | TNullable _ | TOcaml_app ("option", [ _ ])) ->
                      params
                  | Some value_ty ->
                      replace_param name
                        (Types.truthy_constraint (TNullable value_ty))
                        params
                  | None -> params)
              | None -> params)
          | _ -> params
        in
        let inferred =
          List.fold_left
            (fun result condition ->
              Result.bind result (fun params -> infer_truthy params condition))
            (Ok params) conditions
        in
        Result.map
          (fun params ->
            let guards = match List.rev conditions with
              | [] -> [] | _last :: guards -> List.rev guards in
            List.fold_left optionalize_guard params guards)
          inferred
    | FList (FSymbol "__lg_logical-or" :: conditions) ->
        (match List.rev conditions with
        | [] -> Ok params
        | last :: reversed_prefix ->
            let expected_result =
              List.rev reversed_prefix
              |> List.find_map (fun form ->
                     let ty = inferred_form_or_call_type ~lookup_function_ty params form in
                     if Type_solver.is_open ty || Types.is_dynamic ty
                        || Types.equal ty TNil || Types.equal ty TBool
                     then None
                     else
                       match ty with
                       | TNullable _ | TOcaml_app ("option", [ _ ]) ->
                           let fallback_ty =
                             inferred_form_or_call_type ~lookup_function_ty params last
                           in
                           if Types.is_dynamic fallback_ty then None
                           else if Type_solver.is_open fallback_ty then Some ty
                           else Some fallback_ty
                       | _ -> Some ty)
            in
            let infer_last =
              match expected_result with
              | Some ty -> infer_expected ty params last
              | None -> infer_form params last
            in
            Result.bind infer_last (fun params ->
                let result_ty =
                  match inferred_form_type params last with
                  | TUnknown | TMeta _ | TVar _ ->
                      inferred_form_or_call_type ~lookup_function_ty params last
                  | ty -> ty
                in
                let optional_operand_ty =
                  match result_ty with
                  | TNullable _ | TOcaml_app ("option", [ _ ]) -> result_ty
                  | _ -> TNullable result_ty
                in
                let truthy_operand_ty =
                  match result_ty with
                  | TUnknown | TMeta _ | TVar _ ->
                      Types.truthy_constraint optional_operand_ty
                  | _ -> optional_operand_ty
                in
                List.fold_left
                  (fun result condition ->
                    Result.bind result (fun params ->
                        match condition with
                        | FSymbol name
                          when not (Types.equal result_ty TBool) ->
                            (match string_assoc_opt name params with
                            | Some (TUnknown | TMeta _ | TVar _) ->
                                constrain_symbol truthy_operand_ty params name
                            | _ -> infer_truthy params condition)
                        | FList [ FKeyword keyword; FSymbol name ] ->
                            add_record_field_constraint name keyword
                              truthy_operand_ty params
                        | FList
                            [
                              FSymbol "__lg_get";
                              FSymbol name;
                              FKeyword keyword;
                            ] ->
                            add_record_field_constraint name keyword
                              truthy_operand_ty params
                        | FList (FSymbol name :: _)
                          when string_mem_assoc name params
                               && not (Types.equal result_ty TBool)
                               && not (Types.equal result_ty TUnknown) ->
                            (match inferred_form_or_call_type ~lookup_function_ty params condition with
                            | TUnknown | TMeta _ | TVar _ ->
                                infer_expected (TNullable result_ty) params condition
                            | _ -> infer_truthy params condition)
                        | condition -> infer_truthy params condition))
                  (Ok params) (List.rev reversed_prefix)))
    | FSymbol name -> constrain_truthy_symbol params name
    | FList [ FSymbol predicate; value ]
      when has_source_name predicate "__lg_empty-predicate" ->
        (match value with
        | FSymbol name -> constrain_seqable TUnknown params name
        | form ->
            infer_expected (Types.seqable_constraint TUnknown) params form)
    | FList (FSymbol name :: args) when string_mem_assoc name params ->
        let parameter_types =
          List.map
            (if can_accumulate_overloaded_function_parameter name then
               inferred_hof_argument_type params
             else inferred_form_or_call_type ~lookup_function_ty params)
            args
          |> specialize_accumulating_hof_parameter_types name
        in
        let return_ty =
          match string_assoc_opt name params with
          | Some (TFn (_, (TUnknown | TMeta _ | TVar _))) -> TBool
          | Some (TFn (_, return_ty)) -> return_ty
          | _ -> TBool
        in
        constrain_symbol (TFn (parameter_types, return_ty)) params name
    | FList [ FKeyword keyword; FSymbol name ] ->
        let field_ty =
          record_field_type params name keyword
          |> Option.value
               ~default:
                 (Types.truthy_constraint
                    (fresh_type_variable
                       ("field_" ^ Names.sanitize_name keyword)))
        in
        add_record_field_constraint name keyword
          field_ty params
    | FList [ FKeyword keyword; FSymbol name; default ] ->
        let field_ty = inferred_form_type params default in
        Result.bind
          (add_record_field_constraint name keyword (TNullable field_ty) params)
          (fun params -> infer_expected field_ty params default)
    | FList
        [ FKeyword nested_keyword; FList [ FKeyword keyword; FSymbol name ] ] ->
        add_record_field_constraint name keyword
          (TRecord
             [
               make_field nested_keyword
                 (Types.dynamic_constraint TUnknown);
             ])
          params
    | form -> infer_form params form
  and infer_collection params = function
    | FSymbol name -> constrain_seqable TUnknown params name
    | form -> infer_form params form
  and infer_generator_bindings params bindings body_forms =
    let bind_generator_let params bindings rest infer_bindings =
      let bind_one params pattern value =
        Result.bind (infer_form params value) (fun params ->
            let names = Destructure.pattern_names pattern in
            let value_ty =
              match inferred_form_type params value with
              | TUnknown | TMeta _ | TVar _ ->
                  inferred_call_return_type ~lookup_function_ty params value
              | ty -> ty
            in
            let binding_tys =
              match pattern with
              | FSymbol name -> [ (name, value_ty) ]
              | _ ->
                  let lookup name =
                    string_assoc_opt name params
                    |> Option.value ~default:TUnknown
                  in
                  let pattern_ty =
                    Destructure.infer_pattern_type pattern lookup
                    |> Result.value ~default:value_ty
                  in
                  names
                  |> List.map (fun name ->
                         ( name,
                           match string_assoc_opt name params with
                           | Some (TUnknown | TMeta _ | TVar _) | None ->
                               fresh_type_variable "for_let"
                           | Some ty -> ty ))
                  |> fun bindings ->
                  match pattern_ty with
                  | TUnknown | TMeta _ | TVar _ -> bindings
                  | _ -> bindings
            in
            let params =
              binding_tys
              @ List.filter
                  (fun (name, _) -> not (string_mem name names))
                  params
            in
            Ok params)
      in
      let rec bind_all local_names params = function
        | [] ->
            Result.map
              (fun inferred ->
                List.map
                  (fun (name, ty) ->
                    if string_mem name local_names then (name, ty)
                    else
                      ( name,
                        string_assoc_opt name inferred
                        |> Option.value ~default:ty ))
                  params
                |> List.filter
                     (fun (name, _) -> not (string_mem name local_names)))
              (infer_bindings params rest)
        | pattern :: value :: more ->
            let names = Destructure.pattern_names pattern in
            Result.bind (bind_one params pattern value) (fun params ->
                bind_all (List.rev_append names local_names) params more)
        | [ _ ] -> infer_bindings params rest
      in
      bind_all [] params bindings
    in
    let rec infer_bindings params = function
      | [] -> infer_all params body_forms
      | FKeyword ":let" :: FVector bindings :: rest ->
          bind_generator_let params bindings rest infer_bindings
      | FKeyword (":when" | ":while") :: condition :: rest ->
          Result.bind (infer_truthy params condition) (fun params ->
              infer_bindings params rest)
      | ((FSymbol _ | FVector _ | FMap _) as pattern) :: collection :: rest ->
          let local_names = Destructure.pattern_names pattern in
          let local_types =
            List.map
              (fun name ->
                ( name,
                  match pattern with
                  | FSymbol _ -> TUnknown
                  | FVector _ | FMap _ -> Type_solver.fresh ()
                  | _ -> TUnknown ))
              local_names
          in
          let local_params =
            local_types
            @ List.filter
                (fun (name, _) -> not (string_mem name local_names))
                params
          in
          Result.bind (infer_bindings local_params rest) (fun inferred ->
              let lookup_local_ty name =
                string_assoc_opt name inferred
                |> Option.value ~default:TUnknown
              in
              let element_ty =
                Destructure.infer_generator_pattern_type pattern lookup_local_ty
                |> Result.value ~default:TUnknown
              in
              let outer_params =
                List.map
                  (fun (name, ty) ->
                    if string_mem name local_names then (name, ty)
                    else
                      ( name,
                        string_assoc_opt name inferred
                        |> Option.value ~default:ty ))
                  params
              in
              infer_sequence_form element_ty outer_params collection)
      | _ -> infer_all params body_forms
    in
    match bindings with
    | FVector forms -> infer_bindings params forms
    | _ -> infer_all params body_forms
  and infer_known_call ?expected_return_ty name params args =
    let member_name =
      match String.rindex_opt name '/' with
      | None -> name
      | Some index ->
          String.sub name (index + 1) (String.length name - index - 1)
    in
    if
      String.length member_name > 2
      && member_name.[0] = '-'
      && member_name.[1] = '>'
    then
      infer_expected_all (Types.dynamic_constraint TUnknown) params args
    else
      match (lookup_protocol_constraint name, args) with
      | Some constraint_ty, FSymbol receiver :: rest ->
          let constraint_ty =
            refine_protocol_call_constraint params constraint_ty rest
          in
          let constraint_ty =
            match
              ( expected_return_ty,
                Types.protocol_constraint_info constraint_ty )
            with
            | Some expected, Some (protocol_id, witness_ty, value_ty) -> (
                match Types.seqable_constraint_info expected with
                | Some _ -> (
                    match Types.protocol_witness_method_types witness_ty with
                    | Some methods ->
                        let refine_method = function
                          | TFn (parameters, return_ty)
                            when List.length parameters = List.length args
                                 && (match return_ty with
                                    | TUnknown | TMeta _ | TVar _ -> true
                                    | _ -> false) ->
                              TFn (parameters, expected)
                          | method_ty -> method_ty
                        in
                        Types.protocol_constraint protocol_id
                          (List.map refine_method methods)
                          value_ty
                    | None -> constraint_ty)
                | None -> constraint_ty)
            | None, _ | _, None -> constraint_ty
          in
          Result.bind
            (constrain_protocol_symbol constraint_ty params receiver)
            (fun params ->
              match lookup_function_ty name with
              | Ok (TFn (_receiver_ty :: parameter_tys, _))
                when List.length parameter_tys = List.length rest ->
                  List.fold_left2
                    (fun result expected_ty argument ->
                      Result.bind result (fun params ->
                          infer_expected expected_ty params argument))
                    (Ok params) parameter_tys rest
              | Ok _ | Error _ -> infer_all params rest)
      | Some _, _ | None, _ -> (
          let function_ty = lookup_inference_function_type params name args in
          match function_ty with
      | Ok ty when Option.is_some (Types.constant_function_result ty) ->
          infer_all params args
      | Ok (TFn (param_tys, _ret)) when List.length param_tys = List.length args
        ->
        let param_tys =
          let from_signature =
            specialize_accumulating_hof_parameter_types name param_tys
          in
          if core_keep_function_name name then
            match (from_signature, args) with
            | _callback_ty :: collection_param_ty :: rest, [ _callback; collection ] ->
                let collection_ty =
                  inferred_form_or_call_type ~lookup_function_ty params
                    collection
                in
                let element_ty =
                  match static_seqable_element_type collection_ty with
                  | Some element_ty -> element_ty
                  | None -> inferred_literal_collection_item params collection
                in
                (match element_ty with
                | TUnknown | TMeta _ | TVar _ -> from_signature
                | element_ty ->
                    TFn
                      ( [ element_ty ],
                        TNullable (Type_solver.fresh ()) )
                    :: collection_param_ty :: rest)
            | _ -> from_signature
          else from_signature
        in
        let callback_substitutions =
          List.fold_left2
            (fun substitutions expected argument ->
              match expected with
              | TFn (expected_params, _) ->
                  let actual_params = inferred_function_parameter_types params argument in
                  if List.length expected_params <> List.length actual_params then substitutions
                  else List.fold_left2
                    (fun substitutions expected actual ->
                      Type_solver.unify substitutions expected actual
                      |> Result.value ~default:substitutions)
                    substitutions expected_params actual_params
              | _ -> substitutions)
            Type_solver.empty param_tys args
        in
        let param_tys =
          List.map
            (fun ty ->
              Type_solver.apply callback_substitutions ty
              |> resolve_named_record)
            param_tys
        in
        let substitutions =
          List.fold_left2
            (fun substitutions expected arg ->
              let actual =
                match inferred_form_or_call_type ~lookup_function_ty params arg with
                | TUnknown -> (
                    match arg with
                    | FSymbol symbol -> (
                        match string_assoc_opt symbol params with
                        | Some ty -> ty
                        | None ->
                            lookup_function_ty symbol
                            |> Result.value ~default:TUnknown)
                    | _ ->
                        inferred_call_return_type ~lookup_function_ty params arg)
                | ty -> ty
              in
              let unresolved =
                Types.equal actual TUnknown
                || match actual with TMeta _ | TVar _ -> true | _ -> false
              in
              if Types.is_dynamic actual then
                if contextual_lookup_argument expected arg then substitutions
                else
                  Type_solver.variables expected
                  |> List.fold_left
                       (fun substitutions variable ->
                         Type_solver.force substitutions variable
                           (Types.dynamic_constraint TUnknown))
                       substitutions
              else if unresolved then substitutions
              else
                Types.infer_type_substitutions substitutions
                  ~template:expected ~actual)
            Type_solver.empty param_tys args
        in
        let param_tys =
          List.map
            (fun ty ->
              Types.substitute_type_variables substitutions ty
              |> resolve_named_record)
            param_tys
        in
        let return_ty =
          Types.substitute_type_variables substitutions _ret
        in
        let params =
          match inference_function_type params name with
          | Some existing when Type_solver.variables existing = [] ->
              replace_param name (TFn (param_tys, return_ty)) params
          | Some _ | None -> params
        in
        List.fold_left2
          (fun acc expected_ty arg ->
            match acc with
            | Error _ as err -> err
            | Ok params ->
                infer_expected expected_ty params
                  arg)
          (Ok params) param_tys args
    | Ok (TOverloaded_fn arities) -> (
        match select_fn_arity arities (List.length args) with
        | None -> infer_all params args
        | Some arity ->
            let fixed_count = List.length arity.fixed_params in
            let expected_tys =
              arity.fixed_params
              @
              match arity.rest_param with
              | None -> []
              | Some rest_ty ->
                    List.init
                      (List.length args - fixed_count)
                      (fun _ -> rest_ty)
            in
            let substitutions =
              let inferred_argument_type = function
                | FList (FSymbol name :: arguments) -> (
                    match
                      Result.map (freshen_call_type name)
                        (lookup_function_ty name)
                    with
                    | Ok (TFn (parameter_tys, return_ty))
                      when List.length parameter_tys
                           = List.length arguments ->
                        Types.instantiate_type ~templates:parameter_tys
                          ~actuals:
                            (List.map (inferred_form_type params) arguments)
                          return_ty
                    | Ok (TOverloaded_fn arities) -> (
                        match select_fn_arity arities (List.length arguments) with
                        | Some arity ->
                            Types.instantiate_type
                              ~templates:arity.fixed_params
                              ~actuals:
                                (List.map (inferred_form_type params) arguments)
                              arity.return_ty
                        | None -> TUnknown)
                    | _ -> TUnknown)
                | form -> inferred_form_type params form
              in
              List.fold_left2
                (fun substitutions expected arg ->
                  let actual = inferred_argument_type arg in
                  if
                    Types.equal actual TUnknown || Types.is_dynamic actual
                    || match actual with TMeta _ | TVar _ -> true | _ -> false
                  then substitutions
                  else
                    Types.infer_type_substitutions substitutions
                      ~template:expected ~actual)
                Type_solver.empty expected_tys args
            in
            let expected_tys =
              List.map
                (Types.substitute_type_variables substitutions)
                expected_tys
            in
            List.fold_left2
              (fun acc expected_ty arg ->
                match acc with
                | Error _ as err -> err
                | Ok params -> infer_expected expected_ty params arg)
              (Ok params) expected_tys args)
          | _ -> infer_all params args)
  and inferred_unary_function_param params = function
    | FKeyword keyword -> TRecord [ make_field keyword TUnknown ]
    | FSymbol name -> (
        match string_assoc_opt name params with
        | Some (TFn ([ param_ty ], _)) -> param_ty
        | Some _ | None -> (
            match lookup_function_ty name with
            | Ok (TFn ([ param_ty ], _)) -> param_ty
            | _ -> TUnknown))
    | FList
        (FSymbol "fn" :: (FVector _ as params_form) :: body_forms) -> (
        let with_locals bindings =
          bindings
          @ List.filter (fun (name, _) -> not (List.mem_assoc name bindings)) params
        in
        match Destructure.parse_param_specs params_form with
        | Ok [ (spec : Destructure.param_spec) ] -> (
            match spec.explicit_ty with
            | Some ty when not (Types.equal ty TUnknown) ->
                resolve_named_record ty
            | _ when not spec.destructured -> (
                match infer_all (with_locals [ (spec.source_name, TUnknown) ]) body_forms with
                | Ok inferred ->
                    string_assoc_opt spec.source_name inferred
                    |> Option.value ~default:TUnknown
                | Error _ -> TUnknown)
            | _ ->
                let pattern_params =
                  Destructure.pattern_names spec.pattern
                  |> List.map (fun name -> (name, Type_solver.fresh ()))
                in
                (match infer_all (with_locals pattern_params) body_forms with
                | Ok inferred ->
                    Destructure.infer_generator_pattern_type spec.pattern (fun name ->
                        string_assoc_opt name inferred
                        |> Option.value ~default:TUnknown)
                    |> Result.value ~default:TUnknown
                | Error _ -> TUnknown))
        | Ok _ | Error _ -> TUnknown)
    | _ -> TUnknown
  and expected_unary_function_param params return_ty = function
    | FList (FSymbol "fn" :: (FVector _ as params_form) :: body_forms) -> (
        match (Destructure.parse_param_specs params_form, List.rev body_forms) with
        | Ok [ (spec : Destructure.param_spec) ], result :: reversed_prefix ->
            let source_ty =
              Option.value spec.explicit_ty ~default:TUnknown
              |> resolve_named_record
            in
            let destructured =
              if spec.destructured then
                Destructure.pattern_type_hints spec.pattern source_ty
                @ (Destructure.pattern_names spec.pattern
                  |> List.map (fun name -> (name, TUnknown)))
              else []
            in
            let local_bindings = (spec.source_name, source_ty) :: destructured in
            let local_names = List.map fst local_bindings in
            let function_params =
              local_bindings
              @ List.filter
                  (fun (name, _) -> not (string_mem name local_names))
                  params
            in
            let inferred =
              Result.bind
                (infer_all function_params (List.rev reversed_prefix))
                (fun params -> infer_expected return_ty params result)
            in
            (match inferred with
            | Error _ -> None
            | Ok inferred when spec.destructured ->
                Destructure.infer_generator_pattern_type spec.pattern (fun name ->
                    string_assoc_opt name inferred
                    |> Option.value ~default:TUnknown)
                |> Result.to_option
            | Ok inferred ->
                string_assoc_opt spec.source_name inferred)
        | (Ok _ | Error _), _ -> None)
    | _ -> None
  and filter_predicate_parameter_type params predicate element_ty return_ty =
    match expected_unary_function_param params return_ty predicate with
    | Some predicate_ty -> refine_type element_ty predicate_ty
    | None -> element_ty
  and inferred_function_parameter_types params = function
    | FSymbol name -> (
        let function_ty =
          match string_assoc_opt name params with
          | Some ty -> Ok ty
          | None -> lookup_function_ty name
        in
        match function_ty with
        | Ok (TFn (parameter_tys, _)) -> parameter_tys
        | Ok _ | Error _ -> [])
    | FList
        (FSymbol "fn" :: FVector parameter_forms :: body_forms) -> (
        match Destructure.parse_param_specs (FVector parameter_forms) with
        | Error _ -> []
        | Ok specs ->
            let local_bindings =
              specs
              |> List.concat_map (fun (spec : Destructure.param_spec) ->
                     let source_ty =
                       Option.value spec.explicit_ty ~default:TUnknown
                       |> resolve_named_record
                     in
                     let destructured =
                       if spec.destructured then
                         Destructure.pattern_names spec.pattern
                         |> List.map (fun name -> (name, TUnknown))
                       else []
                     in
                     (spec.source_name, source_ty) :: destructured)
            in
            let local_names = List.map fst local_bindings in
            let local_params =
              local_bindings
              @ List.filter
                  (fun (name, _) -> not (string_mem name local_names))
                  params
            in
            let inferred =
              infer_all local_params body_forms
              |> Result.value ~default:local_params
            in
            List.map
              (fun (spec : Destructure.param_spec) ->
                string_assoc_opt spec.source_name inferred
                |> Option.value ~default:TUnknown)
              specs)
    | _ -> []
  and is_variadic_vector_constructor params = function
    | FSymbol name -> (
        let function_ty =
          match string_assoc_opt name params with
          | Some ty -> Ok ty
          | None -> lookup_function_ty name
        in
        match function_ty with
        | Ok
            (TOverloaded_fn
              [
                {
                  fixed_params = [];
                  rest_param = Some element_ty;
                  return_ty = TVector return_element_ty;
                };
              ]) ->
            Types.equal element_ty return_element_ty
        | Ok _ | Error _ -> false)
    | _ -> false
  and callback_compares_destructured_values = function
    | FList (FSymbol "fn" :: (FVector _ as params_form) :: body_forms) -> (
        match Destructure.parse_param_specs params_form with
        | Ok [ (spec : Destructure.param_spec) ] when spec.destructured ->
            let names = Destructure.pattern_names spec.pattern in
            let rec compares = function
              | FList (FSymbol "__lg_equal" :: operands) ->
                  List.length operands >= 2
                  && List.for_all
                       (function
                         | FSymbol name -> string_mem name names
                         | _ -> false)
                       operands
              | FList (FSymbol "fn" :: _) -> false
              | FList forms | FVector forms -> List.exists compares forms
              | FMap pairs ->
                  List.exists
                    (fun (key, value) -> compares key || compares value)
                    pairs
              | _ -> false
            in
            List.exists compares body_forms
        | Ok _ | Error _ -> false)
    | _ -> false
  and callback_checks_runtime_type = function
    | FList (FSymbol "fn" :: (FVector _ as params_form) :: body_forms) -> (
        match Destructure.parse_param_specs params_form with
        | Ok [ (spec : Destructure.param_spec) ] when not spec.destructured ->
            let rec checks = function
              | FList
                  [
                    FSymbol "instance?";
                    FSymbol _type_name;
                    FSymbol value;
                  ] ->
                  String.equal value spec.source_name
              | FList (FSymbol "fn" :: _) -> false
              | FList forms | FVector forms -> List.exists checks forms
              | FMap pairs ->
                  List.exists
                    (fun (key, value) -> checks key || checks value)
                    pairs
              | _ -> false
            in
            List.exists checks body_forms
        | Ok _ | Error _ -> false)
    | _ -> false
  and infer_sequence_form element_ty params = function
    | FSymbol name -> constrain_seqable element_ty params name
    | FList [ FSymbol deref_name; FSymbol reference ]
      when String.equal deref_name "IDeref/-deref" -> (
        match string_assoc_opt reference params with
        | Some (TRef (TList _)) ->
            constrain_symbol (TRef (TList element_ty)) params reference
        | Some (TRef (TSeq _)) ->
            constrain_symbol (TRef (TSeq element_ty)) params reference
        | Some (TRef (TSet _)) ->
            constrain_symbol (TRef (TSet element_ty)) params reference
        | Some (TRef (TVector _ | TUnknown | TMeta _ | TVar _)) ->
            constrain_symbol (TRef (TVector element_ty)) params reference
        | Some _ | None ->
            infer_expected (Types.seqable_constraint element_ty) params
              (FList [ FSymbol "IDeref/-deref"; FSymbol reference ]))
    | FList [ FKeyword keyword; FSymbol name ] ->
        add_record_field_constraint name keyword
          (Types.seqable_constraint element_ty)
          params
    | (FList (FSymbol _ :: _) as form) ->
        infer_expected (Types.seqable_constraint element_ty) params form
    | form ->
        infer_expected (Types.seqable_constraint element_ty) params form
  and inferred_literal_collection_item params = function
    | FVector forms | FList (FSymbol "__lg_list" :: forms) -> (
        let item_types = List.map (inferred_form_type params) forms in
        match item_types with
        | [] -> TUnknown
        | first :: rest
          when not (match first with TUnknown | TMeta _ | TVar _ -> true | _ -> false)
               && List.for_all (Types.equal first) rest ->
            first
        | _ -> TUnknown)
    | _ -> TUnknown
  and inferred_reduce_initial_type params reducer init =
    match (reducer, init) with
    | ( FList
          (FSymbol "fn"
          :: FVector [ FVector pattern_forms; _item_pattern ]
          :: _body_forms),
        FVector initial_forms ) -> (
        match Destructure.parse_sequence_pattern pattern_forms with
        | Ok { item_patterns; rest_name = None; sequence_as_name = _ }
          when item_patterns <> []
               && List.length item_patterns = List.length initial_forms ->
            TTuple (List.map (inferred_form_type params) initial_forms)
        | Ok _ | Error _ ->
            returned_vector_type params init
            |> Option.value ~default:(inferred_form_type params init))
    | _ ->
        returned_vector_type params init
        |> Option.value ~default:(inferred_form_type params init)
  and inferred_reducer_types outer_params accumulator_ty = function
    | FSymbol name -> (
        match lookup_function_ty name with
        | Ok (TFn ([ accumulator_ty; item_ty ], _)) ->
            (accumulator_ty, item_ty)
        | _ -> (accumulator_ty, TUnknown))
    | FList
        (FSymbol "fn"
        :: FVector [ FSymbol accumulator; FSymbol item ]
        :: body_forms) -> (
        let reducer_params =
          [ (accumulator, accumulator_ty); (item, TUnknown) ]
          @ List.filter
              (fun (name, ty) ->
                name <> accumulator && name <> item
                && not (Type_solver.is_open ty)
                && not (Types.is_dynamic ty))
              outer_params
        in
        let rec reducer_returned_vector_type params = function
          | FList
              (FSymbol ("let" | "let*") :: FVector bindings :: body_forms) ->
              let rec infer_bindings params = function
                | FSymbol name :: value :: rest ->
                    let ty = inferred_form_type params value in
                    infer_bindings
                      ((name, ty) :: string_remove_assoc name params)
                      rest
                | _ :: _ :: rest -> infer_bindings params rest
                | _ -> params
              in
              let body_params = infer_bindings params bindings in
              (match List.rev body_forms with
              | result :: _ -> reducer_returned_vector_type body_params result
              | [] -> None)
          | form -> returned_vector_type params form
        in
        match
          infer_all reducer_params body_forms
         with
        | Ok inferred ->
            let inferred_accumulator_ty =
              string_assoc_opt accumulator inferred
              |> Option.value ~default:accumulator_ty
            in
            let inferred_accumulator_ty =
              match List.rev body_forms with
              | result :: _ -> (
                  match reducer_returned_vector_type inferred result with
                  | Some returned_ty ->
                      refine_type inferred_accumulator_ty returned_ty
                  | None -> inferred_accumulator_ty)
              | [] -> inferred_accumulator_ty
            in
            ( inferred_accumulator_ty,
              string_assoc_opt item inferred |> Option.value ~default:TUnknown
            )
        | Error _ -> (accumulator_ty, TUnknown))
    | _ -> (accumulator_ty, TUnknown)
  and inferred_kv_reducer_types params init = function
    | FSymbol name -> (
        match lookup_function_ty name with
        | Ok (TFn ([ _; key_ty; value_ty ], _)) -> (key_ty, value_ty)
        | _ -> (TUnknown, TUnknown))
    | FList
        (FSymbol "fn"
        :: FVector [ accumulator; FSymbol key; FSymbol value ]
        :: body_forms) -> (
        let accumulator_ty = inferred_form_type params init in
        let reducer_params =
          [ (key, TUnknown); (value, TUnknown) ]
          @
          match accumulator with
          | FSymbol name -> [ (name, accumulator_ty) ]
          | _ -> []
        in
        match infer_all reducer_params body_forms with
        | Ok inferred ->
            ( string_assoc_opt key inferred
              |> Option.value ~default:TUnknown,
              string_assoc_opt value inferred
              |> Option.value ~default:TUnknown )
        | Error _ -> (TUnknown, TUnknown))
    | _ -> (TUnknown, TUnknown)
  and infer_let ?expected_body params bindings body_forms =
    (* A repeated name starts a new lexical scope, not another constraint on the old value. *)
    let rec split_rebinding names reversed_prefix = function
      | pattern :: value :: rest as forms ->
          let introduced = Destructure.pattern_names pattern in
          if List.exists (fun name -> List.mem name names) introduced then
            Some (List.rev reversed_prefix, forms)
          else
            split_rebinding (introduced @ names)
              (value :: pattern :: reversed_prefix) rest
      | _ -> None
    in
    let rebinding =
      match bindings with
      | FVector forms -> split_rebinding [] [] forms
      | _ -> None
    in
    match rebinding with
    | Some (prefix, rest) ->
        infer_let ?expected_body params (FVector prefix)
          [ FList (FSymbol "let" :: FVector rest :: body_forms) ]
    | None ->
    let bound_names =
      let rec collect = function
        | pattern :: _value :: rest ->
            Destructure.pattern_names pattern @ collect rest
        | _ -> []
      in
      match bindings with FVector forms -> collect forms | _ -> []
    in
    let shadowed = List.filter (fun (name, _) -> List.mem name bound_names) params in
    if shadowed <> [] then
      let used_names = Hashtbl.create 16 in
      let rec collect_names = function
        | FSymbol name -> Hashtbl.replace used_names name ()
        | FList forms | FVector forms -> List.iter collect_names forms
        | FMap pairs -> List.iter (fun (key, value) -> collect_names key; collect_names value) pairs
        | _ -> ()
      in
      List.iter (fun (name, _) -> Hashtbl.replace used_names name ()) params;
      List.iter collect_names (bindings :: body_forms);
      let next = ref 0 in
      let rec fresh_name () =
        let name = "__lg_inference_outer_" ^ string_of_int !next in
        incr next;
        if Hashtbl.mem used_names name then fresh_name ()
        else (Hashtbl.add used_names name (); name)
      in
      let renames = List.map (fun (name, _) -> name, fresh_name ()) shadowed in
      let aliases = List.map (fun (name, fresh) -> name, FSymbol fresh) renames in
      let renamed_params = List.map (fun (name, ty) ->
        Option.value (List.assoc_opt name renames) ~default:name, ty) params in
      (* Keep initializer references distinct from the locals they introduce. *)
      (match rewrite_simple_aliases aliases (FList (FSymbol "let" :: bindings :: body_forms)) with
       | FList (_ :: bindings :: body_forms) ->
           Result.map (List.map (fun (name, ty) ->
             let original = List.find_map (fun (original, fresh) ->
               if name = fresh then Some original else None) renames in
             Option.value original ~default:name, ty))
             (infer_let ?expected_body renamed_params bindings body_forms)
       | _ -> assert false)
    else
    let infer_body params body_forms =
      match (expected_body, List.rev body_forms) with
      | Some expected, last :: reversed_prefix ->
          Result.bind (infer_all params (List.rev reversed_prefix)) (fun params ->
              infer_expected expected params last)
      | Some _, [] -> Ok params
      | None, _ -> infer_all params body_forms
    in
    match bindings with
    | FVector forms -> (
        let rec macro_slots slots = function
          | FSymbol name :: FList [ FSymbol "__lg_volatile!"; FSymbol "nil" ] :: rest
            ->
              macro_slots (name :: slots) rest
          | _ :: _ :: rest -> macro_slots slots rest
          | _ -> slots
        in
        let slots = macro_slots [] forms in
        let rec local_names names = function
          | pattern :: _value :: rest ->
              local_names
                (List.rev_append (Destructure.pattern_names pattern) names)
                rest
          | _ -> List.rev names
        in
        let provisional_names = local_names [] forms |> List.sort_uniq String.compare in
        let infer_local_function_type scope_params = function
          | FList
              (FSymbol "fn" :: FVector parameters :: body_forms)
          | FList
              (FSymbol "fn" :: FSymbol _ :: FVector parameters :: body_forms)
            -> (
              match Destructure.parse_param_specs (FVector parameters) with
              | Error _ -> TUnknown
              | Ok specs ->
                  let parameter_bindings =
                    specs
                    |> List.concat_map (fun (spec : Destructure.param_spec) ->
                           let parameter_ty =
                             Option.value spec.explicit_ty ~default:TUnknown
                             |> resolve_named_record
                           in
                           let destructured =
                             if spec.destructured then
                               Destructure.pattern_names spec.pattern
                               |> List.map (fun name -> (name, TUnknown))
                             else []
                           in
                           (spec.source_name, parameter_ty) :: destructured)
                  in
                  let local_names = List.map fst parameter_bindings in
                  let function_params =
                    parameter_bindings
                    @ List.filter
                        (fun (name, _) -> not (string_mem name local_names))
                        scope_params
                  in
                  (match infer_all function_params body_forms with
                  | Error _ -> TUnknown
                  | Ok inferred ->
                      let parameter_tys =
                        List.map
                          (fun (spec : Destructure.param_spec) ->
                            match spec.explicit_ty with
                            | Some ty when not (Types.equal ty TUnknown) ->
                                resolve_named_record ty
                            | _ when spec.destructured ->
                                Destructure.infer_pattern_type spec.pattern
                                  (fun name ->
                                    string_assoc_opt name inferred
                                    |> Option.value ~default:TUnknown)
                                |> Result.value ~default:TUnknown
                            | _ ->
                                string_assoc_opt spec.source_name inferred
                                |> Option.value ~default:TUnknown)
                          specs
                      in
                      let return_ty =
                        match List.rev body_forms with
                        | result :: _ -> inferred_form_type inferred result
                        | [] -> TNil
                      in
                      TFn (parameter_tys, return_ty)))
          | _ -> TUnknown
        in
        let inferred_initializer_type scope_params value =
          let inferred_ty =
            match value with
            | FList [ FSymbol "__lg_reduce"; reducer; init; _collection ] ->
                let accumulator_ty =
                  match init with
                  | FMap [] ->
                      Types.dynamic_map (Type_solver.fresh ())
                        (Type_solver.fresh ())
                  | _ ->
                      returned_vector_type scope_params init
                      |> Option.value
                           ~default:(inferred_form_type scope_params init)
                in
                let inferred_accumulator_ty, _ =
                  inferred_reducer_types scope_params accumulator_ty reducer
                in
                refine_type accumulator_ty inferred_accumulator_ty
            | _ -> inferred_form_or_call_type ~lookup_function_ty scope_params value
          in
          match inferred_ty with
          | TUnknown -> (
              match value with
              | FList (FSymbol function_name :: arguments) -> (
                  let actual_tys =
                    List.map (inferred_form_type scope_params) arguments
                  in
                  match
                    Result.map (freshen_call_type function_name)
                      (lookup_function_ty function_name)
                  with
                  | Ok (TFn (parameter_tys, return_ty))
                    when List.length parameter_tys = List.length arguments ->
                      Types.instantiate_type ~templates:parameter_tys
                        ~actuals:actual_tys return_ty
                  | Ok (TOverloaded_fn arities) -> (
                      match select_fn_arity arities (List.length arguments) with
                      | Some arity ->
                          let parameter_tys =
                            arity.fixed_params
                            @
                            match arity.rest_param with
                            | None -> []
                            | Some rest_ty ->
                                List.init
                                  (List.length arguments
                                  - List.length arity.fixed_params)
                                  (fun _ -> rest_ty)
                          in
                          Types.instantiate_type ~templates:parameter_tys
                            ~actuals:actual_tys arity.return_ty
                      | None -> infer_local_function_type scope_params value)
                  | Ok _ | Error _ ->
                      infer_local_function_type scope_params value)
              | _ -> infer_local_function_type scope_params value)
          | ty -> ty
        in
        let rec initializer_type name = function
          | FSymbol candidate :: value :: _ when String.equal name candidate ->
              inferred_initializer_type params value
          | _ :: _ :: rest -> initializer_type name rest
          | _ -> TUnknown
        in
        let provisional_params =
          (* Independent destructured positions must share variables with their source. *)
          List.map
            (fun name ->
              let ty = initializer_type name forms in
              (name, if Types.equal ty TUnknown then fresh_type_variable "let" else ty))
            provisional_names
          @ List.filter
              (fun (name, _) -> not (string_mem name provisional_names))
              params
        in
        let inferred_locals =
          lazy
            (* Later initializers also constrain earlier destructured bindings. *)
            (let rec values = function
               | _pattern :: value :: rest -> value :: values rest
               | _ -> []
             in
             let params =
               infer_all provisional_params (values forms)
               |> Result.value ~default:provisional_params
             in
             infer_body params body_forms
            |> Result.value ~default:provisional_params)
        in
        let lookup_inferred_local name =
          string_assoc_opt name (Lazy.force inferred_locals)
          |> Option.value ~default:TUnknown
        in
        let inferred_binding_pattern_type ?source pattern =
          let source_ty = Option.map (inferred_initializer_type params) source in
          let open_call =
            match source, source_ty with
            | _, Some (TTuple _) -> true
            | Some (FList _), Some ty -> (
                match ty with
                | TUnknown | TMeta _ | TVar _ | TTuple _ -> true
                | _ -> false)
            | _ -> false
          in
          if open_call then
            Destructure.infer_generator_pattern_type ?source_ty pattern lookup_inferred_local
          else
            match Destructure.infer_pattern_type pattern lookup_inferred_local with
            | Ok (TVector element_ty) when Types.is_dynamic element_ty ->
                Destructure.infer_generator_pattern_type pattern lookup_inferred_local
            | result -> result
        in
        let group_by_bucket_element_from_body local_name body_forms =
          let merge_field fields keyword =
            match Types.find_field keyword fields with
            | Some _ -> fields
            | None -> make_field keyword TUnknown :: fields
          in
          let rec fields_read_from_sequence sequence_name fields = function
            | FList [ FSymbol map_name; FKeyword keyword; FSymbol name ]
              when (has_source_name map_name "map"
                   || has_source_name map_name "__lg_map")
                   && String.equal name sequence_name ->
                merge_field fields keyword
            | FList forms | FVector forms ->
                List.fold_left
                  (fields_read_from_sequence sequence_name)
                  fields forms
            | FMap pairs ->
                List.fold_left
                  (fun fields (key, value) ->
                    let fields =
                      fields_read_from_sequence sequence_name fields key
                    in
                    fields_read_from_sequence sequence_name fields value)
                  fields pairs
            | _ -> fields
          in
          let callback_bucket_fields callback =
            match callback with
            | FList (FSymbol "fn" :: FVector [ FVector [ _label; FSymbol values ] ] :: body)
            | FList
                ( FSymbol "fn" :: FSymbol _ :: FVector [ FVector [ _label; FSymbol values ] ]
                :: body ) ->
                List.fold_left
                  (fields_read_from_sequence values)
                  [] body
            | _ -> []
          in
          let rec scan fields = function
            | FList [ FSymbol keep_name; callback; FSymbol source ]
              when has_source_name keep_name "keep"
                   && String.equal source local_name ->
                List.fold_left
                  (fun fields (field : field) ->
                    merge_field fields field.keyword)
                  fields (callback_bucket_fields callback)
            | FList forms | FVector forms -> List.fold_left scan fields forms
            | FMap pairs ->
                List.fold_left
                  (fun fields (key, value) -> scan (scan fields key) value)
                  fields pairs
            | _ -> fields
          in
          match List.fold_left scan [] body_forms with
          | [] -> None
          | fields -> Some (TRecord (List.rev fields))
        in
        let rec infer_slot_writes params = function
          | FList [ FSymbol "IVolatile/-vreset!"; FSymbol slot; value ]
            when string_mem slot slots ->
              infer_expected (Types.dynamic_constraint TUnknown) params value
          | FList forms | FVector forms ->
              List.fold_left
                (fun result form ->
                  Result.bind result (fun params ->
                      infer_slot_writes params form))
                (Ok params) forms
          | FMap pairs ->
              List.fold_left
                (fun result (key, value) ->
                  Result.bind result (fun params ->
                      Result.bind (infer_slot_writes params key) (fun params ->
                          infer_slot_writes params value)))
                (Ok params) pairs
          | _ -> Ok params
        in
        let rec infer_values params = function
          | [] -> Ok params
          | (FVector _ as pattern) :: FSymbol source :: rest -> (
              let pattern_ty =
                inferred_binding_pattern_type pattern
                |> Result.value ~default:TUnknown
              in
              let constrained =
                match pattern_ty with
                | TTuple _ -> constrain_symbol pattern_ty params source
                | TVector element_ty -> constrain_seqable element_ty params source
                | _ -> constrain_seqable TUnknown params source
              in
              match constrained with
              | Error _ as err -> err
              | Ok params -> infer_values params rest)
          | (FMap _ as pattern) :: FSymbol source :: rest -> (
              let map_ty =
                Destructure.infer_pattern_type pattern lookup_inferred_local
                |> Result.value
                     ~default:(Types.dynamic_constraint TUnknown)
              in
              match constrain_symbol map_ty params source
              with
              | Error _ as error -> error
              | Ok params -> infer_values params rest)
          | (FMap _ as pattern)
            :: (FList [ FSymbol "IDeref/-deref"; FSymbol _ ] as source)
            :: rest -> (
              let map_ty =
                Destructure.infer_pattern_type pattern lookup_inferred_local
                |> Result.value
                     ~default:(Types.dynamic_constraint TUnknown)
              in
              match infer_expected (TNullable map_ty) params source with
              | Error _ as error -> error
              | Ok params -> infer_values params rest)
          | FSymbol name :: value_form :: rest -> (
              let infer_value =
                match value_form with
                | FList [ FSymbol group_by_name; _key_fn; _collection ]
                  when has_source_name group_by_name "group-by" -> (
                    match group_by_bucket_element_from_body name body_forms with
                    | Some element_ty ->
                        infer_expected
                          (Types.dynamic_map TUnknown (TVector element_ty))
                          params value_form
                    | None -> infer_form params value_form)
                | _ -> infer_form params value_form
              in
              match infer_value with
              | Error _ as err -> err
              | Ok params -> infer_values params rest)
          | _pattern :: value_form :: rest -> (
              match infer_form params value_form with
              | Error _ as error -> error
              | Ok params -> infer_values params rest)
          | [ _ ] -> Ok params
        in
        match infer_values params forms with
        | Error _ as err -> err
        | Ok params -> (
            match
              List.fold_left
                (fun result form ->
                  Result.bind result (fun params ->
                      infer_slot_writes params form))
                (Ok params) body_forms
            with
            | Error _ as error -> error
            | Ok params -> (
                let rec simple_bindings bindings = function
                  | [] -> Some (List.rev bindings)
                  | FSymbol name :: value :: rest ->
                      simple_bindings ((name, value) :: bindings) rest
                  | _ -> None
                in
                match simple_bindings [] forms with
                | None ->
                    let inferred_locals = Lazy.force inferred_locals in
                    let outer_params =
                      List.filter
                        (fun (name, _) ->
                          not (string_mem name provisional_names))
                        inferred_locals
                    in
                    let rec propagate params = function
                      | [] -> Ok params
                      | pattern :: value :: rest ->
                          let expected =
                            inferred_binding_pattern_type ~source:value pattern
                            |> Result.value ~default:TUnknown
                          in
                          let infer_value =
                            match (pattern, value, expected) with
                            | FVector _, FSymbol source, TVector element_ty ->
                                constrain_seqable element_ty params source
                            | _, _, (TUnknown | TMeta _ | TVar _) ->
                                infer_form params value
                            | _, _, expected ->
                                infer_expected expected params value
                          in
                          Result.bind infer_value (fun params ->
                              propagate params rest)
                      | [ _ ] -> Ok params
                    in
                    Result.bind (infer_values outer_params forms) (fun params ->
                        propagate params forms)
                | Some bindings ->
                    let body_forms =
                      List.map (rewrite_simple_aliases bindings) body_forms
                    in
                    let local_names = List.map fst bindings in
                    let outer_params =
                      List.filter
                        (fun (name, _) -> not (string_mem name local_names))
                        params
                    in
                    let rec initial_locals locals = function
                      | [] -> List.rev locals
                      | (name, value) :: rest ->
                          let generic_call =
                            match value with
                            | FList (FSymbol function_name :: arguments) ->
                                (match
                                   lookup_inference_function_type
                                     (List.rev_append locals outer_params)
                                     function_name arguments
                                 with
                                | Ok ty -> Type_solver.variables ty <> []
                                | Error _ -> false)
                            | _ -> false
                          in
                          let ty =
                            if generic_call then TUnknown
                            else
                              inferred_initializer_type
                                (List.rev_append locals outer_params) value
                          in
                          let ty =
                            match ty with
                            | TArray element_ty when Types.is_dynamic element_ty ->
                                TArray
                                  (fresh_type_variable
                                     ("let_array_" ^ Names.sanitize_name name))
                            | ty when Types.equal ty TUnknown ->
                                fresh_type_variable "let"
                            | ty -> ty
                          in
                          initial_locals ((name, ty) :: locals) rest
                    in
                    let local_params = initial_locals [] bindings in
                    Result.bind
                      (infer_all (local_params @ outer_params)
                         (List.map snd bindings))
                      (fun binding_params ->
                      Result.bind
                      (infer_body binding_params body_forms)
                      (fun inferred ->
                        let rec propagate params = function
                          | [] -> Ok params
                          | ( name,
                              FList
                                [
                                  FSymbol field_access;
                                  FSymbol receiver;
                                ] )
                            :: rest
                            when String.starts_with ~prefix:".-" field_access
                                 && string_mem_assoc receiver params ->
                              let expected =
                                string_assoc_opt name params
                                |> Option.value ~default:TUnknown
                              in
                              let keyword =
                                ":"
                                ^ String.sub field_access 2
                                    (String.length field_access - 2)
                              in
                              (match expected with
                              | TUnknown | TMeta _ | TVar _ ->
                                  propagate params rest
                              | _ ->
                                  Result.bind
                                    (add_record_field_constraint receiver
                                       keyword expected params)
                                    (fun params -> propagate params rest))
                          | (name, value) :: rest ->
                              let expected =
                                string_assoc_opt name params
                                |> Option.value ~default:TUnknown
                              in
                              (match expected with
                              | TUnknown | TMeta _ | TVar _ -> propagate params rest
                              | expected ->
                                  Result.bind
                                    (infer_expected expected params value)
                                    (fun params -> propagate params rest))
                        in
                        Result.map
                          (fun inferred ->
                            List.map
                              (fun (name, ty) ->
                                if string_mem name local_names then
                                  let initial_ty =
                                    string_assoc_opt name local_params
                                    |> Option.value ~default:ty
                                  in
                                  (name, refine_type initial_ty ty)
                                else
                                  ( name,
                                    string_assoc_opt name inferred
                                    |> Option.value ~default:ty ))
                              params)
                          (propagate inferred (List.rev bindings)))))))
    | _ -> infer_all params body_forms
  and infer_assoc ?(constrain_assigned = true) ?expected_fields params target
      pairs =
    let target_name = assoc_root_symbol target in
    let rec infer_pairs params = function
      | [] -> Ok params
      | FKeyword keyword :: value_form :: rest -> (
          let expected_field =
            Option.bind expected_fields (fun fields ->
                Types.find_field keyword fields)
          in
          let infer_value =
            match expected_field with
            | Some field -> infer_expected field.ty params value_form
            | None -> (
            match resolve_named_record (inferred_form_type params target) with
            | TNamed_record record -> (
                match Types.find_field keyword record.fields with
                | Some field -> infer_expected field.ty params value_form
                | None -> infer_form params value_form)
            | _ -> infer_form params value_form)
          in
          match infer_value with
          | Error _ as err -> err
          | Ok params -> (
              match target_name with
              | Some name -> (
                  let field_ty =
                    match expected_field with
                    | Some field -> field.ty
                    | None -> (
                        match value_form with
                        | FSymbol value_name -> (
                            match string_assoc_opt value_name params with
                            | Some TUnknown ->
                                fresh_type_variable
                                  ("assoc_" ^ Names.sanitize_name value_name)
                            | Some ((TMeta _ | TVar _) as ty) -> ty
                            | Some ty -> ty
                            | None -> (
                                match lookup_function_ty value_name with
                                | Ok ty -> ty
                                | Error _ ->
                                    inferred_form_or_call_type
                                      ~lookup_function_ty params value_form))
                        | _ ->
                            inferred_form_or_call_type ~lookup_function_ty
                              params value_form)
                  in
                  let params =
                    match value_form with
                    | FSymbol value_name when string_mem_assoc value_name params
                      ->
                        constrain_symbol field_ty params value_name
                    | _ -> Ok params
                  in
                  match params with
                  | Error _ as error -> error
                  | Ok params when not constrain_assigned ->
                      infer_pairs params rest
                  | Ok params -> (
                      match
                        add_record_field_constraint name keyword field_ty params
                      with
                  | Error _ as err -> err
                      | Ok params -> infer_pairs params rest))
              | None -> infer_pairs params rest))
      | key_form :: value_form :: rest -> (
          let expected_pair =
            match inferred_form_type params target with
            | TVector element_ty -> Some (TInt, element_ty)
            | target_ty -> Types.dynamic_map_types target_ty
          in
          match expected_pair with
          | Some (key_ty, value_ty) ->
              Result.bind (infer_expected key_ty params key_form) (fun params ->
                  Result.bind
                    (infer_expected value_ty params value_form)
                    (fun params -> infer_pairs params rest))
          | None ->
              Result.bind
                (infer_all params [ key_form; value_form ])
                (fun params -> infer_pairs params rest))
      | forms -> infer_all params forms
    in
    let infer_target =
      match (target, pairs) with
      | FSymbol _, (FKeyword _ :: _ | []) -> infer_form params target
      | FSymbol name, key_form :: value_form :: _ -> (
          let target_ty =
            string_assoc_opt name params |> Option.value ~default:TUnknown
          in
          let inferred_or_fresh form =
            match inferred_form_or_call_type ~lookup_function_ty params form with
            | TUnknown -> Type_solver.fresh ()
            | ty -> ty
          in
          match
            ( inferred_form_type params key_form,
              Types.seqable_constraint_element target_ty,
              Types.dynamic_map_types target_ty )
          with
          | TInt, Some element_ty, None ->
              let value_ty =
                inferred_form_or_call_type ~lookup_function_ty params value_form
              in
              let element_ty =
                if Types.is_dynamic element_ty then
                  match value_ty with
                  | TUnknown | TMeta _ | TVar _ ->
                      fresh_type_variable "assoc_vector"
                  | value_ty -> value_ty
                else refine_type element_ty value_ty
              in
              constrain_symbol
                (TVector element_ty) params name
          | _, _, Some _ ->
              constrain_symbol
                (Types.dynamic_map
                   (inferred_or_fresh key_form)
                   (inferred_or_fresh value_form))
                params name
          | _, _, None
            when Option.is_some (Types.contains_constraint_info target_ty) ->
              Ok
                (replace_param name
                   (Types.dynamic_map
                      (inferred_or_fresh key_form)
                      (inferred_or_fresh value_form))
                   params)
          | (TUnknown | TMeta _ | TVar _), _, None
            when (match
                    inferred_form_or_call_type ~lookup_function_ty params
                      value_form
                  with
                  | TUnknown | TMeta _ | TVar _ -> false
                  | ty -> not (Types.is_dynamic ty)) ->
              constrain_symbol
                (Types.dynamic_map
                   (fresh_type_variable
                      ("assoc_key_" ^ Names.sanitize_name name))
                   (inferred_form_or_call_type ~lookup_function_ty params
                      value_form))
                params name
          | _, _, None ->
              constrain_symbol (Types.dynamic_constraint TUnknown) params name)
      | FSymbol name, _ ->
          constrain_symbol (Types.dynamic_constraint TUnknown) params name
      | target, FKeyword _ :: _
        when Option.is_some
               (Types.record_fields
                  (resolve_named_record
                     (inferred_form_or_call_type ~lookup_function_ty params target))) ->
          infer_form params target
      | target, FKeyword _ :: _
        when (match inferred_form_or_call_type ~lookup_function_ty params target with
              | TUnknown | TMeta _ | TVar _ -> true
              | _ -> false) ->
          infer_form params target
      | target, key_form :: value_form :: _ ->
          let key_ty =
            inferred_form_or_call_type ~lookup_function_ty params key_form
          in
          let value_ty =
            inferred_form_or_call_type ~lookup_function_ty params value_form
          in
          (match (key_ty, value_ty) with
          | (TUnknown | TMeta _ | TVar _), _
          | _, (TUnknown | TMeta _ | TVar _)
          | TInt, _ -> infer_form params target
          | key_ty, value_ty ->
              infer_expected (Types.dynamic_map key_ty value_ty) params target)
      | _ -> infer_form params target
    in
    match infer_target with
    | Error _ as err -> err
    | Ok params -> infer_pairs params pairs
  and infer_assoc_in params target keys value =
    Result.bind (infer_all params (keys @ [ value ])) (fun params ->
        let params =
          keys
          |> List.fold_left
               (fun result key ->
                 Result.bind result (fun params ->
                     match key with
                     | FKeyword _ -> Ok params
                     | key ->
                         infer_expected
                           (Type_solver.fresh ())
                           params key))
               (Ok params)
        in
        Result.bind params (fun params ->
        let value_ty =
          match inferred_form_type params value with
          | TUnknown | TMeta _ | TVar _ -> Type_solver.fresh ()
          | ty -> ty
        in
        Result.bind (infer_expected value_ty params value) (fun params ->
        let target_ty =
          List.fold_right
            (fun key nested_ty ->
              match key with
              | FKeyword keyword ->
                  TRecord [ make_field keyword nested_ty ]
              | key ->
                  let key_ty =
                    match inferred_form_type params key with
                    | TUnknown | TMeta _ | TVar _ -> Type_solver.fresh ()
                    | ty -> ty
                  in
                  Types.dynamic_map key_ty nested_ty)
            keys value_ty
        in
        infer_expected target_ty params target)))
  and infer_match params target clauses =
    let rec pairs acc = function
      | pattern :: result :: rest -> pairs ((pattern, result) :: acc) rest
      | [] -> Some (List.rev acc)
      | _ -> None in
    let is_tag = function FList (FSymbol "tag" :: _) -> true | _ -> false in
    match pairs [] clauses with
    | Some clauses when List.exists (fun (pattern, _) -> is_tag pattern) clauses
      && List.for_all (function (FSymbol _, _) -> true | (pattern, _) -> is_tag pattern) clauses ->
        let initial = match resolve_named_record (inferred_form_type params target) with
          | TPoly_variant row -> Some row | _ -> None in
        let bound = match initial with
          | Some row -> row.bound
          | None -> if List.exists (function FSymbol _, _ -> true | _ -> false) clauses then Lower_row else Upper_row in
        let rec bind pattern ty = match pattern, ty with
          | FSymbol "_", _ -> (ty, [])
          | FSymbol name, _ -> (ty, [name, ty])
          | FList (FSymbol "tuple" :: patterns), _ ->
              let types = match ty with TTuple types when List.length types = List.length patterns -> types
                | _ -> List.map (fun _ -> Type_solver.fresh ()) patterns in
              let refined = List.map2 bind patterns types in
              (TTuple (List.map fst refined), List.concat_map snd refined)
          | _ -> (ty, []) in
        let rec refined_payload pattern ty bindings = match pattern, ty with
          | FSymbol name, _ -> Option.value (List.assoc_opt name bindings) ~default:ty
          | FList (FSymbol "tuple" :: patterns), TTuple types when List.length patterns = List.length types ->
              TTuple (List.map2 (fun pattern ty -> refined_payload pattern ty bindings) patterns types)
          | _ -> ty in
        let rec infer params tags = function
          | [] -> infer_expected (TPoly_variant {tags = List.sort compare tags; bound}) params target
          | (FList (FSymbol "tag" :: FSymbol tag :: payload), result) :: rest ->
              let previous = Option.bind initial (fun row -> List.assoc_opt tag row.tags) in
              let payload = match payload, previous with
                | [], _ -> Ok (None, [])
                | [pattern], _ ->
                    let ty = Option.join previous |> Option.value ~default:(Type_solver.fresh ()) in
                    let ty, bindings = bind pattern ty in
                    Ok (Some (pattern, ty), bindings)
                | _ -> Error.error "polymorphic variant pattern expects at most one payload" in
              Result.bind payload (fun (payload, bindings) ->
                let names = List.map fst bindings in
                let shadowed = List.filter (fun (name, _) -> List.mem name names) params in
                Result.bind (infer_form (bindings @ List.filter (fun (name, _) -> not (List.mem name names)) params) result)
                  (fun inferred ->
                    let payload = Option.map (fun (pattern, ty) -> refined_payload pattern ty inferred) payload in
                    let tags = (tag, payload) :: List.remove_assoc tag tags in
                    let params = shadowed @ List.filter (fun (name, _) -> not (List.mem name names)) inferred in
                    infer params tags rest))
          | (FSymbol name, result) :: rest ->
              let row = TPoly_variant {tags; bound} in
              let shadowed = List.assoc_opt name params in
              let params = if name = "_" then params else (name, row) :: List.remove_assoc name params in
              Result.bind (infer_form params result) (fun params ->
                let params = if name = "_" then params else
                  let params = List.remove_assoc name params in
                  match shadowed with None -> params | Some ty -> (name, ty) :: params in
                infer params tags rest)
          | _ -> Error.error "invalid polymorphic variant pattern" in
        infer params (Option.fold ~none:[] ~some:(fun row -> row.tags) initial) clauses
    | _ -> infer_nominal_match params target clauses
  and infer_nominal_match params target clauses =
    let pattern_type = function
      | FInt _ -> Some TInt
      | FString _ -> Some TString
      | FKeyword _ -> Some TKeyword
      | FBool _ -> Some TBool
      | _ -> None
    in
    let rec refine_pattern pattern ty =
      match pattern with
      | FList (FSymbol "tag" :: FSymbol tag :: payload_patterns) ->
          let row = match ty with
            | TPoly_variant row -> row
            | _ -> { tags = []; bound = Lower_row }
          in
          let previous = List.assoc_opt tag row.tags in
          let payload, bindings = match payload_patterns with
            | [] -> (None, [])
            | [pattern] ->
                let initial = Option.join previous
                  |> Option.value ~default:(fresh_type_variable "pattern_tag") in
                let payload, bindings = refine_pattern pattern initial in
                (Some payload, bindings)
            | _ -> (None, [])
          in
          (TPoly_variant { row with tags = (tag, payload) :: List.remove_assoc tag row.tags }, bindings)
      | FSymbol "_" -> (ty, [])
      | FSymbol name when not (Expression_support.is_constructor_name name) ->
          (ty, [ (name, ty) ])
      | FSymbol name -> (
          match lookup_function_ty name with
          | Ok (TFn ([], return_ty)) -> (return_ty, [])
          | Ok ((TOcaml _ | TOcaml_app _ | TNamed_record _) as return_ty) ->
              (return_ty, [])
          | Ok _ | Error _ -> (ty, [ (name, ty) ]))
      | FList [ FSymbol ("Ok" | "Error" as constructor); payload_pattern ] ->
          let success, error =
            match ty with
            | TOcaml_app ("result", [ success; error ]) -> success, error
            | _ -> fresh_type_variable "pattern_success", fresh_type_variable "pattern_error"
          in
          let payload, bindings =
            refine_pattern payload_pattern (if constructor = "Ok" then success else error)
          in
          let arguments =
            if constructor = "Ok" then [ payload; error ] else [ success; payload ]
          in
          TOcaml_app ("result", arguments), bindings
      | FList [ FSymbol "Some"; payload_pattern ] ->
          let payload_ty =
            match ty with
            | TNullable payload_ty | TOcaml_app ("option", [ payload_ty ]) ->
                payload_ty
            | _ -> fresh_type_variable "pattern_option"
          in
          let payload_ty, bindings =
            refine_pattern payload_pattern payload_ty
          in
          (TNullable payload_ty, bindings)
      | FList (FSymbol "tuple" :: item_patterns) ->
          let item_tys =
            match ty with
            | TTuple item_tys
              when List.length item_tys = List.length item_patterns ->
                item_tys
            | _ ->
                List.map
                  (fun _ -> fresh_type_variable "pattern_tuple")
                  item_patterns
          in
          let refined = List.map2 refine_pattern item_patterns item_tys in
          (TTuple (List.map fst refined), List.concat_map snd refined)
      | FVector item_patterns -> (
          match static_sequential_element_type ty with
          | Some element_ty ->
              let rec refine_items = function
                | [] -> []
                | [FSymbol "&"; rest] ->
                    [TList element_ty, refine_pattern rest (TList element_ty)]
                | pattern :: rest ->
                    (element_ty, refine_pattern pattern element_ty) :: refine_items rest
              in
              let refined = refine_items item_patterns in
              let substitutions = List.fold_left
                (fun substitutions (expected, (item_ty, _)) ->
                  Type_solver.unify substitutions expected item_ty
                  |> Result.value ~default:substitutions)
                Type_solver.empty refined in
              (Type_solver.apply substitutions ty, List.concat_map (fun (_, (_, bindings)) -> bindings) refined)
          | _ -> (ty, []))
      | FList (FSymbol constructor :: payload_patterns) -> (
          match lookup_function_ty constructor with
          | Ok (TFn (payload_tys, return_ty))
            when List.length payload_tys = List.length payload_patterns ->
              let refined =
                List.map2 refine_pattern payload_patterns payload_tys
              in
              let refined_payload_tys = List.map fst refined in
              let substitutions =
                List.fold_left2
                  (fun substitutions template actual ->
                    Type_solver.unify substitutions template actual
                    |> Result.value ~default:substitutions)
                  Type_solver.empty payload_tys refined_payload_tys
              in
              ( Type_solver.apply substitutions return_ty,
                List.concat_map snd refined )
          | Ok _ | Error _ -> (ty, []))
      | _ -> (ty, [])
    in
    let variant_pattern = function
      | (FList [ FSymbol ("Ok" | "Error"); (FList _ | FVector _ | FMap _) ] as pattern) ->
          Some (refine_pattern pattern (inferred_form_type params target))
      | FVector patterns -> (
          match inferred_form_type params target with
          | TTuple items as ty when List.length items = List.length patterns ->
              Some (refine_pattern (FList (FSymbol "tuple" :: patterns)) ty)
          | _ -> None)
      | FSymbol constructor when Expression_support.is_constructor_name constructor -> (
          match lookup_function_ty constructor with
          | Ok (TFn ([], return_ty)) -> Some (return_ty, [])
          | Ok ((TOcaml _ | TOcaml_app _ | TNamed_record _) as return_ty) ->
              Some (return_ty, [])
          | Ok _ | Error _ -> None)
      | FList [ FSymbol "Some"; payload_pattern ] ->
          let payload_ty, bindings =
            refine_pattern payload_pattern
              (fresh_type_variable "pattern_option")
          in
          Some (TNullable payload_ty, bindings)
      | FList (FSymbol "tuple" :: payload_patterns) ->
          let refined =
            List.map
              (fun pattern ->
                refine_pattern pattern
                  (fresh_type_variable "pattern_tuple"))
              payload_patterns
          in
          Some (TTuple (List.map fst refined), List.concat_map snd refined)
      | FList (FSymbol constructor :: payload_patterns) -> (
          match lookup_function_ty constructor with
          | Ok (TFn (payload_tys, return_ty))
            when List.length payload_tys = List.length payload_patterns ->
              let refined =
                List.map2 refine_pattern payload_patterns payload_tys
              in
              let refined_payload_tys = List.map fst refined in
              let bindings = List.concat_map snd refined in
              let substitutions =
                List.fold_left2
                  (fun substitutions template actual ->
                    Type_solver.unify substitutions template actual
                    |> Result.value ~default:substitutions)
                  Type_solver.empty payload_tys refined_payload_tys
              in
              Some (Type_solver.apply substitutions return_ty, bindings)
          | Ok _ | Error _ -> None)
      | _ -> None
    in
    let target_needs_inference params =
      Type_solver.is_open (inferred_form_type params target)
    in
    let zero_arity_constructor = Expression_support.is_constructor_name in
    let rec refine_bound_pattern pattern ty bindings =
      match pattern, ty with
      | FSymbol name, _ -> Option.value (string_assoc_opt name bindings) ~default:ty
      | FList (FSymbol "tuple" :: patterns), TTuple types
        when List.length patterns = List.length types ->
          TTuple (List.map2 (fun pattern ty -> refine_bound_pattern pattern ty bindings) patterns types)
      | _ -> ty
    in
    let expected_binding_type_from_body binding =
      let expected_from_call name args =
        match lookup_inference_function_type params name args with
        | Ok (TFn (parameter_tys, _))
          when List.length parameter_tys = List.length args ->
            List.combine parameter_tys args
            |> List.find_map (function
                 | expected_ty, FSymbol name when String.equal name binding ->
                     Some (resolve_named_record expected_ty)
                 | _ -> None)
        | Ok (TOverloaded_fn arities) -> (
            match select_fn_arity arities (List.length args) with
            | Some arity ->
                let fixed_count = List.length arity.fixed_params in
                let parameter_tys =
                  arity.fixed_params
                  @
                  match arity.rest_param with
                  | None -> []
                  | Some rest_ty ->
                      List.init
                        (List.length args - fixed_count)
                        (fun _ -> rest_ty)
                in
                List.combine parameter_tys args
                |> List.find_map (function
                     | expected_ty, FSymbol name
                       when String.equal name binding ->
                         Some (resolve_named_record expected_ty)
                     | _ -> None)
            | None -> None)
        | Ok _ | Error _ -> None
      in
      let rec find = function
        | FList (FSymbol name :: args) -> (
            match expected_from_call name args with
            | Some _ as expected -> expected
            | None -> List.find_map find args)
        | FList forms | FVector forms -> List.find_map find forms
        | FMap pairs ->
            List.find_map
              (fun (key, value) ->
                match find key with
                | Some _ as expected -> expected
                | None -> find value)
              pairs
        | FInt _ | FFloat _ | FDecimal _ | FChar _ | FString _ | FBool _
        | FRegex _ | FSymbol _ | FKeyword _ | FCoreSymbol _ ->
            None
      in
      find
    in
    let infer_variant_clause params pattern expected_ty bindings result =
      Result.bind (infer_expected expected_ty params target) (fun params ->
          let local_names = List.map fst bindings in
          let shadowed =
            List.filter (fun (name, _) -> string_mem name local_names) params
          in
          let branch_params =
            bindings
            @ List.filter
                (fun (name, _) -> not (string_mem name local_names))
                params
          in
          Result.bind (infer_form branch_params result) (fun inferred ->
              let substitutions =
                List.fold_left
                  (fun substitutions (name, initial_ty) ->
                    match string_assoc_opt name inferred with
                    | None -> substitutions
                    | Some inferred_ty ->
                        Type_solver.unify substitutions initial_ty inferred_ty
                        |> Result.value ~default:substitutions)
                  Type_solver.empty bindings
              in
              let expected_ty = Type_solver.apply substitutions expected_ty in
              let expected_ty = refine_bound_pattern pattern expected_ty
                (List.filter (fun (name, _) -> string_mem name local_names) inferred) in
              let params =
                shadowed
                @ List.filter
                    (fun (name, _) -> not (string_mem name local_names))
                    inferred
              in
              infer_expected expected_ty params target))
    in
    let infer_option_clause params binding result =
      let rec form_contains_symbol name = function
        | FSymbol candidate -> String.equal candidate name
        | FList forms | FVector forms ->
            List.exists (form_contains_symbol name) forms
        | FMap entries ->
            List.exists
              (fun (key, value) ->
                form_contains_symbol name key || form_contains_symbol name value)
              entries
        | FInt _ | FFloat _ | FDecimal _ | FChar _ | FString _ | FBool _
        | FRegex _ | FKeyword _ | FCoreSymbol _ ->
            false
      in
      let rec form_uses_symbol_in_string_str params name = function
        | FList (FSymbol operation :: args)
          when has_source_name operation "str"
               || has_source_name operation "__lg_str" ->
            List.exists (form_contains_symbol name) args
            && List.exists
                 (fun arg -> Types.equal (inferred_form_type params arg) TString)
                 args
        | FList
            (FSymbol "__lg_apply" :: FSymbol operation :: args)
          when has_source_name operation "str"
               || has_source_name operation "__lg_str" ->
            List.exists (form_contains_symbol name) args
            && List.exists
                 (fun arg -> Types.equal (inferred_form_type params arg) TString)
                 args
        | FList forms | FVector forms ->
            List.exists (form_uses_symbol_in_string_str params name) forms
        | FMap entries ->
            List.exists
              (fun (key, value) ->
                form_uses_symbol_in_string_str params name key
                || form_uses_symbol_in_string_str params name value)
              entries
        | FInt _ | FFloat _ | FDecimal _ | FChar _ | FString _ | FBool _
        | FRegex _ | FSymbol _ | FKeyword _ | FCoreSymbol _ ->
            false
      in
      let initial_payload_ty =
        match inferred_form_type params target with
        | TNullable inner | TOcaml_app ("option", [ inner ]) -> inner
        | _ -> fresh_type_variable "option"
      in
      let shadowed = string_assoc_opt binding params in
      let branch_params =
        (binding, initial_payload_ty) :: string_remove_assoc binding params
      in
      match infer_form branch_params result with
      | Error _ as error -> error
      | Ok branch_params -> (
          let payload_ty =
            string_assoc_opt binding branch_params
            |> Option.value ~default:initial_payload_ty
          in
          let payload_ty =
            match Types.printable_constraint_info payload_ty with
            | Some value_ty
              when Type_solver.is_open value_ty
                   && form_uses_symbol_in_string_str branch_params binding
                        result ->
                TString
            | Some _ | None -> payload_ty
          in
          let params = string_remove_assoc binding branch_params in
          let params =
            match shadowed with
            | None -> params
            | Some ty -> (binding, ty) :: params
          in
          match payload_ty with
          | TUnknown -> infer_form params target
          | payload_ty -> infer_expected (TNullable payload_ty) params target)
    in
    let rec infer_clauses params = function
      | [] -> Ok params
      | [ form ] -> infer_form params form
      | FList [ FSymbol ("Ok" | "Error" as constructor); FSymbol binding ] :: result :: rest
        when not (zero_arity_constructor binding) ->
          let success, error =
            match inferred_call_return_type ~lookup_function_ty params target with
            | TOcaml_app ("result", [ success; error ]) -> (success, error)
            | _ -> (fresh_type_variable "success", fresh_type_variable "error")
          in
          let expected_payload =
            expected_binding_type_from_body binding result
          in
          let params =
            match (expected_payload, target) with
            | Some expected, FList (_callee :: arguments)
              when List.exists
                     (function
                       | FSymbol name -> String.equal name binding
                       | _ -> false)
                     arguments ->
                constrain_symbol expected params binding
                |> Result.value ~default:params
            | (Some _, _) | (None, _) -> params
          in
          let payload = if constructor = "Ok" then success else error in
          let payload =
            match expected_payload with
            | Some expected -> refine_type payload expected
            | None -> payload
          in
          let initial_payload = payload in
          let shadowed = string_assoc_opt binding params in
          let branch_params = (binding, payload) :: string_remove_assoc binding params in
          Result.bind (infer_form branch_params result) (fun branch_params ->
              let payload =
                match string_assoc_opt binding branch_params with
                | Some inferred_payload ->
                    refine_type payload inferred_payload
                | None -> payload
              in
              let params = string_remove_assoc binding branch_params in
              let params =
                match shadowed with None -> params | Some ty -> (binding, ty) :: params
              in
              let arguments =
                if constructor = "Ok" then [ payload; error ] else [ success; payload ]
              in
              let local_target = match target with
                | FSymbol name | FList (FSymbol name :: _) -> string_mem_assoc name params
                | _ -> false in
              Result.bind
                (if local_target || not (Types.equal initial_payload payload) then
                   infer_expected (TOcaml_app ("result", arguments)) params target
                 else infer_form params target)
                (fun params -> infer_clauses params rest))
      | FList [ FSymbol "Some"; FSymbol binding ] :: result :: rest
        when not (zero_arity_constructor binding) -> (
          match infer_option_clause params binding result with
          | Error _ as error -> error
          | Ok params -> infer_clauses params rest)
      | pattern :: result :: rest -> (
          let inferred =
            match pattern_type pattern with
            | Some expected_ty ->
                Result.bind
                  (infer_expected expected_ty params target)
                  (fun params -> infer_form params result)
            | None -> (
                let variant =
                  match variant_pattern pattern with
                  | None -> None
                  | Some (expected_ty, bindings) ->
                      if target_needs_inference params then
                        Some (expected_ty, bindings)
                      else
                        let target_ty = inferred_form_type params target in
                        if
                          Types.equal expected_ty target_ty
                          || Types.assignable ~policy:Host_boundary
                               ~expected:target_ty ~actual:expected_ty
                          || Types.assignable ~policy:Host_boundary
                               ~expected:expected_ty ~actual:target_ty
                        then Some (expected_ty, bindings)
                        else None
                in
                match variant with
                | Some (expected_ty, bindings) ->
                    infer_variant_clause params pattern expected_ty bindings result
                | None ->
                    Result.bind (infer_form params target) (fun params ->
                        infer_form params result))
          in
          match inferred with
          | Error _ as err -> err
          | Ok params -> infer_clauses params rest)
    in
    let rec merge_pattern_types current inferred =
      match current, inferred with
      | TTuple current, TTuple inferred when List.length current = List.length inferred ->
          TTuple (List.map2 merge_pattern_types current inferred)
      | TNullable current, TNullable inferred ->
          TNullable (merge_pattern_types current inferred)
      | TOcaml_app (name, current), TOcaml_app (other, inferred)
        when name = other && List.length current = List.length inferred ->
          TOcaml_app (name, List.map2 merge_pattern_types current inferred)
      | _ -> refine_type current inferred
    in
    let rec collect_pattern_type current = function
      | pattern :: _result :: rest ->
          let current =
            match variant_pattern pattern with
            | Some (ty, _) -> merge_pattern_types current ty
            | None -> current
          in
          collect_pattern_type current rest
      | _ -> current
    in
    (* Collect nested row alternatives before propagating through a polymorphic call. *)
    let initial_params =
      if target_needs_inference params then
        infer_expected (collect_pattern_type TUnknown clauses) params target
      else Ok params
    in
    Result.bind (Result.bind initial_params (fun params -> infer_clauses params clauses)) (fun params ->
        let rec result_forms results = function
          | _pattern :: result :: rest ->
              result_forms (result :: results) rest
          | _ -> List.rev results
        in
        let results = result_forms [] clauses in
        let result_types =
          results
          |> List.map (inferred_form_type params)
          |> List.filter (fun ty ->
                 not (Types.equal ty TUnknown)
                 &&
                 match ty with TMeta _ | TVar _ -> false | _ -> true)
        in
        let concrete_types =
          result_types
          |> List.fold_left
               (fun unique ty ->
                 if List.exists (Types.equal ty) unique then unique
                 else ty :: unique)
               []
        in
        let requires_dynamic =
          List.exists Types.is_dynamic result_types
          || List.length concrete_types > 1
          || List.exists
               (function
                 | FSymbol name -> (
                     match string_assoc_opt name params with
                     | Some TUnknown -> true
                     | _ -> false)
                 | _ -> false)
               results
        in
        if not requires_dynamic then Ok params
        else
          results
          |> List.fold_left
               (fun result -> function
                 | FSymbol name ->
                     Result.bind result (fun params ->
                         constrain_symbol
                           (Types.dynamic_constraint TUnknown)
                           params name)
                 | _ -> result)
               (Ok params))
  and update_signature updater extra_argument_count =
    match lookup_function_ty updater with
    | Ok (TFn (field_ty :: extra_tys, return_ty))
      when List.length extra_tys = extra_argument_count ->
        Some (field_ty, extra_tys, return_ty)
    | Ok (TOverloaded_fn arities) ->
        Option.bind
          (select_fn_arity arities (extra_argument_count + 1))
          (fun arity ->
            match arity.fixed_params with
            | field_ty :: extra_tys
              when Option.is_none arity.rest_param
                   && List.length extra_tys = extra_argument_count ->
                Some (field_ty, extra_tys, arity.return_ty)
            | _ -> None)
    | Ok _ | Error _ -> None
  and updated_value_type field_ty return_ty =
    match field_ty with
    | TNullable inner | TOcaml_app ("option", [ inner ])
      when not (Types.equal return_ty TUnknown)
           && Types.assignable ~policy:Host_boundary ~expected:inner
                ~actual:return_ty ->
        refine_type inner return_ty
    | _ -> refine_type field_ty return_ty
  and infer_conj_get params target values =
    let element_ty =
      values
      |> List.map (inferred_form_type params)
      |> List.fold_left refine_type TUnknown
      |> stored_value_type
    in
    let collection_ty =
      match inferred_form_type params target with
      | TList _ -> TList element_ty
      | TSeq _ -> TSeq element_ty
      | TSet _ -> TSet element_ty
      | TVector _ -> TVector element_ty
      | _ -> TVector element_ty
    in
    Result.bind (infer_expected collection_ty params target) (fun params ->
        infer_expected_all element_ty params values)
  and infer_form params form =
    let form =
      match form with
      | FList (FSymbol "__lg_swap!" :: reference :: FSymbol updater :: arguments) ->
          let value = FSymbol "__lg_inference_receiver" in
          let invocation = FList (FSymbol updater :: value :: arguments) in
          (match expand_form invocation with
          | Ok (FList (FSymbol primitive :: expanded_arguments))
            when primitive <> updater && expanded_arguments = value :: arguments ->
              FList (FSymbol "__lg_swap!" :: reference :: FSymbol primitive :: arguments)
          | _ -> form)
      | _ -> form
    in
    match form with
    | FList (FCoreSymbol core_symbol :: arguments) ->
        let name =
          match core_symbol with
          | Core_update -> "__lg_update"
          | _ -> Ast.core_symbol_name core_symbol
        in
        infer_form params
          (FList (FSymbol name :: arguments))
    | FList [ FSymbol "->Eduction"; transducer; collection ] ->
        infer_form params
          (FList [ FSymbol "sequence"; transducer; collection ])
    | FList [ FSymbol "__type-hint"; FSymbol annotation; value ] -> (
        match Type_annotation.of_param_annotation annotation with
        | Error _ as error -> error
        | Ok hinted_ty when !branch_depth = 0 ->
            let hinted_ty = resolve_named_record hinted_ty in
            (match value with
            | FSymbol name -> constrain_symbol hinted_ty params name
            | value -> infer_expected hinted_ty params value)
        | Ok _hinted_ty ->
            (match value with
            | FSymbol name when not (string_mem name !branch_hint_symbols) ->
                branch_hint_symbols := name :: !branch_hint_symbols
            | _ -> ());
            infer_form params value)
    | FList [ FSymbol filter_name; predicate; collection ]
      when source_sequence_filter_name filter_name ->
        let collection_ty =
          inferred_form_or_call_type ~lookup_function_ty params collection
        in
        let element_ty =
          match static_seqable_element_type collection_ty with
          | Some element_ty
            when not (Types.is_dynamic element_ty)
                 && not (Type_solver.is_open element_ty) ->
              element_ty
          | Some element_ty when not (Types.is_dynamic element_ty) ->
              element_ty
          | Some _ | None -> fresh_type_variable "filter_item"
        in
        let predicate_result_ty = Types.truthy_constraint TUnknown in
        let element_ty =
          filter_predicate_parameter_type params predicate element_ty
            predicate_result_ty
        in
        Result.bind
          (infer_sequence_form element_ty params collection)
          (fun params ->
            infer_expected
              (TFn ([ element_ty ], predicate_result_ty)) params predicate)
    | FList [ FSymbol keep_name; fn; collection ]
      when core_keep_function_name keep_name ->
        let inferred_element_ty = inferred_unary_function_param params fn in
        let inferred_element_ty =
          match inferred_element_ty with
          | TUnknown | TMeta _ | TVar _ ->
              inferred_literal_collection_item params collection
          | ty -> ty
        in
        let element_ty =
          match inferred_element_ty with
          | TUnknown | TMeta _ | TVar _ -> fresh_type_variable "keep_item"
          | ty -> ty
        in
        let result_ty = fresh_type_variable "keep_result" in
        Result.bind
          (infer_sequence_form element_ty params collection)
          (fun params ->
            match fn with
            | FSymbol name ->
                constrain_symbol (TFn ([ element_ty ], TNullable result_ty))
                  params name
            | form ->
                infer_expected (TFn ([ element_ty ], TNullable result_ty))
                  params form)
    | FList
        (FSymbol "record" :: FSymbol record_type_name :: field_forms) ->
        let record_fields =
          resolve_named_record (TOcaml record_type_name)
          |> Type_solver.generalize |> Type_solver.instantiate
          |> Types.record_fields
        in
        List.fold_left
          (fun result field_form ->
            Result.bind result (fun params ->
                match field_form with
                | FList [ FSymbol field_name; value ] -> (
                    match
                      Option.bind record_fields (fun fields ->
                          Types.find_field (":" ^ field_name) fields)
                    with
                    | Some field -> infer_expected field.ty params value
                    | None -> infer_form params value)
                | _ -> Ok params))
          (Ok params) field_forms
    | FList (FSymbol "record" :: _record_type :: field_forms) ->
        infer_all params
          (List.filter_map
             (function
               | FList [ FSymbol _field_name; value ] -> Some value
               | _ -> None)
             field_forms)
    | FList
        [
          FSymbol ("__lg_if-some" | "__lg_if-let");
          FVector [ pattern; option_form ];
          then_form;
          else_form;
        ]
      when (match pattern with FSymbol _ -> false | _ -> true) -> (
        let pattern_names = Destructure.pattern_names pattern in
        let pattern_params =
          pattern_names
          |> List.map (fun name -> (name, Type_solver.fresh ()))
        in
        let shadowed =
          List.filter (fun (name, _) -> List.mem name pattern_names) params
        in
        let branch_params =
          pattern_params
          @ List.filter
              (fun (name, _) -> not (List.mem name pattern_names))
              params
        in
        let infer_then =
          match inferred_form_type params else_form with
          | ty
            when Types.is_dynamic ty
                 || match ty with
                    | TUnknown | TMeta _ | TVar _ -> true
                    | _ -> false ->
              infer_form branch_params then_form
          | expected_ty -> infer_expected expected_ty branch_params then_form
        in
        match infer_then with
        | Error _ as error -> error
        | Ok branch_params ->
            let lookup name =
              string_assoc_opt name branch_params
              |> Option.value ~default:TUnknown
            in
            let payload_ty =
              Destructure.infer_pattern_type pattern lookup
              |> Result.value ~default:TUnknown
            in
            let params =
              List.filter
                (fun (name, _) -> not (List.mem name pattern_names))
                branch_params
            in
            let params =
              shadowed
              @ List.filter
                  (fun (name, _) ->
                    not (List.exists (fun (shadowed, _) -> shadowed = name) shadowed))
                  params
            in
            infer_expected (TNullable payload_ty) params option_form)
    | FList
        [
          FSymbol ("__lg_if-some" | "__lg_if-let");
          FVector [ FSymbol binding; option_form ];
          then_form;
          else_form;
        ] -> (
        let inferred_option_ty =
          inferred_binding_form_type params option_form
        in
        let initial_payload_ty =
          match inferred_option_ty with
          | TNullable inner | TOcaml_app ("option", [ inner ]) -> inner
          | _ -> fresh_type_variable "option"
        in
        let shadowed = string_assoc_opt binding params in
        let branch_params =
          (binding, initial_payload_ty) :: string_remove_assoc binding params
        in
        let infer_then_branch =
          match (then_form, inferred_form_type branch_params else_form) with
          | ( FList (FSymbol "__lg_conj" :: FSymbol target :: values),
              (TList element_ty | TSeq element_ty) )
            when String.equal target binding ->
              Result.bind
                (constrain_symbol (TSeq element_ty) branch_params binding)
                (fun branch_params ->
                  infer_expected_all element_ty branch_params values)
          | ( FList (FSymbol "__lg_conj" :: FSymbol target :: values),
              ((TVector element_ty | TSet element_ty) as collection_ty) )
            when String.equal target binding ->
              Result.bind
                (constrain_symbol collection_ty branch_params binding)
                (fun branch_params ->
                  infer_expected_all element_ty branch_params values)
          | _ -> (
              match inferred_form_type params else_form with
              | ty
                when Types.is_dynamic ty
                     || match ty with
                        | TUnknown | TMeta _ | TVar _ -> true
                        | _ -> false ->
                  infer_form branch_params then_form
              | expected_ty ->
                  infer_expected expected_ty branch_params then_form)
        in
        match infer_then_branch with
        | Error _ as error -> error
        | Ok branch_params ->
            let payload_ty =
              string_assoc_opt binding branch_params
              |> Option.value ~default:initial_payload_ty
            in
            let params = string_remove_assoc binding branch_params in
            let params =
              match shadowed with
              | None -> params
              | Some ty -> (binding, ty) :: params
            in
            let infer_option =
              match payload_ty with
              | TUnknown -> infer_form params option_form
              | payload_ty ->
                  let expected_ty =
                    match option_form with
                    | FList
                        [
                          FSymbol "__lg_first";
                          _collection;
                        ] ->
                        payload_ty
                    | _ when (match payload_ty with TSeq _ -> true | _ -> false) ->
                        let element_ty =
                          match payload_ty with
                          | TSeq element_ty -> element_ty
                          | _ -> assert false
                        in
                        Types.next_seq element_ty
                    | _ -> TNullable payload_ty
                  in
                  infer_expected expected_ty params option_form
            in
            Result.bind infer_option (fun params -> infer_form params else_form)
        )
    | FList
        [
          FSymbol "__lg_some-thread";
          FVector [ FSymbol binding; option_form ];
          then_form;
        ] -> (
        let inferred_option_ty =
          inferred_binding_form_type params option_form
        in
        let initial_payload_ty =
          match inferred_option_ty with
          | TNullable inner | TOcaml_app ("option", [ inner ]) -> inner
          | _ -> fresh_type_variable "option"
        in
        let shadowed = string_assoc_opt binding params in
        let branch_params =
          (binding, initial_payload_ty) :: string_remove_assoc binding params
        in
        match infer_form branch_params then_form with
        | Error _ as error -> error
        | Ok branch_params ->
            let payload_ty =
              string_assoc_opt binding branch_params
              |> Option.value ~default:initial_payload_ty
            in
            let params = string_remove_assoc binding branch_params in
            let params =
              match shadowed with
              | None -> params
              | Some ty -> (binding, ty) :: params
            in
            let input_is_nullable =
              match inferred_option_ty with
              | TNullable _ | TOcaml_app ("option", [ _ ]) | TNil | TUnknown
              | TMeta _ | TVar _ ->
                  true
              | _ -> false
            in
            let expected_option_ty =
              match (input_is_nullable, payload_ty) with
              | true, TUnknown -> TNullable TUnknown
              | true, payload_ty -> TNullable payload_ty
              | false, payload_ty -> payload_ty
            in
            infer_expected expected_option_ty params option_form)
    | FList
        (FSymbol ("__lg_when-some" | "__lg_when-let")
        :: FVector [ FSymbol binding; option_form ]
        :: body_forms) -> (
        let initial_payload_ty =
          match inferred_binding_form_type params option_form with
          | TNullable inner | TOcaml_app ("option", [ inner ]) -> inner
          | _ -> fresh_type_variable "option"
        in
        let shadowed = string_assoc_opt binding params in
        let branch_params =
          (binding, initial_payload_ty) :: string_remove_assoc binding params
        in
        match infer_all branch_params body_forms with
        | Error _ as error -> error
        | Ok branch_params ->
            let payload_ty =
              string_assoc_opt binding branch_params
              |> Option.value ~default:initial_payload_ty
            in
            let params = string_remove_assoc binding branch_params in
            let params =
              match shadowed with
              | None -> params
              | Some ty -> (binding, ty) :: params
            in
            (match payload_ty with
            | TUnknown -> infer_form params option_form
            | payload_ty ->
                let expected_ty =
                  match option_form with
                  | FList
                      [
                        FSymbol "__lg_first";
                        _collection;
                      ] ->
                      payload_ty
                  | _ -> TNullable payload_ty
                in
                infer_expected expected_ty params option_form))
    | FList [ FSymbol "__lg_with-meta"; FSymbol value; metadata ] ->
        Result.bind (infer_form params metadata) (fun params ->
            match lookup_protocol_constraint "IWithMeta" with
            | Some constraint_ty -> (
                let value_ty =
                  string_assoc_opt value params |> Option.value ~default:TUnknown
                in
                match value_ty with
                | TNamed_record _ -> Ok params
                | ty
                  when Type_solver.is_open ty
                       && Option.is_none (Types.protocol_constraint_info ty)
                  ->
                    constrain_symbol
                      (Types.protocol_constraint_with_value constraint_ty ty)
                      params value
                | _ -> Ok params)
            | None -> Ok params)
    | FList [ FSymbol "__lg_with-meta"; value; metadata ] ->
        Result.bind (infer_form params value) (fun params ->
            infer_form params metadata)
    | FList [ FSymbol predicate; value ]
      when has_source_name predicate "__lg_reduced-predicate"
           || has_source_name predicate "reduced?" ->
        infer_form params value
    | FList [ FSymbol "__lg_not"; value ] -> infer_truthy params value
    | FList (FSymbol "__lg_logical-and" :: forms) -> (
        match List.rev forms with
        | [] -> Ok params
        | last :: reversed_guards ->
            let guards = List.rev reversed_guards in
            Result.bind
              (List.fold_left
                 (fun result guard ->
                   Result.bind result (fun params -> infer_truthy params guard))
                 (Ok params) guards)
              (fun params -> infer_form params last))
    | (FList (FSymbol "__lg_logical-or" :: _) as form) -> infer_truthy params form
    | FList [ FSymbol predicate; value ]
      when has_source_name predicate "__lg_empty-predicate" ->
        (match value with
        | FSymbol name -> constrain_seqable TUnknown params name
        | form ->
            infer_expected (Types.seqable_constraint TUnknown) params form)
    | FList [ FSymbol predicate; value ]
      when has_source_name predicate "__lg_true-predicate"
           || has_source_name predicate "__lg_false-predicate" ->
        let value_ty =
          inferred_form_or_call_type ~lookup_function_ty params value
        in
        if Type_solver.is_open value_ty then infer_expected TBool params value
        else infer_form params value
    | FList [ FSymbol predicate; FSymbol value ]
      when has_source_name predicate "__lg_symbol-predicate" ->
        constrain_symbol_predicate params value
    | FList [ FSymbol predicate; FSymbol value ]
      when has_source_name predicate "__lg_int-predicate" ->
        constrain_symbol TInt params value
    | FList [ FSymbol predicate; FSymbol value ]
      when List.exists
             (has_source_name predicate)
             [
               "__lg_keyword-predicate";
               "__lg_string-predicate";
               "__lg_decimal-predicate";
               "__lg_number-predicate";
               "__lg_array-predicate";
               "__lg_array-value-predicate";
               "__lg_list-predicate";
               "__lg_seq-predicate";
               "__lg_fn-predicate";
               "__lg_ifn-predicate";
             ] ->
        constrain_symbol (Types.dynamic_constraint TUnknown) params value
    | FList [ FSymbol "__lg_hash"; FSymbol value ] ->
        constrain_hashable_symbol params value
    | FList
        [
          FSymbol "__lg_compare";
          FList [ FKeyword left_keyword; FSymbol left ];
          FList [ FKeyword right_keyword; FSymbol right ];
        ]
      when String.equal left_keyword right_keyword ->
        let comparison = Types.comparable_constraint (fresh_type_variable "comparison") in
        Result.bind
          (add_record_field_constraint left left_keyword comparison params)
          (fun params ->
            add_record_field_constraint right right_keyword comparison params)
    | FList
        [ FSymbol "__lg_compare"; FSymbol left; FSymbol right ] -> (
        match (string_assoc_opt left params, string_assoc_opt right params) with
        | Some left_ty, _
          when Option.is_some
                 (Types.nested_comparable_constraint_info left_ty) ->
            constrain_symbol
              (Types.nested_comparable_constraint_info left_ty |> Option.get)
              params right
        | _, Some right_ty
          when Option.is_some
                 (Types.nested_comparable_constraint_info right_ty) ->
            constrain_symbol
              (Types.comparable_constraint
                 (Types.nested_comparable_constraint_info right_ty |> Option.get))
              params left
        | Some left_ty, Some right_ty
          when Type_solver.is_open (Types.constraint_value_type left_ty)
               && Type_solver.is_open (Types.constraint_value_type right_ty) ->
            let comparison = fresh_type_variable "comparison" in
            let unify_value params ty =
              match
                Type_solver.unify Type_solver.empty
                  (Types.constraint_value_type ty)
                  comparison
              with
              | Ok substitutions ->
                  Ok
                    (List.map
                       (fun (name, ty) ->
                         (name, Type_solver.apply substitutions ty))
                       params)
              | Error _ ->
                  Error.error "compare arguments must have the same type"
            in
            let rec add_comparable = function
              | TConstraint (Comparable_constraint _value_ty) as ty ->
                  ty
              | TConstraint (Truthy_constraint value_ty) ->
                  Types.truthy_constraint (add_comparable value_ty)
              | TConstraint (Nil_predicate_constraint value_ty) ->
                  Types.nil_predicate_constraint (add_comparable value_ty)
              | TNullable value_ty ->
                  TNullable (add_comparable value_ty)
              | TOcaml_app ("option", [ value_ty ]) ->
                  TOcaml_app ("option", [ add_comparable value_ty ])
              | value_ty -> Types.comparable_constraint value_ty
            in
            Result.bind (unify_value params left_ty) (fun params ->
                let right_ty =
                  string_assoc_opt right params |> Option.value ~default:right_ty
                in
                Result.map
                  (fun params ->
                    let left_ty =
                      string_assoc_opt left params
                      |> Option.value ~default:left_ty
                    in
                    replace_param left (add_comparable left_ty) params)
                  (unify_value params right_ty))
        | _ -> (
            match constrain_comparable_symbol params left with
            | Error _ as error -> error
            | Ok params -> constrain_comparable_symbol params right))
    | FList [ FSymbol "ordering-compare"; FSymbol left; FSymbol right ] -> (
        match (string_assoc_opt left params, string_assoc_opt right params) with
        | Some (TUnknown | TMeta _ | TVar _),
          Some (TUnknown | TMeta _ | TVar _) ->
            infer_expected_all
              (fresh_type_variable "comparison")
              params [ FSymbol left; FSymbol right ]
        | _ -> Ok params)
    | FList [ FSymbol ("__lg_identical-predicate" | ".equals"); left; right ] ->
        Result.bind (infer_all params [ left; right ]) (fun params ->
            let left_ty = inferred_form_type params left in
            let right_ty = inferred_form_type params right in
            let identity_ty =
              if not (Type_solver.is_open left_ty) then left_ty
              else if not (Type_solver.is_open right_ty) then right_ty
              else fresh_type_variable "identical-value"
            in
            infer_expected_all identity_ty params [ left; right ])
    | FList
        (FSymbol (".valAt" | ".containsKey" | ".entryAt")
        :: FList [ FSymbol field_access; FSymbol receiver ]
        :: key_form :: remaining)
      when String.starts_with ~prefix:".-" field_access ->
        let keyword =
          ":"
          ^ String.sub field_access 2 (String.length field_access - 2)
        in
        let key_ty =
          match inferred_form_type params key_form with
          | TUnknown | TMeta _ | TVar _ -> Types.dynamic_constraint TUnknown
          | ty -> ty
        in
        Result.bind
          (add_record_field_constraint receiver keyword
             (Types.dynamic_map key_ty TUnknown)
             params)
          (fun params -> infer_all params (key_form :: remaining))
    | FList
        (FSymbol (".valAt" | ".containsKey" | ".entryAt")
        :: FSymbol target :: arguments) ->
        Result.bind
          (constrain_symbol (Types.dynamic_constraint TUnknown) params target)
          (fun params -> infer_all params arguments)
    | FList [ FSymbol field_access; target ]
      when String.starts_with ~prefix:".-" field_access ->
        let keyword =
          ":"
          ^ String.sub field_access 2 (String.length field_access - 2)
        in
        (match hinted_symbol_target resolve_named_record target with
        | Some (name, Some hinted_ty) ->
            Result.bind (constrain_symbol hinted_ty params name) (fun params ->
                add_record_field_constraint name keyword TUnknown params)
        | Some (name, None) ->
            add_record_field_constraint name keyword TUnknown params
        | None ->
            infer_expected (TRecord [ make_field keyword TUnknown ]) params
              target)
    | FList [ FSymbol "instance?"; FSymbol type_name; FSymbol value ] -> (
        match resolve_named_record (TOcaml type_name) with
        | TNamed_record _ as record_ty ->
            let candidates = lookup_closed_sum_candidates [ record_ty ] in
            let predicate_ty =
              match candidates with
              | [ sum_ty ] -> sum_ty
              | [] | _ :: _ :: _ -> record_ty
            in
            constrain_symbol predicate_ty params value
        | _ -> Ok params)
    | FList [ FSymbol operation; FSymbol name ]
      when string_mem_assoc name params
           && (has_source_name operation "__lg_keys"
              || has_source_name operation "__lg_vals") ->
        let key_ty = fresh_type_variable "map_key" in
        let value_ty = fresh_type_variable "map_value" in
        constrain_symbol (Types.dynamic_map key_ty value_ty) params name
    | FList (FSymbol name :: arguments) when string_mem_assoc name params -> (
        let return_ty = fresh_type_variable "call_result" in
        let parameter_tys =
          List.mapi
            (fun index argument ->
              let argument_ty =
                if can_accumulate_overloaded_function_parameter name then
                  inferred_hof_argument_type params argument
                else
                  inferred_form_or_call_type ~lookup_function_ty params
                    argument
              in
              let argument_ty =
                if Types.equal argument_ty TUnknown then
                  inferred_call_return_type ~lookup_function_ty params argument
                else argument_ty
              in
              match argument_ty with
              | TUnknown ->
                  fresh_type_variable
                    ("call_" ^ Names.sanitize_name name ^ "_"
                   ^ string_of_int index)
              | ty -> ty)
            arguments
        in
        let parameter_tys =
          match string_assoc_opt name params with
          | Some (TFn (existing_parameter_tys, _))
            when List.length existing_parameter_tys = List.length arguments ->
              List.map2
                (fun existing (argument, inferred) ->
                  if
                    Types.is_dynamic inferred
                    && contextual_lookup_argument existing argument
                  then existing
                  else inferred)
                existing_parameter_tys
                (List.combine arguments parameter_tys)
          | Some _ | None -> parameter_tys
        in
        let parameter_tys =
          specialize_accumulating_hof_parameter_types name parameter_tys
          |> List.map resolve_named_record
        in
        match constrain_symbol (TFn (parameter_tys, return_ty)) params name with
        | Error _ as err -> err
        | Ok params ->
            List.fold_left2
              (fun result expected argument ->
                Result.bind result (fun params ->
                    infer_expected expected params
                      argument))
              (Ok params) parameter_tys arguments)
    | FList
        [ FSymbol "IDeref/-deref"; FList [ FKeyword keyword; FSymbol name ] ] ->
        add_record_field_constraint name keyword (TRef (Type_solver.fresh ())) params
    | FList
        [
          FSymbol "IDeref/-deref";
          FList [ FSymbol field_access; FSymbol name ];
        ]
      when String.starts_with ~prefix:".-" field_access ->
        let keyword =
          ":" ^ String.sub field_access 2 (String.length field_access - 2)
        in
        add_record_field_constraint name keyword (TRef (Type_solver.fresh ())) params
    | FList
        [
          FSymbol ("__lg_weak-deref" | "__lg_weak-clear!");
          FList [ FKeyword keyword; FSymbol name ];
        ] ->
        add_record_field_constraint name keyword
          (Types.weak_type TUnknown) params
    | FList
        [ FSymbol ("__lg_weak-deref" | "__lg_weak-clear!"); FSymbol name ] ->
        constrain_symbol (Types.weak_type TUnknown) params name
    | FList [ FSymbol "weak-ref"; value ] -> infer_form params value
    | FList
        [
          FSymbol "IVolatile/-vreset!";
          FSymbol reference;
          FList
            [
              FSymbol "__lg_assoc!";
              FList [ FSymbol "IDeref/-deref"; FSymbol deref_reference ];
              key;
              value;
            ];
        ]
      when String.equal reference deref_reference ->
        let inferred_or_fresh form =
          match inferred_form_type params form with
          | TUnknown | TMeta _ | TVar _ -> Type_solver.fresh ()
          | ty -> ty
        in
        let key_ty = inferred_or_fresh key in
        let value_ty = inferred_or_fresh value in
        let reference_ty =
          TRef
            (TOcaml_app
               ( "Lg_runtime.Runtime_transient.map",
                 [ key_ty; value_ty ] ))
        in
        Result.bind (constrain_symbol reference_ty params reference)
          (fun params ->
            Result.bind (infer_expected key_ty params key) (fun params ->
                infer_expected value_ty params value))
    | FList
        [
          FSymbol "IVolatile/-vreset!";
          FSymbol reference;
          FList
            [
              FSymbol "__lg_conj!";
              FList [ FSymbol "IDeref/-deref"; FSymbol deref_reference ];
              value;
            ];
        ]
      when String.equal reference deref_reference ->
        let element_ty =
          match inferred_form_type params value with
          | TUnknown | TMeta _ | TVar _ -> Type_solver.fresh ()
          | ty -> ty
        in
        let reference_ty =
          TRef
            (TOcaml_app
               ("Lg_runtime.Runtime_transient.vector", [ element_ty ]))
        in
        Result.bind (constrain_symbol reference_ty params reference)
          (fun params -> infer_expected element_ty params value)
    | FList
        [
          FSymbol ("IVolatile/-vreset!" | "IReset/-reset!");
          FSymbol reference;
          value;
        ]
      when
        (match string_assoc_opt reference params with
        | Some (TRef _ | TUnknown | TMeta _ | TVar _) | None -> false
        | Some _ -> true) ->
        infer_form params value
    | FList
        [
          FSymbol ("IVolatile/-vreset!" | "IReset/-reset!");
          FSymbol reference;
          value;
        ] ->
        let value_ty = inferred_form_type params value in
        let referenced_ty =
          match string_assoc_opt reference params with
          | Some (TRef (TNullable _)) -> TNullable value_ty
          | Some (TRef (TOcaml_app ("option", [ _ ]))) ->
              TOcaml_app ("option", [ value_ty ])
          | Some _ | None -> value_ty
        in
        Result.bind
          (constrain_symbol (TRef referenced_ty) params reference)
          (fun params ->
            match value_ty with
            | TUnknown | TMeta _ | TVar _ -> infer_form params value
            | value_ty -> infer_expected value_ty params value)
    | FList
        [
          FSymbol "__lg_swap!";
          FSymbol reference;
          FSymbol "__lg_assoc!";
          key;
          value;
        ] ->
        let inferred_or_dynamic form =
          match inferred_form_type params form with
          | TUnknown | TMeta _ | TVar _ -> Type_solver.fresh ()
          | ty -> ty
        in
        let key_ty = inferred_or_dynamic key in
        let value_ty = inferred_or_dynamic value in
        let reference_ty =
          TRef
            (TOcaml_app
               ( "Lg_runtime.Runtime_transient.map",
                 [ key_ty; value_ty ] ))
        in
        Result.bind (constrain_symbol reference_ty params reference)
          (fun params ->
            Result.bind (infer_expected key_ty params key) (fun params ->
                infer_expected value_ty params value))
      | FList
          [
            FSymbol "__lg_swap!";
            FSymbol reference;
            FSymbol "__lg_conj!";
          value;
        ] ->
        let element_ty =
          match inferred_form_type params value with
          | TUnknown | TMeta _ | TVar _ -> Type_solver.fresh ()
          | ty -> ty
        in
        let reference_ty =
          TRef
            (TOcaml_app
               ("Lg_runtime.Runtime_transient.vector", [ element_ty ]))
          in
          Result.bind (constrain_symbol reference_ty params reference)
            (fun params -> infer_expected element_ty params value)
      | FList
        (FSymbol "__lg_swap!"
        :: FList [ FKeyword reference_keyword; FSymbol receiver ]
        :: (FSymbol "__lg_update" | FCoreSymbol Core_update)
        :: FKeyword field_keyword :: FSymbol updater :: extra_arguments) -> (
          match update_signature updater (List.length extra_arguments) with
          | None -> infer_all params extra_arguments
          | Some (field_ty, extra_tys, return_ty) ->
              let field_ty = updated_value_type field_ty return_ty in
              let state_ty =
                TRecord [ make_field field_keyword field_ty ]
              in
              Result.bind
                (add_record_field_constraint receiver reference_keyword
                   (TRef state_ty) params)
                (fun params ->
                  List.fold_left2
                    (fun result expected argument ->
                      Result.bind result (fun params ->
                          infer_expected expected params argument))
                    (Ok params) extra_tys extra_arguments))
      | FList
          (FSymbol "__lg_swap!"
          :: ((FSymbol _ | FList [ FKeyword _; FSymbol _ ]) as reference_form)
          :: FSymbol conj_name :: values)
      when (match inferred_binding_form_type params reference_form with
            | TRef _ | TUnknown | TMeta _ | TVar _ -> true
            | _ -> false)
           && has_source_name conj_name "__lg_conj" ->
        let inferred_value_type value =
          match inferred_form_type params value with
          | (TUnknown | TMeta _ | TVar _) as unresolved -> (
              match value with
              | FList (FSymbol name :: arguments) -> (
                  match lookup_function_ty name with
                  | Ok (TFn (parameters, return_ty))
                    when List.length parameters = List.length arguments ->
                      return_ty
                  | Ok (TOverloaded_fn arities) -> (
                      match select_fn_arity arities (List.length arguments) with
                      | Some arity -> arity.return_ty
                      | None -> unresolved)
                  | Ok _ | Error _ ->
                      inferred_call_return_type ~lookup_function_ty params
                        value)
              | _ -> unresolved)
          | ty -> ty
        in
        let element_ty =
          values
          |> List.map inferred_value_type
          |> List.fold_left refine_type TUnknown
        in
        let collection_ty =
          match inferred_binding_form_type params reference_form with
          | TRef (TList _) -> TList element_ty
          | TRef (TSeq _) -> TSeq element_ty
          | TRef (TSet _) -> TSet element_ty
          | TRef (TVector _) | TRef (TUnknown | TMeta _ | TVar _)
          | TUnknown | TMeta _ | TVar _ ->
              TVector element_ty
          | TRef collection_ty -> collection_ty
          | _ -> TVector element_ty
        in
        Result.bind
          (infer_expected (TRef collection_ty) params reference_form)
          (fun params -> infer_expected_all element_ty params values)
      | FList
          (FSymbol "__lg_swap!"
          :: ((FSymbol _ | FList [ FKeyword _; FSymbol _ ]) as reference_form)
          :: (FSymbol updater as update_fn) :: arguments)
      when (match inferred_binding_form_type params reference_form with
            | TRef _ | TUnknown | TMeta _ | TVar _ -> true
            | _ -> false) ->
        (* Infer the same updater application that elaboration writes back to the cell. *)
        let invocation =
          FList (update_fn :: FList [FSymbol "IDeref/-deref"; reference_form] :: arguments)
        in
        Result.bind
          (if string_mem_assoc updater params then Ok invocation else expand_form invocation)
          (fun invocation ->
            Result.bind (infer_form params invocation) (fun params ->
                let result_ty = inferred_binding_form_type params invocation in
                Result.bind (infer_expected (TRef result_ty) params reference_form)
                  (fun params -> infer_expected result_ty params invocation)))
    | FList
        (FSymbol "__lg_swap!" :: reference :: update_fn
       :: arguments) ->
        Result.bind (infer_form params reference) (fun params ->
            let infer_updater =
              match inferred_form_type params reference with
              | (TRef _ | TUnknown | TMeta _ | TVar _) as reference_ty ->
                  let payload_ty =
                    match reference_ty with
                    | TRef payload -> payload
                    | _ -> Type_solver.fresh ()
                  in
                  (* Updater parameters constrain the cell, not just captured values. *)
                  let payload_ty =
                    match inferred_function_parameter_types params update_fn with
                    | current :: _ -> refine_type payload_ty current
                    | [] -> payload_ty
                  in
                  let argument_tys =
                    List.map (inferred_form_type params) arguments
                  in
                  Result.bind
                    (infer_expected (TRef payload_ty) params reference)
                    (fun params ->
                      infer_expected
                        (TFn (payload_ty :: argument_tys, payload_ty))
                        params update_fn)
              | _ -> infer_form params update_fn
            in
            Result.bind infer_updater (fun params ->
                let expected = inferred_form_type params reference in
                let update_ty =
                  match update_fn with
                  | FSymbol name -> (
                      match string_assoc_opt name params with
                      | Some ty -> ty
                      | None ->
                          lookup_function_ty name
                          |> Result.value ~default:TUnknown)
                  | form -> inferred_form_type params form
                in
                let invocation_parameter_types =
                  let argument_count = List.length arguments + 1 in
                  match update_ty with
                  | TFn (parameter_tys, _)
                    when List.length parameter_tys = argument_count ->
                      Some parameter_tys
                  | TOverloaded_fn arities ->
                      select_fn_arity arities argument_count
                      |> Option.map (fun (arity : fn_arity) ->
                             arity.fixed_params
                             @
                             match arity.rest_param with
                             | None -> []
                             | Some rest_ty ->
                                 List.init
                                   (argument_count
                                   - List.length arity.fixed_params)
                                   (fun _ -> rest_ty))
                  | _ -> None
                in
                let expected_arguments =
                  match invocation_parameter_types with
                  | Some (_current :: additional) -> additional
                  | Some [] | None ->
                      let expected_argument =
                        if Types.is_dynamic expected then
                          Types.dynamic_constraint TUnknown
                        else TUnknown
                      in
                      List.init (List.length arguments) (fun _ -> expected_argument)
                in
                List.fold_left2
                  (fun result expected_argument argument ->
                    Result.bind result (fun params ->
                        if Types.equal expected_argument TUnknown then
                          infer_form params argument
                        else infer_expected expected_argument params argument))
                  (Ok params) expected_arguments arguments))
    | FList
        [
          FSymbol "__deftype-field-set!";
          FKeyword keyword;
          FSymbol receiver;
          value;
        ] -> (
        match record_mutable_field_value_type params receiver keyword with
        | Some ty -> infer_expected ty params value
        | None ->
            let field_ty =
              match inferred_form_type params value with
              | TNil -> TOcaml_app ("option", [ TUnknown ])
              | ty -> ty
            in
            Result.bind
              (constrain_symbol
                 (TRecord [ make_field ~mutable_:true keyword field_ty ])
                 params receiver)
              (fun params -> infer_expected field_ty params value))
    | FList
        [
          FSymbol "set!";
          FList [ FSymbol field_access; FSymbol receiver ];
          value;
        ]
      when String.starts_with ~prefix:".-" field_access ->
        let keyword =
          ":"
          ^ String.sub field_access 2 (String.length field_access - 2)
        in
        (match record_mutable_field_value_type params receiver keyword with
        | Some ty -> infer_expected ty params value
        | None ->
            let field_ty =
              match inferred_form_type params value with
              | TNil -> TOcaml_app ("option", [ TUnknown ])
              | ty -> ty
            in
            Result.bind
              (constrain_symbol
                 (TRecord [ make_field ~mutable_:true keyword field_ty ])
                 params receiver)
              (fun params -> infer_expected field_ty params value))
    | FList
        [
          FSymbol ("IVolatile/-vreset!" | "IReset/-reset!");
          FList [ FKeyword keyword; FSymbol name ];
          value;
        ]
      -> (
        match record_ref_field_value_type params name keyword with
        | Some ty -> infer_expected ty params value
        | None -> (
            match value with
            | FList [ FSymbol "Some"; FSymbol value_name ] ->
                let payload_ty =
                  match string_assoc_opt value_name params with
                  | Some (TUnknown | TMeta _ | TVar _) | None ->
                      fresh_type_variable
                        ("option_" ^ Names.sanitize_name value_name)
                  | Some ty -> ty
                in
                Result.bind
                  (add_record_field_constraint name keyword
                     (TRef (TNullable payload_ty)) params)
                  (fun params ->
                    constrain_symbol payload_ty params value_name)
            | _ ->
                let value_ty = inferred_form_type params value in
                Result.bind
                  (add_record_field_constraint name keyword (TRef value_ty)
                     params)
                  (fun params -> infer_form params value)))
    | FList [ FSymbol predicate; value ]
      when has_source_name predicate "__lg_nil-predicate" ->
        let inferred_ty = inferred_form_type params value in
        let expected_ty =
          match value with
          | FList [ FSymbol ("__lg_first" | "__lg_second"); _ ] ->
              let payload_ty =
                match inferred_ty with
                | TNullable inner | TOcaml_app ("option", [ inner ]) -> inner
                | TUnknown | TMeta _ | TVar _ -> Type_solver.fresh ()
                | ty -> ty
              in
              TNullable (Types.nil_predicate_constraint payload_ty)
          | _ -> (
          match inferred_ty with
          | TNullable ((TUnknown | TMeta _ | TVar _) as payload_ty) ->
              TNullable (Types.nil_predicate_constraint payload_ty)
          | TOcaml_app
              ("option", [ (TUnknown | TMeta _ | TVar _) as payload_ty ]) ->
              TOcaml_app
                ("option", [ Types.nil_predicate_constraint payload_ty ])
          | TUnknown -> TNullable (Type_solver.fresh ())
          | (TMeta _ as value_ty) -> TNullable value_ty
          | (TVar _) as value_ty ->
              Types.nil_predicate_constraint value_ty
          | ty -> ty)
        in
        let nil_predicate_optional_seqable =
          Option.bind
            (Types.nil_predicate_constraint_info inferred_ty)
            (fun ty ->
              match Types.seqable_constraint_info ty with
              | Some ((`Optional | `Optional_sequential), _, _) -> Some ty
              | Some (`Required, _, _) | None -> None)
        in
        (match (value, inferred_ty) with
        | FSymbol name, _
          when Option.is_some nil_predicate_optional_seqable ->
            Ok
              (replace_param name
                 (Option.get nil_predicate_optional_seqable)
                 params)
        | FSymbol _, ty
          when Option.bind
                 (Types.nil_predicate_constraint_info ty)
                 Types.nested_comparable_constraint_info
               |> Option.is_some ->
            Ok params
        | FSymbol name, ty
          when (match Types.seqable_constraint_info ty with
               | Some ((`Optional | `Optional_sequential), _, _) -> true
               | Some (`Required, _, _) | None -> false) ->
            Ok (replace_param name ty params)
        | FSymbol name, TConstraint (Seqable_constraint {element; storage; _}) ->
            Ok (replace_param name
              (Types.optional_seqable_constraint element storage) params)
        | ( FSymbol name,
            ((TNullable _ | TOcaml_app ("option", [ _ ])) as ty) ) ->
            Ok (replace_param name ty params)
        | FSymbol _, ty
          when Option.is_some (Types.nil_predicate_constraint_info ty) ->
            Ok params
        | FSymbol name, ty
          when (match ty with
               | TUnknown | TMeta _ | TVar _ -> false
               | _ -> true) ->
            Ok (replace_param name (TNullable ty) params)
        | _ -> infer_expected expected_ty params value)
    | FList [ FSymbol "__lg_count"; collection ] -> (
        match collection with
        | FSymbol name -> constrain_seqable TUnknown params name
        | form ->
            infer_expected (Types.seqable_constraint TUnknown) params form)
    | FList [ FSymbol "__lg_name"; FSymbol name ] -> (
        match lookup_protocol_constraint "INameCoercion" with
        | Some constraint_ty -> constrain_symbol constraint_ty params name
        | None -> infer_expected TString params (FSymbol name))
    | FList [ FSymbol "__lg_name"; value ] ->
        infer_expected
          (match lookup_protocol_constraint "INameCoercion" with
          | Some constraint_ty -> constraint_ty
          | None -> TString)
          params value
    | FList [ FSymbol "__lg_namespace"; FSymbol name ] -> (
        match lookup_protocol_constraint "INamed" with
        | Some constraint_ty -> constrain_symbol constraint_ty params name
        | None -> infer_expected TString params (FSymbol name))
    | FList [ FSymbol "__lg_re-find"; expression; source ] ->
        Result.bind (infer_expected TRegex params expression)
          (fun params -> infer_expected TString params source)
    | FList (FSymbol "__lg_merge" :: maps) ->
        let key_ty, value_ty =
          maps
          |> List.find_map (fun map ->
                 Types.dynamic_map_types (inferred_form_type params map))
          |> Option.value
               ~default:(Type_solver.fresh (), Type_solver.fresh ())
        in
        let expected_map = Types.dynamic_map key_ty value_ty in
        List.fold_left
          (fun result map ->
            Result.bind result (fun params ->
                match inferred_form_type params map with
                | TUnknown | TMeta _ | TVar _ ->
                    infer_expected expected_map params map
                | ty when Option.is_some (Types.dynamic_map_types ty) ->
                    infer_expected expected_map params map
                | _ -> infer_form params map))
          (Ok params) maps
    | FList
        (FSymbol "__lg_update"
        :: target :: key
        :: (FSymbol "__lg_update"
           | FCoreSymbol Core_update)
        :: nested_arguments) ->
        let nested_value = "__lg_nested_update_value" in
        let params =
          match (target, key) with
          | FSymbol target, FKeyword keyword ->
              let field_ty =
                match nested_arguments with
                | nested_key :: FSymbol updater :: extra_arguments -> (
                    match
                      update_signature updater (List.length extra_arguments)
                    with
                    | Some (updater_field_ty, _, return_ty) ->
                        let key_ty =
                          inferred_form_type params nested_key
                          |> materialize_dynamic_unknown
                        in
                        let value_ty =
                          updated_value_type updater_field_ty return_ty
                        in
                        Types.dynamic_map key_ty value_ty
                    | None -> Types.dynamic_constraint TUnknown)
                | _ -> Types.dynamic_constraint TUnknown
              in
              add_record_field_constraint target keyword
                field_ty params
          | _ -> Ok params
        in
        Result.bind params (fun params ->
            infer_form params
              (FList
                 [
                   FCoreSymbol Core_update;
                   target;
                   key;
                   FList
                     [
                       FSymbol "fn";
                       FVector [ FSymbol nested_value ];
                       FList
                         (FSymbol "__lg_update" :: FSymbol nested_value
                        :: nested_arguments);
                     ];
                 ]))
    | FList
        (FSymbol "__lg_update"
        :: FSymbol target
        :: (FInt _ as index)
        :: FSymbol updater
        :: extra_arguments) -> (
        match lookup_function_ty updater with
        | Ok (TFn (element_ty :: extra_tys, return_ty))
          when List.length extra_tys = List.length extra_arguments
               && Types.equal (refine_type element_ty return_ty) element_ty ->
            Result.bind (constrain_symbol (TVector element_ty) params target)
              (fun params ->
                Result.bind (infer_expected TInt params index) (fun params ->
                    List.fold_left2
                      (fun result expected argument ->
                        Result.bind result (fun params ->
                            infer_expected expected params argument))
                      (Ok params) extra_tys extra_arguments))
        | Ok _ | Error _ -> infer_all params extra_arguments)
    | FList
        (FSymbol "__lg_update"
        :: FSymbol target
        :: FKeyword keyword
        :: FSymbol updater
        :: extra_arguments) -> (
        let signature =
          match (updater, extra_arguments) with
          | "__lg_conj", _ :: _ ->
              let element_ty =
                extra_arguments
                |> List.map (inferred_form_type params)
                |> List.fold_left refine_type TUnknown
                |> stored_value_type
              in
              let collection_ty =
                match
                  string_assoc_opt target params
                  |> fun target_ty ->
                  Option.bind target_ty (fun target_ty ->
                      match Types.constraint_value_type target_ty with
                      | TRecord fields | TNamed_record { fields; _ } ->
                          Option.map
                            (fun (field : field) -> field.ty)
                            (Types.find_field keyword fields)
                      | _ -> None)
                with
                | Some (TList _) -> TList element_ty
                | Some (TSeq _) -> TSeq element_ty
                | Some (TSet _) -> TSet element_ty
                | Some (TVector _) | Some _ | None -> TVector element_ty
              in
              Some
                ( collection_ty,
                  List.map (fun _ -> element_ty) extra_arguments,
                  collection_ty )
          | _ -> update_signature updater (List.length extra_arguments)
        in
        match signature with
        | None -> infer_all params extra_arguments
        | Some (field_ty, extra_tys, return_ty) -> (
            let field_ty = updated_value_type field_ty return_ty in
            match
              add_record_field_constraint target keyword field_ty params
            with
            | Error _ as error -> error
            | Ok params ->
                List.fold_left2
                  (fun result expected argument ->
                    Result.bind result (fun params ->
                        infer_expected expected params argument))
                  (Ok params) extra_tys extra_arguments))
    | FList
        (FSymbol "__lg_update"
        :: FSymbol target
        :: key
        :: updater
        :: extra_arguments) ->
        let infer_inline_updater_return = function
          | FList
              (FSymbol "fn" :: FVector parameter_forms :: body_forms) -> (
              let parameter_names =
                List.filter_map
                  (function FSymbol name -> Some name | _ -> None)
                  parameter_forms
              in
              if List.length parameter_names <> List.length parameter_forms then
                TUnknown
              else
                let function_params =
                  List.map
                    (fun name -> (name, Type_solver.fresh ()))
                    parameter_names
                  @ params
                in
                match infer_all function_params body_forms with
                | Error _ -> TUnknown
                | Ok inferred ->
                    (match List.rev body_forms with
                    | result :: _ -> inferred_form_type inferred result
                    | [] -> TNil))
          | _ -> TUnknown
        in
        let target_ty, key_ty =
          match string_assoc_opt target params with
          | Some (TVector _ as ty) -> (ty, TInt)
          | _ -> (
              match infer_inline_updater_return updater with
              | return_ty
                when not
                       (match return_ty with
                       | TUnknown | TMeta _ | TVar _ -> true
                       | _ -> false) ->
                  let key_ty =
                    match inferred_form_type params key with
                    | TUnknown | TMeta _ | TVar _ -> Type_solver.fresh ()
                    | ty -> ty
                  in
                  (Types.dynamic_map key_ty return_ty, key_ty)
              | _ ->
                  let dynamic = Types.dynamic_constraint TUnknown in
                  (dynamic, dynamic))
        in
        Result.bind (constrain_symbol target_ty params target) (fun params ->
            Result.bind (infer_expected key_ty params key) (fun params ->
                infer_all params (updater :: extra_arguments)))
    | FList
        [
          FSymbol "__lg_get";
          FSymbol target;
          FKeyword keyword;
          default;
        ] ->
        let field_ty = inferred_form_type params default in
        Result.bind
          (add_record_field_constraint target keyword field_ty params)
          (fun params -> infer_expected field_ty params default)
    | FList [ FSymbol "__lg_get"; FSymbol target; key ]
      when match key with FKeyword _ -> false | _ -> true -> (
        let infer_map () =
          let key_ty =
            match inferred_form_type params key with
            | TUnknown | TMeta _ | TVar _ -> Type_solver.fresh ()
            | ty -> ty
          in
          Result.bind
            (constrain_symbol
               (Types.dynamic_map key_ty (Type_solver.fresh ()))
               params target)
            (fun params -> infer_expected key_ty params key)
        in
        match
          string_assoc_opt target params
          |> Option.map Types.constraint_value_type
        with
        | Some (TNamed_record _) -> infer_expected TKeyword params key
        | Some map_ty -> (
            match Types.dynamic_map_types map_ty with
            | Some (key_ty, _) -> infer_expected key_ty params key
            | None -> infer_map ())
        | None -> infer_map ())
    | FList [ FSymbol operation; FSymbol array ]
      when String.equal operation "Array.length" ->
        let element_ty =
          match string_assoc_opt array params with
          | Some (TArray element_ty | TOcaml_app ("array", [ element_ty ])) ->
              element_ty
          | _ -> fresh_type_variable ("array_" ^ Names.sanitize_name array)
        in
        constrain_symbol (TArray element_ty) params array
    | FList [ FSymbol operation; FSymbol array; from; length ]
      when String.equal operation "Array.sub" ->
        let element_ty =
          match string_assoc_opt array params with
          | Some (TArray element_ty | TOcaml_app ("array", [ element_ty ])) ->
              element_ty
          | _ -> fresh_type_variable ("array_" ^ Names.sanitize_name array)
        in
        Result.bind (constrain_symbol (TArray element_ty) params array)
          (fun params ->
            Result.bind (infer_expected TInt params from) (fun params ->
                infer_expected TInt params length))
    | FList [ FSymbol operation; FSymbol array; index ]
      when has_source_name operation "__lg_aget"
           || has_source_name operation "unsafe-aget" -> (
        let element_ty =
          match string_assoc_opt array params with
          | Some (TArray element_ty | TOcaml_app ("array", [ element_ty ])) ->
              element_ty
          | _ -> fresh_type_variable ("array_" ^ Names.sanitize_name array)
        in
        match constrain_symbol (TArray element_ty) params array with
        | Error _ as error -> error
        | Ok params -> (
            match (operation, index) with
            | "__lg_aget", FSymbol index ->
                constrain_array_index_symbol params index
            | _ ->
                let index_ty = inferred_form_type params index in
                infer_expected
                  (if Types.equal index_ty TFloat then TFloat else TInt)
                  params index))
    | FList [ FSymbol "__lg_nth"; collection; index ] ->
        Result.bind (infer_sequence_form TUnknown params collection)
          (fun params -> infer_expected TInt params index)
    | FList [ FSymbol "__lg_nth"; collection; index; default ] ->
        Result.bind (infer_sequence_form TUnknown params collection)
          (fun params ->
            Result.bind (infer_expected TInt params index) (fun params ->
                infer_form params default))
    | FList (FSymbol qualified_method :: FSymbol receiver :: arguments)
      when (match String.split_on_char '/' qualified_method with
           | [ protocol_name; method_name ] ->
               String.starts_with ~prefix:"-" method_name
               && Option.is_some (lookup_protocol_constraint protocol_name)
           | _ -> false) -> (
        infer_known_call qualified_method params
          (FSymbol receiver :: arguments))
    | FList (FSymbol method_name :: FSymbol receiver :: arguments)
      when Option.is_some (lookup_protocol_constraint method_name) ->
        infer_known_call method_name params (FSymbol receiver :: arguments)
    | FList [ FSymbol "satisfies?"; FSymbol protocol_name; FSymbol receiver ]
      -> (
        match lookup_protocol_constraint protocol_name with
        | None -> Error.error ("unknown protocol " ^ protocol_name)
        | Some _ when Protocol_id.name (Protocol_id.of_string protocol_name) = "ISequential" ->
            constrain_optional_sequential TUnknown params receiver
        | Some constraint_ty ->
            constrain_symbol
              (Types.guarded_protocol_constraint constraint_ty)
              params receiver)
    | FList
        [
          FSymbol (("uncurried-call" | "uncurried-compare") as name);
          FSymbol fn;
          left;
          right;
        ] ->
        let left_ty = inferred_form_type params left in
        let right_ty = inferred_form_type params right in
        let return_ty =
          match string_assoc_opt fn params with
          | Some (TFn (_, (TUnknown | TMeta _ | TVar _)))
            when name = "uncurried-compare" ->
              TOcaml "int"
          | Some (TFn (_, return_ty)) -> return_ty
          | _ ->
              if name = "uncurried-compare" then TOcaml "int" else TUnknown
        in
        if name = "uncurried-compare" then
          let value_ty =
            match string_assoc_opt fn params with
            | Some (TFn ([ left; right ], _))
              when Types.equal left right
                   && not (Types.equal left TUnknown)
                   && (match left with TMeta _ | TVar _ -> false | _ -> true) ->
                left
            | _ -> (
                match (left_ty, right_ty) with
                | ty, _
                  when not (Types.equal ty TUnknown)
                       && (match ty with TMeta _ | TVar _ -> false | _ -> true) ->
                    ty
                | _, ty
                  when not (Types.equal ty TUnknown)
                       && (match ty with TMeta _ | TVar _ -> false | _ -> true) ->
                    ty
                | _ -> fresh_type_variable "ordering_value")
          in
          Result.bind
            (constrain_symbol
               (TFn ([ value_ty; value_ty ], return_ty))
               params fn)
            (fun params -> infer_expected_all value_ty params [ left; right ])
        else
          constrain_symbol
            (TFn ([ left_ty; right_ty ], return_ty))
            params fn
    | FList [ FSymbol "as-ordering"; FSymbol fn ] ->
        let fn_ty =
          match string_assoc_opt fn params with
          | Some (TFn (parameter_tys, (TOcaml "int" as return_ty))) ->
              TFn (parameter_tys, return_ty)
          | Some (TFn (parameter_tys, _)) -> TFn (parameter_tys, TInt)
          | _ ->
              let value_ty = fresh_type_variable "ordering_value" in
              TFn ([ value_ty; value_ty ], TInt)
        in
        constrain_symbol fn_ty params fn
    | FList [ FSymbol "seq-uncons"; FSymbol collection ] ->
        constrain_symbol
          (TSeq (fresh_type_variable "seq_uncons_element"))
          params collection
    | FList
        [
          FSymbol
            (("__lg_first" | "__lg_second" | "__lg_seq" | "__lg_rest" | "__lg_next")
              as operation);
          FSymbol collection;
        ] ->
        constrain_seqable
          (fresh_type_variable
             ("sequence_" ^ Names.sanitize_name operation ^ "_element"))
          params collection
    | FList
        [
          FSymbol
            ("__lg_first" | "__lg_second" | "__lg_seq" | "__lg_rest" | "__lg_next");
          FList [ FKeyword keyword; FSymbol record ];
        ] ->
        add_record_field_constraint record keyword
          (Types.seqable_constraint
             (fresh_type_variable
                ("sequence_" ^ Names.sanitize_name keyword ^ "_element")))
          params
    | FList
        [
          FSymbol
            (("__lg_first" | "__lg_second" | "__lg_seq" | "__lg_rest" | "__lg_next")
              as operation);
          collection;
        ] ->
        infer_expected
          (Types.seqable_constraint
             (fresh_type_variable
                ("sequence_" ^ Names.sanitize_name operation ^ "_element")))
          params collection
    | FList
        [
          FSymbol ("__lg_re-matches" | "__lg_re-seq");
          expression;
          source;
        ] -> (
        match infer_expected TRegex params expression with
        | Error _ as error -> error
        | Ok params -> infer_expected TString params source)
    | FList (FSymbol "__lg_list" :: values) -> (
        match infer_all params values with
        | Error _ as error -> error
        | Ok params ->
            let value_types = List.map (inferred_form_type params) values in
            let heterogeneous =
              match value_types with
              | [] | [ _ ] -> false
              | first :: rest ->
                  List.exists (fun ty -> not (Types.equal first ty)) rest
            in
            if not heterogeneous then Ok params
            else
              List.fold_left2
                (fun result value ty ->
                  match (result, value) with
                  | (Error _ as error), _ -> error
                  | Ok params, FSymbol name ->
                      constrain_symbol
                        (materialize_dynamic_unknown ty)
                        params name
                  | Ok params, _ -> Ok params)
                (Ok params) values value_types)
    | FList (FSymbol ("__lg_pr_str" | "__lg_pr" | "__lg_print_values") :: values) ->
        List.fold_left
          (fun result value ->
            Result.bind result (fun params ->
                match value with
                | FSymbol name when string_mem_assoc name params ->
                    constrain_printable_symbol params name
                | _ ->
                    infer_expected
                      (Types.printable_constraint (Type_solver.fresh ()))
                      params value))
          (Ok params) values
    | FList
        (FSymbol "__lg_apply" :: FSymbol "__lg_pr" :: arguments)
      -> (
        match List.rev arguments with
        | [] -> Ok params
        | collection :: reversed_fixed ->
            let printable =
              Types.printable_constraint (Type_solver.fresh ())
            in
            Result.bind
              (List.fold_left
                 (fun result argument ->
                   Result.bind result (fun params ->
                       infer_expected printable params argument))
                 (Ok params) (List.rev reversed_fixed))
              (fun params ->
                infer_expected (Types.seqable_constraint printable) params
                  collection))
    | FList
        (FSymbol "__lg_apply"
        :: FSymbol ("__lg_map" | "__lg_mapv")
        :: constructor_form
        :: fixed_and_rest)
      when List.length fixed_and_rest >= 2
           && is_variadic_vector_constructor params constructor_form ->
        let reversed = List.rev fixed_and_rest in
        let rest_collection = List.hd reversed in
        let fixed_collections = List.rev (List.tl reversed) in
        let element_ty = fresh_type_variable "zip_element" in
        let infer_collection params = function
          | FSymbol name -> constrain_symbol (TVector element_ty) params name
          | form -> infer_form params form
        in
        Result.bind
          (List.fold_left
             (fun result collection ->
               Result.bind result (fun params ->
                   infer_collection params collection))
             (Ok params) fixed_collections)
          (fun params ->
            match rest_collection with
            | FSymbol name ->
                constrain_seqable (TVector element_ty) params name
            | form -> infer_form params form)
    | FList (FSymbol "__lg_apply" :: function_form :: arguments) ->
        let is_dynamic_function_type ty =
          Types.is_dynamic ty
          || match ty with TUnknown | TMeta _ | TVar _ -> true | _ -> false
        in
        let dynamic_function =
          match function_form with
          | FSymbol name -> (
              match string_assoc_opt name params with
              | Some ty -> is_dynamic_function_type ty
              | None -> (
                  match lookup_function_ty name with
                  | Ok ty -> is_dynamic_function_type ty
                  | Error _ -> false))
          | _ ->
              is_dynamic_function_type
                (inferred_form_type params function_form)
        in
        if dynamic_function then
          let value_ty = fresh_type_variable "apply_value" in
          let result_ty = fresh_type_variable "apply_result" in
          let variadic_fn_ty =
            (* apply may call f with any number of arguments, so the
               demanded shape is a single variadic arity; concrete
               overload sets adapt through the variadic wrapper. *)
            TOverloaded_fn
              [
                {
                  fixed_params = [];
                  rest_param = Some value_ty;
                  return_ty = result_ty;
                };
              ]
          in
          let params =
            match function_form with
            | FSymbol name -> (
                match string_assoc_opt name params with
                | Some (TUnknown | TMeta _ | TVar _) ->
                    constrain_symbol variadic_fn_ty params name
                | _ -> Ok params)
            | _ -> Ok params
          in
          Result.bind params (fun params ->
              match List.rev arguments with
              | collection :: reversed_fixed ->
                  Result.bind
                    (infer_expected_all value_ty params
                       (List.rev reversed_fixed))
                    (fun params ->
                      match collection with
                      | FSymbol name -> constrain_seqable value_ty params name
                      | collection ->
                          infer_expected
                            (Types.seqable_constraint value_ty)
                            params collection)
              | [] -> Ok params)
        else (
          match List.rev arguments with
          | FSymbol collection :: reversed_fixed ->
              let fixed_count = List.length reversed_fixed in
              let fixed_arguments = List.rev reversed_fixed in
              let rec drop count values =
                if count <= 0 then values
                else
                  match values with
                  | [] -> []
                  | _ :: rest -> drop (count - 1) rest
              in
              let rec take count values =
                if count <= 0 then []
                else
                  match values with
                  | [] -> []
                  | value :: rest -> value :: take (count - 1) rest
              in
              let remaining_parameters = function
                | TFn (parameter_tys, _) -> drop fixed_count parameter_tys
                | TOverloaded_fn arities ->
                    arities
                    |> List.concat_map (fun arity ->
                           if fixed_count <= List.length arity.fixed_params then
                             drop fixed_count arity.fixed_params
                             @ Option.to_list arity.rest_param
                           else Option.to_list arity.rest_param)
                | _ -> []
              in
              let function_ty =
                match function_form with
                | FSymbol name -> (
                    match string_assoc_opt name params with
                    | Some ty -> ty
                    | None ->
                        lookup_function_ty name
                        |> Result.value ~default:TUnknown)
                | form -> inferred_form_type params form
              in
              let fixed_parameter_types =
                match function_ty with
                | TFn (parameter_tys, _)
                  when fixed_count <= List.length parameter_tys ->
                    take fixed_count parameter_tys
                | TOverloaded_fn arities ->
                    arities
                    |> List.find_map (fun arity ->
                           let declared_count =
                             List.length arity.fixed_params
                           in
                           if fixed_count <= declared_count then
                             Some (take fixed_count arity.fixed_params)
                           else
                             Option.map
                               (fun rest_ty ->
                                 arity.fixed_params
                                 @ List.init (fixed_count - declared_count)
                                     (fun _ -> rest_ty))
                               arity.rest_param)
                    |> Option.value
                         ~default:
                           (List.init fixed_count (fun _ -> TUnknown))
                | _ -> List.init fixed_count (fun _ -> TUnknown)
              in
              let sequence_concat_element =
                match function_ty with
                | TOverloaded_fn
                    ({ return_ty = TSeq element_ty; _ } :: _ as arities)
                  when List.for_all
                         (fun (arity : fn_arity) ->
                           Types.equal arity.return_ty (TSeq element_ty)
                           && List.for_all
                                (fun parameter_ty ->
                                  match
                                    Types.seqable_constraint_element
                                      parameter_ty
                                  with
                                  | Some actual -> Types.equal actual element_ty
                                  | None -> false)
                                arity.fixed_params
                           &&
                           match arity.rest_param with
                           | None -> true
                           | Some rest_ty -> (
                               match
                                 Types.seqable_constraint_element rest_ty
                               with
                               | Some actual -> Types.equal actual element_ty
                               | None -> false))
                         arities ->
                    Some element_ty
                | TOverloaded_fn _ | TFn _ | _ -> None
              in
              Result.bind
                (List.fold_left2
                   (fun result expected argument ->
                     Result.bind result (fun params ->
                         infer_expected expected params argument))
                   (Ok params) fixed_parameter_types fixed_arguments)
                (fun params ->
                  match (sequence_concat_element, function_ty, fixed_arguments) with
                  | Some element_ty, _, _ ->
                      let argument_constraint () =
                        Types.optional_seqable_constraint element_ty
                          (fresh_type_variable "concat_storage")
                      in
                      Result.bind
                        (List.fold_left
                           (fun result argument ->
                             Result.bind result (fun params ->
                                 infer_expected (argument_constraint ()) params
                                   argument))
                           (Ok params) fixed_arguments)
                        (fun params ->
                          constrain_seqable (argument_constraint ()) params
                            collection)
                  | None, TOverloaded_fn arities, constructor :: collections
                    when List.for_all
                           (fun (arity : fn_arity) ->
                             match arity.return_ty with
                             | TVector _ -> true
                             | _ -> false)
                         arities
                         && is_variadic_vector_constructor params constructor ->
                      let element_ty = fresh_type_variable "zip_element" in
                      Result.bind
                        (List.fold_left
                           (fun result collection ->
                             Result.bind result (fun params ->
                                 infer_expected (TVector element_ty) params
                                   collection))
                           (Ok params) collections)
                        (fun params ->
                          constrain_seqable (TVector element_ty) params
                            collection)
                  | None, _, _ ->
                      let element_ty =
                        match remaining_parameters function_ty with
                        | [] -> TUnknown
                        | first :: rest
                          when List.for_all (Types.equal first) rest ->
                            first
                        | _ -> Types.dynamic_constraint TUnknown
                      in
                      constrain_seqable element_ty params collection)
          | _ -> infer_all params arguments)
    | FList [ FSymbol ("__lg_map" | "__lg_mapv" | "__lg_run"); fn; collection ] ->
        let inferred_element_ty = inferred_unary_function_param params fn in
        let inferred_element_ty =
          match inferred_element_ty with
          | TUnknown | TMeta _ | TVar _ ->
              inferred_literal_collection_item params collection
          | ty -> ty
        in
        let element_ty =
          match inferred_element_ty with
          | TUnknown | TMeta _ | TVar _ -> fresh_type_variable "unary_map_item"
          | ty -> ty
        in
        let infer_collection =
          match collection with
          | FList [ FKeyword keyword; FSymbol name ] ->
              add_record_field_constraint name keyword
                (Types.seqable_constraint element_ty)
                params
          | form -> infer_sequence_form element_ty params form
        in
        Result.bind infer_collection
          (fun params ->
            match fn with
            | FSymbol name ->
                constrain_symbol
                  (TFn
                     ( [ element_ty ],
                       fresh_type_variable "unary_map_result" ))
                  params name
            | form -> infer_form params form)
    | FList (FSymbol ("__lg_map" | "__lg_mapv") :: fn :: collection_forms)
      when List.length collection_forms >= 2 -> (
        let collection_element_ty collection =
          let collection_ty = inferred_form_type params collection in
          match Types.next_seq_element collection_ty with
          | Some element_ty -> element_ty
          | None -> (
              match Types.seqable_constraint_element collection_ty with
              | Some element_ty -> element_ty
              | None -> TUnknown)
        in
        let variadic_callback_tys =
          match fn with
          | FSymbol name -> (
              let function_ty =
                match string_assoc_opt name params with
                | Some ty -> Ok ty
                | None -> lookup_function_ty name
              in
              match function_ty with
              | Ok (TOverloaded_fn arities) ->
                  arities
                  |> List.find_map (fun (arity : fn_arity) ->
                         match arity.rest_param with
                         | Some rest_ty
                           when List.length arity.fixed_params
                                <= List.length collection_forms ->
                             Some
                               (arity.fixed_params
                               @ List.init
                                   (List.length collection_forms
                                   - List.length arity.fixed_params)
                                   (fun _ -> rest_ty))
                         | Some _ | None -> None)
              | Ok _ | Error _ -> None)
          | _ -> None
        in
        let callback_tys =
          Option.value variadic_callback_tys
            ~default:(inferred_function_parameter_types params fn)
        in
        let element_tys =
          collection_forms
          |> List.mapi (fun index collection ->
                 match collection_element_ty collection with
                 | TUnknown | TMeta _ | TVar _ ->
                     List.nth_opt callback_tys index
                     |> Option.value ~default:TUnknown
                 | element_ty -> element_ty)
        in
        let function_ty = TFn (element_tys, TUnknown) in
        let rec constrain_collections params element_tys collections =
          match (element_tys, collections) with
          | [], [] -> Ok params
          | element_ty :: element_tys, collection :: collections ->
              Result.bind
                (infer_sequence_form element_ty params collection)
                (fun params ->
                  constrain_collections params element_tys collections)
          | _ -> assert false
        in
        let inferred_function =
          match variadic_callback_tys with
          | Some _ -> Ok params
          | None -> infer_expected function_ty params fn
        in
        Result.bind inferred_function (fun params ->
            constrain_collections params element_tys collection_forms))
    | FList
        [
          FSymbol "__lg_some";
          fn;
          collection;
        ] ->
        let dynamic_predicate =
          match fn with
          | FSymbol name -> (
              match string_assoc_opt name params with
              | Some ty -> Types.is_dynamic ty
              | None -> (
                  match lookup_function_ty name with
                  | Ok (TFn ([ parameter_ty ], _)) ->
                      Types.is_dynamic parameter_ty
                  | Ok _ | Error _ -> false))
          | _ -> false
        in
        let element_ty =
          if dynamic_predicate then Types.dynamic_constraint TUnknown
          else inferred_unary_function_param params fn
        in
        let element_ty =
          if
            (not dynamic_predicate)
            && Types.is_dynamic element_ty
            && not (callback_compares_destructured_values fn)
            && not (callback_checks_runtime_type fn)
          then
            TUnknown
          else element_ty
        in
        Result.bind
          (infer_sequence_form element_ty params collection)
          (fun params ->
            match fn with
            | FSymbol name -> (
                match string_assoc_opt name params with
                | Some (TUnknown | TMeta _ | TVar _) ->
                    constrain_symbol
                      (TFn ([ element_ty ], TUnknown))
                      params name
                | Some _ | None -> infer_form params fn)
            | _ -> infer_expected (TFn ([ element_ty ], TUnknown)) params fn)
    | FList
        [
          FSymbol "__lg_reduce";
          reducer;
          FList [ FSymbol first_name; FSymbol first_source ];
          FList [ FSymbol next_name; FSymbol next_source ];
        ]
      when has_source_name first_name "__lg_first"
           && has_source_name next_name "__lg_next"
           && String.equal first_source next_source ->
        let accumulator_ty, element_ty =
          inferred_reducer_types params (Type_solver.fresh ()) reducer
        in
        let element_ty =
          match element_ty with
          | TUnknown | TMeta _ | TVar _ -> accumulator_ty
          | element_ty -> element_ty
        in
        Result.bind
          (infer_sequence_form element_ty params (FSymbol first_source))
          (fun params ->
            infer_expected
              (TFn ([ accumulator_ty; element_ty ], accumulator_ty))
              params reducer)
    | FList [ FSymbol "__lg_reduce"; reducer; init; collection ] -> (
        let declared_accumulator_ty, declared_element_ty =
          match reducer with
          | FSymbol name -> (
              let reducer_ty =
                match string_assoc_opt name params with
                | Some ty -> Ok ty
                | None -> lookup_function_ty name
              in
              match reducer_ty with
              | Ok (TFn ([ accumulator_ty; element_ty ], _)) ->
                  (accumulator_ty, element_ty)
              | Ok (TOverloaded_fn arities) -> (
                  match
                    List.find_opt
                      (fun (arity : fn_arity) ->
                        Option.is_none arity.rest_param
                        && List.length arity.fixed_params = 2)
                      arities
                  with
                  | Some { fixed_params = [ accumulator_ty; element_ty ]; _ }
                    ->
                      (accumulator_ty, element_ty)
                  | Some _ | None -> (TUnknown, TUnknown))
              | Ok _ | Error _ -> (TUnknown, TUnknown))
          | _ -> (TUnknown, TUnknown)
        in
        let accumulator_ty =
          match declared_accumulator_ty with
          | TUnknown | TMeta _ | TVar _ -> (
              match init with
              | FMap [] | FList [ FSymbol "__lg_hash-map" ] ->
                  Types.dynamic_map (Type_solver.fresh ())
                    (Type_solver.fresh ())
              | _ -> inferred_reduce_initial_type params reducer init)
          | ty -> ty
        in
        let inferred_accumulator_ty, inferred_element_ty =
          inferred_reducer_types params accumulator_ty reducer
        in
        let accumulator_ty =
          refine_type accumulator_ty inferred_accumulator_ty
        in
        Result.bind (infer_expected accumulator_ty params init) (fun params ->
            let element_ty =
              match (declared_element_ty, collection) with
              | (TUnknown | TMeta _ | TVar _), _ -> (
                  match collection with
                  | FSymbol collection -> (
                      match string_assoc_opt collection params with
                      | Some collection_ty -> (
                          match
                            Types.seqable_constraint_element collection_ty
                          with
                          | Some (TUnknown | TMeta _ | TVar _) | None ->
                              inferred_element_ty
                          | Some element_ty -> element_ty)
                      | None -> inferred_element_ty)
                  | _ -> inferred_element_ty)
              | ty, _ -> ty
            in
            Result.bind (infer_sequence_form element_ty params collection)
              (fun params ->
                infer_expected
                  (TFn ([ accumulator_ty; element_ty ], TUnknown))
                  params reducer)))
    | FList [ FSymbol "__lg_reduce"; reducer; collection ] ->
        let declared_element_ty =
          match reducer with
          | FSymbol name -> (
              let reducer_ty =
                match string_assoc_opt name params with
                | Some ty -> Ok ty
                | None -> lookup_function_ty name
              in
              match reducer_ty with
              | Ok (TFn ([ _accumulator_ty; element_ty ], _)) -> element_ty
              | Ok (TOverloaded_fn arities) -> (
                  match
                    List.find_opt
                      (fun (arity : fn_arity) ->
                        Option.is_none arity.rest_param
                        && List.length arity.fixed_params = 2)
                      arities
                  with
                  | Some { fixed_params = [ _accumulator_ty; element_ty ]; _ }
                    ->
                      element_ty
                  | Some _ | None -> TUnknown)
              | Ok _ | Error _ -> TUnknown)
          | _ -> TUnknown
        in
        Result.bind
          (infer_sequence_form declared_element_ty params collection)
          (fun params ->
            infer_expected
              (TFn
                 ( [ declared_element_ty; declared_element_ty ],
                   declared_element_ty ))
              params reducer)
    | FList [ FSymbol "__lg_sort"; FSymbol collection ] ->
        constrain_seqable (Types.dynamic_constraint TUnknown) params collection
    | FList [ FSymbol "__lg_sort"; FSymbol comparator; FSymbol collection ] ->
        let element_ty =
          match
            match string_assoc_opt comparator params with
            | Some ty -> Ok ty
            | None -> lookup_function_ty comparator
          with
          | Ok (TFn ([ left; right ], TInt)) -> refine_type left right
          | Ok (TOverloaded_fn arities) -> (
              match select_fn_arity arities 2 with
              | Some { fixed_params = [ left; right ]; return_ty = TInt; _ } ->
                  refine_type left right
              | Some _ | None -> Types.dynamic_constraint TUnknown)
          | Ok _ | Error _ -> Types.dynamic_constraint TUnknown
        in
        constrain_seqable element_ty params collection
    | FList [ FSymbol "__lg_sort"; FSymbol comparator; collection ] ->
        let element_ty =
          match
            match string_assoc_opt comparator params with
            | Some ty -> Ok ty
            | None -> lookup_function_ty comparator
          with
          | Ok (TFn ([ left; right ], TInt)) -> refine_type left right
          | Ok (TOverloaded_fn arities) -> (
              match select_fn_arity arities 2 with
              | Some { fixed_params = [ left; right ]; return_ty = TInt; _ } ->
                  refine_type left right
              | Some _ | None -> Types.dynamic_constraint TUnknown)
          | Ok _ | Error _ -> Types.dynamic_constraint TUnknown
        in
        infer_sequence_form element_ty params collection
    | FList [ FSymbol "__lg_sort"; _comparator; FSymbol collection ] ->
        constrain_seqable (Types.dynamic_constraint TUnknown) params collection
    | FList
        (FSymbol
           ( "__lg_add" | "__lg_subtract" | "__lg_multiply"
           | "__lg_divide" | "__lg_divide-melange" | "__lg_max"
           | "__lg_min" )
        :: args)
      ->
        let expected_ty =
          if
            List.exists
              (fun arg ->
                Types.equal (numeric_form_type params arg)
                  (TOcaml "Lg_runtime.Runtime_decimal.t"))
              args
          then TOcaml "Lg_runtime.Runtime_decimal.t"
          else if
            List.exists
              (fun arg -> Types.equal (numeric_form_type params arg) TFloat)
              args
          then TFloat
          else TInt
        in
        infer_expected_all expected_ty params args
    | FList [ FSymbol "__lg_with-precision"; precision; rounding_mode; thunk ] ->
        Result.bind (infer_expected TInt params precision) (fun params ->
            Result.bind
              (infer_expected TString params rounding_mode)
              (fun params -> infer_form params thunk))
    | FList
        [
          FSymbol
            ( "__lg_zero-predicate" | "__lg_pos-predicate"
            | "__lg_neg-predicate" );
          arg;
        ] ->
        let arg_ty =
          match inferred_form_type params arg with
          | TUnknown ->
              inferred_call_return_type ~lookup_function_ty params arg
          | ty -> ty
        in
        (match arg_ty with
        | TUnknown | TMeta _ | TVar _ -> infer_expected TInt params arg
        | _ -> infer_form params arg)
    | FList [ FSymbol "__lg_abs"; arg ] ->
        let arg_ty =
          match inferred_form_type params arg with
          | TUnknown ->
              inferred_call_return_type ~lookup_function_ty params arg
          | ty -> ty
        in
        infer_expected
          (if Types.equal arg_ty TFloat then TFloat else TInt)
          params arg
    | FList [ FSymbol "__lg_dec"; arg ] ->
        let arg_ty =
          match inferred_form_type params arg with
          | TUnknown ->
              inferred_call_return_type ~lookup_function_ty params arg
          | ty -> ty
        in
        let expected_ty =
          if Types.equal arg_ty TFloat then TFloat
          else if Types.equal arg_ty (TOcaml "int") then TOcaml "int"
          else TInt
        in
        infer_expected expected_ty params arg
    | FList [ FSymbol "__lg_bigdec"; arg ]
    | FList [ FSymbol "__lg_bigint"; arg ] ->
        infer_form params arg
    | FList [ FSymbol "__lg_constantly"; arg ] -> infer_form params arg
    | FList [ FSymbol "__lg_ex-message"; arg ] ->
        infer_expected (TOcaml "exn") params arg
    | FList [ FSymbol "__lg_ex-cause"; arg ] ->
        infer_expected (TOcaml "exn") params arg
    | FList [ FSymbol "__lg_ex-data"; arg ] ->
        infer_expected (TOcaml "exn") params arg
    | FList [ FSymbol "__lg_exec-tap-fn"; thunk ] ->
        infer_expected (TFn ([], TUnit)) params thunk
    | FList [ FSymbol "__lg_add-tap"; callback ]
    | FList [ FSymbol "__lg_remove-tap"; callback ] ->
        infer_expected
          (TFn ([ Types.printable_constraint TUnknown ], TUnknown))
          params callback
    | FList [ FSymbol "__lg_tap"; value ] -> infer_form params value
    | FList [ FSymbol "__lg_flatten"; collection ] ->
        infer_form params collection
    | FList [ FSymbol "__lg_memoize"; function_form ] ->
        infer_form params function_form
    | FList [ FSymbol "__lg_cljs-test-report"; reporter; event ] ->
        Result.bind (infer_expected TKeyword params reporter) (fun params ->
            match event with
            | FSymbol _ ->
                infer_expected (Types.dynamic_constraint TUnknown) params event
            | _ -> Ok params)
    | FList [ FSymbol "__lg_multimethod-methods"; _multifn ] -> Ok params
    | FList [ FSymbol "__lg_multimethod-dispatch-fn"; _multifn ] -> Ok params
    | FList [ FSymbol "__lg_multimethod-get-method"; _multifn; _dispatch ] ->
        Ok params
    | FList [ FSymbol "__lg_multimethod-remove-method"; _multifn; _dispatch ] ->
        Ok params
    | FList [ FSymbol "__lg_multimethod-remove-all-methods"; _multifn ] ->
        Ok params
    | FList [ FSymbol "__lg_multimethod-default-dispatch-val"; _multifn ] ->
        Ok params
    | FList
        [
          FSymbol "__lg_multimethod-prefer-method";
          _multifn;
          _preferred;
          _other;
        ] ->
        Ok params
    | FList [ FSymbol "__lg_multimethod-prefers"; _multifn ] -> Ok params
    | FList [ FSymbol "__lg_re-pattern"; arg ] ->
        let expected_ty =
          if Types.equal (inferred_form_type params arg) TRegex then TRegex
          else TString
        in
        infer_expected expected_ty params arg
    | FList [ FSymbol "__lg_double"; (FSymbol _ as arg) ] ->
        let expected_ty =
          if Types.equal (inferred_form_type params arg) TFloat then TFloat
          else TInt
        in
        infer_expected expected_ty params arg
    | FList [ FSymbol ("__lg_int" | "__lg_long" | "__lg_double"); arg ] ->
        infer_form params arg
    | FList
        (FSymbol
           ( "__lg_numeric-equal" | "__lg_less" | "__lg_less-equal"
           | "__lg_greater" | "__lg_greater-equal" )
        :: args) ->
        let ordering_type = function
          | FSymbol name -> (
              match string_assoc_opt name params with
              | Some ty -> ty
              | None -> (
                  match lookup_function_ty name with
                  | Ok ty -> ty
                  | Error _ -> TUnknown))
          | arg -> inferred_form_or_call_type ~lookup_function_ty params arg
        in
        let ordering_type arg = ordering_type arg |> Types.constraint_value_type in
        let expected_ty =
          if
            List.exists
              (fun arg -> Types.equal (ordering_type arg) TFloat)
              args
          then TFloat
          else if
            List.exists
              (fun arg -> Types.equal (ordering_type arg) (TOcaml "int64"))
              args
          then TOcaml "int64"
          else TInt
        in
        infer_expected_all expected_ty params args
    | FList (FSymbol "__lg_equal" :: args) ->
        let expected_ty =
          let inferred_equality_type arg =
            inferred_form_or_call_type ~lookup_function_ty params arg
            |> Types.constraint_value_type
          in
          let concrete =
            args
            |> List.filter_map (fun arg ->
                   match inferred_equality_type arg with
                   | TUnknown | TMeta _ | TVar _ -> None
                   | ty when Types.is_dynamic ty -> None
                   | ty -> Some ty)
            |> List.fold_left
                 (fun unique ty ->
                   if List.exists (Types.same_shape ty) unique then unique
                   else ty :: unique)
                 []
          in
          let has_dynamic_argument =
            List.exists
              (fun arg -> Types.is_dynamic (inferred_form_type params arg))
              args
          in
          match concrete with
          | types
            when List.exists Edn_value_elaborator.is_value_type types ->
              TOcaml "Lg_edn_backend.t"
          | [ ty ] -> ty
          | _ :: _ :: _
            when List.exists
                   (function
                     | FSymbol name -> string_mem_assoc name params
                     | _ -> false)
                   args ->
              Types.dynamic_constraint TUnknown
          | ty :: _ -> ty
          | [] when has_dynamic_argument ->
              Types.dynamic_constraint TUnknown
          | [] ->
              args
              |> List.find_map (fun arg ->
                     match inferred_equality_type arg with
                     | (TMeta _ | TVar _) as ty -> Some ty
                     | _ -> None)
              |> Option.value ~default:(fresh_type_variable "equality")
        in
        if Types.equal expected_ty TSymbol then
          List.fold_left
            (fun result arg ->
              Result.bind result (fun params ->
                  match arg with
                  | FSymbol name -> (
                      match string_assoc_opt name params with
                      | Some (TUnknown | TMeta _ | TVar _) ->
                          constrain_symbol_predicate params name
                      | Some _ | None -> infer_expected TSymbol params arg)
                  | _ -> infer_expected TSymbol params arg))
            (Ok params) args
        else infer_expected_all expected_ty params args
    | FList
        [
          FSymbol "__lg_select-keys";
          FList [ FKeyword keyword; FSymbol record ];
          FSymbol keys;
        ] ->
        let key_ty = fresh_type_variable "select_keys_key" in
        let value_ty = fresh_type_variable "select_keys_value" in
        Result.bind (constrain_seqable key_ty params keys) (fun params ->
            add_record_field_constraint record keyword
              (Types.dynamic_map key_ty value_ty)
              params)
    | FList [ FSymbol "__lg_select-keys"; FSymbol target; keys ] -> (
        let key_ty = fresh_type_variable "select_keys_key" in
        let value_ty = fresh_type_variable "select_keys_value" in
        match keys with
        | FSymbol name ->
            Result.bind (constrain_seqable key_ty params name) (fun params ->
                constrain_symbol (Types.dynamic_map key_ty value_ty) params
                  target)
        | form ->
            Result.bind
              (infer_expected
                 (Types.seqable_constraint key_ty)
                 params form)
              (fun params ->
                constrain_symbol (Types.dynamic_map key_ty value_ty) params
                  target))
    | FList
        [ FKeyword nested_keyword; FList [ FKeyword keyword; FSymbol name ] ] ->
        add_record_field_constraint name keyword
          (TRecord
             [
               make_field nested_keyword
                 (Types.dynamic_constraint TUnknown);
             ])
          params
    | FList
        [
          FKeyword keyword;
          FList
            [ FSymbol "__lg_first"; collection ];
        ] ->
        infer_sequence_form
          (TRecord
             [
               make_field keyword
                 (fresh_type_variable
                    ("projected_" ^ Names.sanitize_name keyword));
             ])
          params collection
    | FList [ FKeyword keyword; FSymbol name ] ->
        let field_ty =
          match string_assoc_opt name params with
          | Some ty
            when Option.is_some (Types.contains_constraint_info ty) ->
              TNullable
                (fresh_type_variable
                   ("field_" ^ Names.sanitize_name keyword))
          | Some _ | None ->
              fresh_type_variable
                ("field_" ^ Names.sanitize_name keyword)
        in
        add_record_field_constraint name keyword field_ty params
    | (FList [ FKeyword _; _ ] as form) ->
        infer_expected (Type_solver.fresh ()) params form
    | FList [ FKeyword keyword; FSymbol name; default ] ->
        let field_ty = inferred_form_type params default in
        Result.bind
          (add_record_field_constraint name keyword field_ty params)
          (fun params -> infer_expected field_ty params default)
    | FList
        [
          FSymbol "__lg_contains";
          FSymbol name;
          (FKeyword _ as key);
        ] -> (
        match constrain_contains TKeyword params name with
        | Error _ as err -> err
        | Ok params -> infer_expected TKeyword params key)
    | FList [ FSymbol "__lg_contains"; FSymbol name; key ] -> (
        let target_ty =
          match string_assoc_opt name params with
          | Some ty -> ty
          | None -> (
              match lookup_function_ty name with
              | Ok (TRef value_ty) -> value_ty
              | Ok ty -> ty
              | Error _ -> TUnknown)
        in
        let collection_ty, key_ty =
          match target_ty with
          | TSet element_ty -> (TSet element_ty, element_ty)
          | TVector element_ty -> (TVector element_ty, TInt)
          | collection_ty -> (
              match Types.dynamic_map_types collection_ty with
              | Some (key_ty, _) -> (collection_ty, key_ty)
              | None ->
                  let key_ty =
                    match inferred_form_type params key with
                    | TUnknown | TMeta _ | TVar _ ->
                        fresh_type_variable "contains_key"
                    | key_ty -> key_ty
                  in
                  (Types.contains_constraint key_ty, key_ty))
        in
        let infer_collection =
          match Types.contains_constraint_info collection_ty with
          | Some _ -> constrain_contains key_ty params name
          | None -> infer_expected collection_ty params (FSymbol name)
        in
        match infer_collection with
        | Error _ as error -> error
        | Ok params -> infer_expected key_ty params key)
    | FList [ FSymbol "__lg_contains"; target; key ] ->
        let target_ty =
          match inferred_form_type params target with
          | TUnknown ->
              inferred_call_return_type ~lookup_function_ty params target
          | ty -> ty
        in
        let concrete_key_ty =
          match target_ty with
          | TSet element_ty -> Some element_ty
          | TVector _ -> Some TInt
          | TMap_keys -> Some TKeyword
          | target_ty -> (
              match Types.contains_constraint_info target_ty with
              | Some (key_ty, _) -> Some key_ty
              | None -> Option.map fst (Types.dynamic_map_types target_ty))
        in
        let key_ty =
          match concrete_key_ty with
          | Some key_ty -> key_ty
          | None -> (
              match inferred_form_type params key with
              | TUnknown | TMeta _ | TVar _ ->
                  fresh_type_variable "contains_key"
              | key_ty -> key_ty)
        in
        let infer_target =
          match concrete_key_ty with
          | Some _ -> infer_form params target
          | None ->
              infer_expected (Types.contains_constraint key_ty) params target
        in
        Result.bind infer_target (fun params -> infer_expected key_ty params key)
    | FList
        [ FSymbol "__lg_get-in"; target; FVector keys ] ->
        infer_form params (Core_form_expansion.get_in target keys None)
    | FList
        [
          FSymbol "__lg_get-in";
          target;
          FVector keys;
          default;
        ] ->
        infer_form params
          (Core_form_expansion.get_in target keys (Some default))
    | FList
        [
          FSymbol "__lg_assoc-in";
          target;
          FVector keys;
          value;
        ] ->
        infer_assoc_in params target keys value
    | FList
        (FSymbol "__lg_update-in"
        :: target :: FVector (_ :: _ as keys) :: function_form
        :: argument_forms) ->
        infer_form params
          (Core_form_expansion.update_in target keys function_form argument_forms)
    | FList
        (FSymbol "__lg_dissoc" :: target :: keys) ->
        (match
           Types.dynamic_map_types (inferred_form_type params target)
         with
        | Some (key_ty, _) ->
            Result.bind (infer_form params target) (fun params ->
                infer_expected_all key_ty params keys)
        | None -> (
            let key_ty = fresh_type_variable "dissoc_key" in
            let value_ty = fresh_type_variable "dissoc_value" in
            match target with
            | FSymbol name ->
                Result.bind
                  (constrain_symbol
                     (Types.dynamic_map key_ty value_ty)
                     params name)
                  (fun params -> infer_expected_all key_ty params keys)
            | _ -> infer_all params (target :: keys)))
    | FList (FSymbol "__lg_assoc" :: target :: pairs) ->
        infer_assoc params target pairs
    | FList (FSymbol "__lg_subvec" :: collection :: indexes)
      when List.length indexes = 1 || List.length indexes = 2 ->
        let element_ty =
          match inferred_form_type params collection with
          | TVector element_ty -> element_ty
          | _ -> Type_solver.fresh ()
        in
        Result.bind
          (infer_expected (TVector element_ty) params collection)
          (fun params -> infer_expected_all TInt params indexes)
    | FList
        (FSymbol "__lg_conj"
        :: (FList [ FSymbol "__lg_get"; _; _ ] as target)
        :: values) -> infer_conj_get params target values
    | FList (FSymbol "__lg_conj" :: target :: values) -> (
        let inferred_value_type value =
          let value_ty =
            match value with
            | FList (FSymbol "record" :: _) ->
                inferred_binding_form_type params value
            | _ -> inferred_form_type params value
          in
          match value_ty with
          | (TUnknown | TMeta _ | TVar _) as unresolved -> (
              match value with
              | FList (FSymbol name :: arguments) -> (
                  match lookup_function_ty name with
                  | Ok (TFn (parameters, return_ty))
                    when List.length parameters = List.length arguments ->
                      return_ty
                  | Ok (TOverloaded_fn arities) -> (
                      match select_fn_arity arities (List.length arguments) with
                      | Some arity -> arity.return_ty
                      | None -> unresolved)
                  | Ok _ | Error _ ->
                      inferred_call_return_type ~lookup_function_ty params value)
              | _ -> unresolved)
          | ty -> ty
        in
        let element_ty =
          values
          |> List.find_map (fun value ->
                 match inferred_value_type value with
                 | TUnknown -> None
                 | ty -> Some (stored_value_type ty))
          |> Option.value ~default:TUnknown
        in
        let collection_ty =
          match inferred_form_type params target with
          | TList _ -> TList element_ty
          | TSeq _ -> TSeq element_ty
          | TOcaml_app (name, [ _ ]) when Types.is_next_seq_type_name name ->
              TSeq element_ty
          | TSet inner -> (
              let element_ty =
                match inner with
                | ty when Types.is_dynamic element_ty ->
                    ty
                | TUnknown | TMeta _ | TVar _ -> element_ty
                | ty
                  when Types.assignable ~policy:Host_boundary ~expected:ty
                         ~actual:element_ty ->
                    ty
                | ty
                  when (Types.is_dynamic ty || Type_solver.is_open ty)
                       && not (Types.equal element_ty TUnknown)
                       &&
                       (match element_ty with
                       | TMeta _ | TVar _ -> false
                       | _ -> not (Types.is_dynamic element_ty)) ->
                    element_ty
                | ty when Types.is_dynamic ty || Type_solver.is_open ty ->
                    refine_type ty element_ty
                | ty -> refine_type ty element_ty
              in
              match Types.set_module_name element_ty with
              | Ok _ -> TSet element_ty
              | Error _ -> Types.dynamic_constraint (TSet TUnknown))
          | TFn ([ predicate_arg ], TBool) ->
              TSet (refine_type element_ty predicate_arg)
          | TVector _ -> TVector element_ty
          | TNil -> TList element_ty
          | TUnknown | TMeta _ | TVar _ -> TVector element_ty
          | _ -> Types.dynamic_constraint TUnknown
        in
        match infer_expected collection_ty params target with
        | Error _ as error -> error
        | Ok params ->
            let value_ty =
              if Types.is_dynamic collection_ty then
                Types.dynamic_constraint TUnknown
              else element_ty
            in
            infer_expected_all value_ty params values)
    | (FList (FSymbol "__lg_list-star" :: _) as form) ->
        infer_expected TUnknown params form
    | FList [ FSymbol "__lg_cons"; value; collection ] ->
        let element_ty =
          match inferred_form_type params value with
          | TUnknown | TMeta _ | TVar _ -> Type_solver.fresh ()
          | ty -> ty
        in
        Result.bind (infer_expected element_ty params value) (fun params ->
            infer_expected
              (Types.seqable_constraint element_ty)
              params collection)
    | FList [ FSymbol "__lg_reduce-kv"; reducer; init; FSymbol name ] -> (
        let key_ty, value_ty = inferred_kv_reducer_types params init reducer in
        let unresolved = function
          | TUnknown | TMeta _ | TVar _ -> fresh_type_variable "map"
          | ty -> ty
        in
        match
          infer_expected
            (Types.dynamic_map
               (unresolved key_ty)
               (unresolved value_ty))
            params (FSymbol name)
        with
        | Error _ as error -> error
        | Ok params -> infer_all params [ reducer; init ])
    | FList [ FSymbol "__lg_reduce-kv"; reducer; init; collection ]
      when
        (match inferred_form_type params collection with
        | TUnknown | TMeta _ | TVar _ -> true
        | _ -> false) -> (
        let key_ty, value_ty = inferred_kv_reducer_types params init reducer in
        let unresolved = function
          | TUnknown | TMeta _ | TVar _ -> fresh_type_variable "map"
          | ty -> ty
        in
        match
          infer_expected
            (Types.dynamic_map
               (unresolved key_ty)
               (unresolved value_ty))
            params collection
        with
        | Error _ as error -> error
        | Ok params -> infer_all params [ reducer; init ])
    | FList (FSymbol "__lg_format" :: format :: args) ->
        let requirements = Array.make (List.length args) [] in
        (match format with
        | FString source ->
            (try
               Runtime_format_spec.iter source ~text:(fun _ -> ())
                 ~conversion:(fun spec ->
                   let expected = match Char.lowercase_ascii spec.code with
                     | 'd' | 'o' | 'x' -> Some TInt
                     | 'e' | 'f' | 'g' -> Some TFloat
                     | _ -> None
                   in
                   match spec.argument, expected with
                   | Some index, Some ty when index < Array.length requirements ->
                       requirements.(index) <- ty :: requirements.(index)
                   | _ -> ())
             with Invalid_argument _ -> Array.fill requirements 0 (Array.length requirements) [])
        | _ -> ());
        Result.bind (infer_expected TString params format) (fun params ->
          List.fold_left
            (fun result (index, argument) ->
              Result.bind result (fun params ->
                let actual = inferred_form_or_call_type ~lookup_function_ty params argument in
                match requirements.(index) with
                | expected :: rest
                  when Type_solver.is_open actual && List.for_all (Types.equal expected) rest ->
                    infer_expected expected params argument
                | _ -> infer_form params argument))
            (Ok params) (List.mapi (fun index argument -> index, argument) args))
    | FList (FSymbol ("__lg_str" | "__lg_print_str") :: args) ->
        List.fold_left
          (fun result arg ->
            Result.bind result (fun params ->
                match arg with
                | FSymbol name when string_mem_assoc name params ->
                    constrain_printable_symbol params name
                | _ ->
                    infer_expected
                      (Types.printable_constraint (Type_solver.fresh ()))
                      params arg))
          (Ok params) args
    | FList [ FSymbol ex_info; message; data ]
      when has_source_name ex_info "ex-info" ->
        Result.bind (infer_expected TString params message) (fun params ->
            match data with
            | FMap _ -> infer_exception_data_literal params data
            | _ -> infer_expected (Types.dynamic_constraint TUnknown) params data)
    | FList [ FSymbol ex_info; message; data; cause ]
      when has_source_name ex_info "ex-info" ->
        Result.bind (infer_expected TString params message) (fun params ->
            Result.bind
              (match data with
              | FMap _ -> infer_exception_data_literal params data
              | _ -> infer_expected (Types.dynamic_constraint TUnknown) params data)
              (fun params -> infer_expected (TOcaml "exn") params cause))
    | FList [ FSymbol "if"; condition; then_form; else_form ] -> (
        match infer_truthy params condition with
        | Error _ as err -> err
        | Ok params -> (
            match literal_truthiness condition with
            | Some true -> infer_form params then_form
            | Some false -> infer_form params else_form
            | None ->
            let previous_hints = !branch_hint_symbols in
            let then_params =
              instance_branch_params ~matching:true params condition
              |> fun params ->
              successful_call_branch_params params condition
            in
            (
            match with_branch (fun () -> infer_form then_params then_form) with
            | Error _ as err -> err
            | Ok inferred ->
                let inferred =
                  restore_instance_branch_param params inferred condition
                  |> fun inferred ->
                  restore_successful_call_branch_params params inferred condition
                in
                let else_params =
                  instance_branch_params ~matching:false inferred condition
                in
                Result.map
                  (fun inferred ->
                    let inferred =
                      restore_instance_branch_param params inferred condition
                      |> fun inferred ->
                      restore_successful_call_branch_params params inferred
                        condition
                    in
                    let inferred =
                      restore_branch_evidence params inferred previous_hints
                        condition
                    in
                    let then_ty =
                      returned_vector_type inferred then_form
                      |> Option.value
                           ~default:(inferred_form_type inferred then_form)
                    in
                    let else_ty =
                      returned_vector_type inferred else_form
                      |> Option.value
                           ~default:(inferred_form_type inferred else_form)
                    in
                    let inferred =
                      match then_ty, else_ty with
                      | TMeta _, TMeta _ -> (
                          match Type_solver.unify Type_solver.empty then_ty else_ty with
                          | Error _ -> inferred
                          | Ok substitutions ->
                              List.map
                                (fun (name, ty) ->
                                  (name, Type_solver.apply substitutions ty))
                                inferred)
                      | _ -> inferred
                    in
                    inferred
                    |> fun params ->
                    refine_returned_seqable_vector params then_form else_ty
                    |> fun params ->
                    refine_returned_seqable_vector params else_form then_ty)
                  (with_branch (fun () -> infer_form else_params else_form)))))
    | FList [ FSymbol "if"; condition; then_form ] -> (
        match infer_truthy params condition with
        | Error _ as err -> err
        | Ok params ->
            let previous_hints = !branch_hint_symbols in
            let then_params =
              successful_call_branch_params params condition
            in
            Result.map
              (fun inferred ->
                restore_successful_call_branch_params params inferred condition
                |> fun inferred ->
                restore_branch_evidence params inferred previous_hints condition)
              (with_branch (fun () -> infer_form then_params then_form)))
    | FList (FSymbol "try" :: forms) ->
        let is_catch = function
          | FList (FSymbol "catch" :: _) -> true
          | _ -> false
        in
        let body_forms, catch_forms =
          List.partition (fun form -> not (is_catch form)) forms
        in
        let catch_bodies =
          catch_forms
          |> List.filter_map (function
               | FList (FSymbol "catch" :: _pattern :: body_forms) ->
                   Some body_forms
               | _ -> None)
        in
        let all_forms = body_forms @ List.concat catch_bodies in
        (* Elaboration merges the static branch types after inference resolves
           host calls. Unresolved branches must not impose dynamic storage. *)
        infer_all params all_forms
    | FList (FSymbol "match" :: target :: clauses) ->
        infer_match params target clauses
    | FList (FSymbol "case" :: target :: clauses) ->
        let rec grouped_pattern = function
          | [] -> FSymbol "_"
          | [ pattern ] -> pattern
          | pattern :: rest ->
              FList [ FSymbol "or"; pattern; grouped_pattern rest ]
        in
        let pattern = function
          | FList patterns -> grouped_pattern patterns
          | pattern -> pattern
        in
        let rec pairs acc = function
          | [] -> List.rev (FSymbol "nil" :: FSymbol "_" :: acc)
          | [ default ] -> List.rev (default :: FSymbol "_" :: acc)
          | constant :: result :: rest ->
              pairs (result :: pattern constant :: acc) rest
        in
        infer_match params target (pairs [] clauses)
    | FList [ FSymbol "__lg_set"; collection ] ->
        infer_collection params collection
    | FList (FSymbol ("__lg_doseq" | "for") :: bindings :: body_forms) ->
        infer_generator_bindings params bindings body_forms
    | FList (FSymbol "do" :: body_forms) -> infer_all params body_forms
    | FList (FSymbol "loop" :: FVector bindings :: body_forms) -> (
        let rec pairs acc = function
          | [] -> Some (List.rev acc)
          | FSymbol local :: value :: rest -> pairs ((local, value) :: acc) rest
          | _ -> None
        in
        match pairs [] bindings with
        | None -> infer_all params body_forms
        | Some bindings ->
            Result.bind
              (infer_all params (List.map snd bindings))
              (fun params ->
            let initializer_type value =
              match inferred_form_type params value with
              | TUnknown ->
                  inferred_call_return_type
                    ~lookup_function_ty:lookup_loop_initializer_type params
                    value
              | ty -> ty
            in
            let local_params =
              bindings
              |> List.map (fun (local, value) ->
                     let ty = initializer_type value in
                     let ty =
                       if Types.equal ty TUnknown then
                         fresh_type_variable
                           ("loop_" ^ Names.sanitize_name local)
                       else ty
                     in
                     (local, ty))
            in
            let equality_first_locals =
              let rec collect locals = function
                | FList (FSymbol "__lg_equal" :: operands) ->
                    List.fold_left
                      (fun locals -> function
                        | FList
                            [
                              FSymbol "__lg_first";
                              FSymbol local;
                            ] ->
                            if string_mem local locals then locals
                            else local :: locals
                        | _ -> locals)
                      locals operands
                | FList (FSymbol ("fn" | "loop") :: _) -> locals
                | FList forms | FVector forms ->
                    List.fold_left collect locals forms
                | FMap pairs ->
                    List.fold_left
                      (fun locals (key, value) ->
                        collect (collect locals key) value)
                      locals pairs
                | _ -> locals
              in
              if materialize_open_equality then
                List.fold_left collect [] body_forms
              else []
            in
            let local_params =
              List.map
                (fun (local, ty) ->
                  if string_mem local equality_first_locals then
                    ( local,
                      Types.optional_seqable_constraint
                        (Types.dynamic_constraint TUnknown) ty )
                  else (local, ty))
                local_params
            in
                match infer_all (local_params @ params) body_forms with
            | Error _ as error -> error
                | Ok inferred -> (
                let rec recur_arguments = function
                  | FList (FSymbol "recur" :: args) -> [ args ]
                  | FList (FSymbol ("loop" | "fn") :: _) -> []
                  | FList (FSymbol let_name :: bindings :: body)
                    when let_name = "let"
                         || String.ends_with ~suffix:"/let" let_name ->
                      (* Recur arguments must retain the locals in scope at the call. *)
                      List.concat_map recur_arguments body
                      |> List.map (List.map (fun arg ->
                             FList [ FSymbol let_name; bindings; arg ]))
                  | FList forms | FVector forms ->
                      List.concat_map recur_arguments forms
                  | FMap pairs ->
                      pairs
                      |> List.concat_map (fun (key, value) ->
                             recur_arguments key @ recur_arguments value)
                  | _ -> []
                in
                let constrain_recur params args =
                  match (local_params, args) with
                      | locals, args when List.length locals = List.length args
                        ->
                      List.fold_left2
                        (fun result (local, _) arg ->
                          Result.bind result (fun params ->
                              let expected =
                                string_assoc_opt local params
                                |> Option.value ~default:TUnknown
                              in
                              Result.bind
                                (infer_expected expected params arg)
                                (fun params ->
                                  let actual =
                                    match arg with
                                    | FList (FSymbol name :: args) -> (
                                        match lookup_function_ty name with
                                        | Ok (TFn (param_tys, return_ty))
                                          when List.length param_tys
                                               = List.length args ->
                                            Types.instantiate_type
                                              ~templates:param_tys
                                              ~actuals:
                                                (List.map
                                                       (inferred_form_type
                                                          params)
                                                   args)
                                              return_ty
                                            | _ -> inferred_form_type params arg
                                            )
                                    | arg -> inferred_form_type params arg
                                  in
                                  constrain_symbol actual params local)))
                        (Ok params) locals args
                  | _ -> Ok params
                in
                let inferred =
                  body_forms
                  |> List.concat_map recur_arguments
                  |> List.fold_left
                       (fun result args ->
                         Result.bind result (fun params ->
                             constrain_recur params args))
                       (Ok inferred)
                in
                    match inferred with
                | Error _ as error -> error
                | Ok inferred ->
                let original_names = List.map fst params in
                let originals =
                  original_names
                  |> List.map (fun name ->
                         ( name,
                           string_assoc_opt name inferred
                           |> Option.value
                                ~default:
                                  (string_assoc_opt name params
                                  |> Option.value ~default:TUnknown) ))
                in
                bindings
                |> List.fold_left
                     (fun result (local, value) ->
                       match (result, value) with
                       | (Error _ as error), _ -> error
                       | ( Ok params,
                           FList
                             [
                               FSymbol field_access;
                               FSymbol receiver;
                             ] )
                         when String.starts_with ~prefix:".-" field_access
                              && string_mem_assoc receiver params ->
                           let expected =
                             string_assoc_opt local inferred
                             |> Option.value ~default:TUnknown
                           in
                           let keyword =
                             ":"
                             ^ String.sub field_access 2
                                 (String.length field_access - 2)
                           in
                           (match expected with
                           | TUnknown | TMeta _ | TVar _ -> Ok params
                           | _ ->
                               add_record_field_constraint receiver keyword
                                 expected params)
                       | Ok params, FSymbol source
                         when string_mem_assoc source params ->
                           let local_ty =
                             string_assoc_opt local inferred
                             |> Option.value ~default:TUnknown
                           in
                           constrain_symbol local_ty params source
                       | ( Ok params,
                           FList
                             [
                               FSymbol
                                 ("__lg_seq" | "__lg_rest" | "__lg_next");
                               FSymbol source;
                             ] )
                         when string_mem_assoc source params ->
                           let local_ty =
                             string_assoc_opt local inferred
                             |> Option.value ~default:TUnknown
                           in
                           let element_ty =
                             match local_ty with
                             | ty when Types.is_dynamic ty -> Some ty
                             | TSeq inner | TList inner | TVector inner
                             | TArray inner | TSet inner ->
                                 Some inner
                             | TOcaml_app (("Seq.t" | "Seq"), [ inner ]) ->
                                 Some inner
                             | ty -> Types.seqable_constraint_element ty
                           in
                           Option.fold ~none:(Ok params)
                             ~some:(fun element_ty ->
                               constrain_seqable element_ty params source)
                             element_ty
                     | Ok params, _ -> Ok params)
                     (Ok originals))))
    | FList (FSymbol let_name :: bindings :: body_forms)
      when let_name = "let" || let_name = "let*"
           || String.ends_with ~suffix:"/let" let_name
           || String.ends_with ~suffix:"/let*" let_name ->
        let bindings =
          match bindings with
          | FVector forms ->
              FVector (Destructure.normalize_binding_type_hints forms)
          | bindings -> bindings
        in
        Result.bind (infer_let params bindings body_forms) (fun params ->
            let rec parse_aliases aliases = function
              | [] -> aliases
              | FSymbol name :: value :: rest ->
                  parse_aliases ((name, value) :: aliases) rest
              | _ :: _ :: rest -> parse_aliases aliases rest
              | [ _ ] -> aliases
            in
            let aliases =
              match bindings with
              | FVector forms -> parse_aliases [] forms
              | _ -> []
            in
            let body_aliases =
              List.filter
                (fun (name, _) ->
                  match
                    rewrite_simple_aliases aliases (FSymbol name)
                  with
                  | FSymbol source -> not (string_mem_assoc source params)
                  | FKeyword _ -> true
                  | _ -> false)
                aliases
            in
            let rewritten_body_forms =
              List.map (rewrite_simple_aliases body_aliases) body_forms
            in
            let rec infer_alias_constraints params = function
              | FList
                  (FSymbol apply_name :: FSymbol function_name :: arguments)
                when apply_name = "__lg_apply" -> (
                  match string_assoc_opt function_name aliases with
                  | Some function_form ->
                      infer_form params
                        (FList
                           (FSymbol apply_name :: function_form :: arguments))
                  | None -> Ok params)
              | FList [ FSymbol reduce_name; reducer; init; FSymbol collection ]
                when reduce_name = "__lg_reduce" -> (
                  match string_assoc_opt collection aliases with
                  | Some value ->
                      infer_form params
                        (FList [ FSymbol reduce_name; reducer; init; value ])
                  | None -> Ok params)
              | FList forms | FVector forms ->
                  List.fold_left
                    (fun result form ->
                      Result.bind result (fun params ->
                          infer_alias_constraints params form))
                    (Ok params) forms
              | FMap pairs ->
                  List.fold_left
                    (fun result (key, value) ->
                      Result.bind result (fun params ->
                          Result.bind (infer_alias_constraints params key)
                            (fun params -> infer_alias_constraints params value)))
                    (Ok params) pairs
              | _ -> Ok params
            in
            let binding_values =
              match bindings with
              | FVector forms ->
                  forms
                  |> List.mapi (fun index form -> (index, form))
                  |> List.filter_map (fun (index, form) ->
                      if index mod 2 = 1 then Some form else None)
              | _ -> []
            in
            Result.bind
              (if rewritten_body_forms = body_forms then Ok params
               else infer_all params rewritten_body_forms)
              (fun params ->
                List.fold_left
                  (fun result form ->
                    Result.bind result (fun params ->
                        infer_alias_constraints params form))
                  (Ok params)
                  (binding_values @ rewritten_body_forms)))
    | FList
        (FSymbol "fn" :: FSymbol _function_name
        :: (FVector _ as fn_params) :: body_forms) ->
        infer_form params (FList (FSymbol "fn" :: fn_params :: body_forms))
    | FList (FSymbol "fn" :: (FVector _ as fn_params) :: body_forms) -> (
        match Destructure.parse_param_specs fn_params with
        | Error _ -> infer_all params body_forms
        | Ok specs ->
            let local_bindings =
              specs
              |> List.concat_map (fun (spec : Destructure.param_spec) ->
                     let source_ty =
                       Option.value spec.explicit_ty ~default:TUnknown
                       |> resolve_named_record
                     in
                     let destructured =
                       if spec.destructured then
                         Destructure.pattern_names spec.pattern
                         |> List.map (fun name -> (name, TUnknown))
                       else []
                     in
                     (spec.source_name, source_ty) :: destructured)
            in
            let local_names = List.map fst local_bindings in
            let shadowed =
              params
              |> List.filter (fun (name, _) -> string_mem name local_names)
            in
            let local_params =
              local_bindings
              @ List.filter
                  (fun (name, _) -> not (string_mem name local_names))
                  params
            in
            let state params =
              (List.map fst params,
               Type_solver.canonical (TTuple (List.map snd params))) in
            let rec infer_local seen local_params =
              Result.bind (infer_all local_params body_forms) (fun inferred ->
                  let inferred =
                    restore_explicit_parameter_types ~resolve_named_record specs
                      inferred
                  in
                  if equal_parameters local_params inferred then Ok inferred else
                  let current = state local_params and next = state inferred in
                  if current = next then Ok inferred
                  else if List.mem next seen then
                    Error.error "local parameter type constraints do not converge"
                  else infer_local (current :: seen) inferred)
            in
            Result.map
              (fun inferred ->
                shadowed
                @ List.filter
                    (fun (name, _) -> not (string_mem name local_names))
                    inferred)
              (infer_local [] local_params))
    | FList [ FSymbol "__lg_into"; target; source ] ->
        Result.bind (infer_form params target) (fun params ->
            let element_ty =
              inferred_binding_form_type params target
              |> into_source_element_type
              |> Option.value ~default:TUnknown
            in
            infer_sequence_form element_ty params source)
    | FList
        [
          FSymbol "__lg_into";
          target;
          transducer;
          source;
        ] ->
        infer_all params
          [ target; FList [ FSymbol "sequence"; transducer; source ] ]
    | FList
        (FSymbol "__lg_interleave" :: collections) ->
        let element_ty =
          collections
          |> List.find_map (fun collection ->
                 let element_ty =
                   inferred_form_type params collection
                   |> Types.next_seq_element
                 in
                 match element_ty with
                 | Some (TUnknown | TMeta _ | TVar _) | None -> None
                 | Some element_ty -> Some element_ty)
          |> Option.value ~default:(Type_solver.fresh ())
        in
        List.fold_left
          (fun result collection ->
            Result.bind result (fun params ->
                match collection with
                | FSymbol name -> constrain_seqable element_ty params name
                | collection -> infer_sequence_form element_ty params collection))
          (Ok params) collections
    | FList (FList [ FKeyword keyword; FSymbol receiver ] :: arguments) -> (
        let infer_unknown_field () =
          let parameter_tys =
            List.mapi
              (fun index argument ->
                match inferred_form_type params argument with
                | TUnknown ->
                    fresh_type_variable
                      ("field_call_" ^ Names.sanitize_name receiver ^ "_"
                     ^ string_of_int index)
                | ty -> ty)
              arguments
          in
          Result.bind
            (add_record_field_constraint receiver keyword
               (TFn (parameter_tys, TUnknown)) params)
            (fun params ->
              List.fold_left2
                (fun result expected argument ->
                  Result.bind result (fun params ->
                      infer_expected expected params argument))
                (Ok params) parameter_tys arguments)
        in
        match
          match string_assoc_opt receiver params with
          | None -> None
          | Some ty -> Types.record_fields ty
        with
        | None -> infer_unknown_field ()
        | Some fields -> (
            match Types.find_field keyword fields with
            | Some { ty = TFn (parameter_tys, _); _ }
              when List.length parameter_tys = List.length arguments ->
                let rec infer_arguments params expected actual =
                  match (expected, actual) with
                  | [], [] -> Ok params
                  | expected_ty :: expected, argument :: actual ->
                      Result.bind (infer_expected expected_ty params argument)
                        (fun params -> infer_arguments params expected actual)
                  | _ -> assert false
                in
                infer_arguments params parameter_tys arguments
            | _ -> infer_unknown_field ()))
    | FList (FSymbol name :: args) ->
        Option.iter
          (fun observe ->
            observe name args (List.map (inferred_form_type params) args))
          observe_call;
        infer_known_call name params args
    | FVector forms -> infer_all params forms
    | FMap pairs ->
        if
          List.exists
            (fun (key, _value) ->
              match key with FKeyword _ -> false | _ -> true)
            pairs
        then
          pairs
          |> List.fold_left
               (fun result (key, value) ->
                 Result.bind result (fun params ->
                     Result.bind (infer_form params key) (fun params ->
                         infer_form params value)))
               (Ok params)
        else
          pairs
          |> List.fold_left
               (fun result (_key, value) ->
                 Result.bind result (fun params -> infer_form params value))
               (Ok params)
    | FList ((FList _ as callee) :: arguments) ->
        Result.bind (infer_form params callee) (fun params ->
            let callee_ty =
              inferred_form_or_call_type ~lookup_function_ty params callee
              |> Expression_support.clj_function_type
            in
            let signature =
              match callee_ty with
              | TFn (parameter_tys, _) when List.length parameter_tys = List.length arguments ->
                  Some callee_ty
              | TUnknown | TMeta _ | TVar _ ->
                  Some (TFn (List.map (fun argument ->
                      match inferred_form_or_call_type ~lookup_function_ty params argument with
                      | TUnknown -> Type_solver.fresh ()
                      | ty -> ty) arguments, Type_solver.fresh ()))
              | _ -> None
            in
            match signature with
            | Some (TFn (parameter_tys, _) as signature) ->
                Result.bind (infer_expected signature params callee) (fun params ->
                    List.fold_left2
                      (fun result expected argument ->
                        Result.bind result (fun params -> infer_expected expected params argument))
                      (Ok params) parameter_tys arguments)
            | _ -> infer_all params arguments)
    | FList forms -> infer_all params forms
    | FInt _ | FFloat _ | FDecimal _ | FChar _ | FString _ | FRegex _ | FBool _
    | FKeyword _
    | FSymbol _ | FCoreSymbol _ ->
        Ok params
  in
  let rec propagate_record_ref_writes params = function
    | FList
        [
          FSymbol ("IVolatile/-vreset!" | "IReset/-reset!");
          FList [ FKeyword keyword; FSymbol receiver ];
          FList [ FSymbol "Some"; FSymbol value ];
        ]
      when string_mem_assoc receiver params && string_mem_assoc value params -> (
        match record_ref_field_value_type params receiver keyword with
        | Some (TNullable payload_ty | TOcaml_app ("option", [ payload_ty ])) ->
            constrain_symbol payload_ty params value
        | Some _ | None -> Ok params)
    | FList
        [
          FSymbol "__deftype-field-set!";
          FKeyword keyword;
          FSymbol receiver;
          FList [ FSymbol "Some"; FSymbol value ];
        ]
      when string_mem_assoc receiver params && string_mem_assoc value params -> (
        match record_mutable_field_value_type params receiver keyword with
        | Some (TNullable payload_ty | TOcaml_app ("option", [ payload_ty ])) ->
            constrain_symbol payload_ty params value
        | Some _ | None -> Ok params)
    | FList (FSymbol ("fn" | "let" | "let*" | "loop") :: _) -> Ok params
    | FList forms | FVector forms ->
        List.fold_left
          (fun result form ->
            Result.bind result (fun params ->
                propagate_record_ref_writes params form))
          (Ok params) forms
    | FMap pairs ->
        List.fold_left
          (fun result (key, value) ->
            Result.bind result (fun params ->
                Result.bind (propagate_record_ref_writes params key)
                  (fun params -> propagate_record_ref_writes params value)))
          (Ok params) pairs
    | FInt _ | FFloat _ | FDecimal _ | FChar _ | FString _ | FRegex _ | FBool _
    | FKeyword _
    | FSymbol _ | FCoreSymbol _ ->
        Ok params
  in
  let state params =
    (List.map fst params, Type_solver.canonical (TTuple (List.map snd params))) in
  let rec stabilize seen params =
    branch_hint_symbols := [];
    let infer_body =
      match (expected_return_ty, List.rev body_forms) with
      | Some expected, result :: reversed_prefix ->
          Result.bind
            (infer_all params (List.rev reversed_prefix))
            (fun params -> infer_expected expected params result)
      | Some _, [] | None, _ -> infer_all params body_forms
    in
    Result.bind infer_body (fun inferred ->
        Result.bind
          (List.fold_left
             (fun result form ->
               Result.bind result (fun inferred ->
                   propagate_record_ref_writes inferred form))
             (Ok inferred) body_forms)
          (fun inferred ->
        let inferred =
          List.map
            (fun (name, ty) -> (name, deduplicate_protocol_constraints ty))
            inferred
        in
        if equal_parameters params inferred then Ok inferred else
        let current = state params and next = state inferred in
        if current = next then Ok inferred
        else if List.mem next seen then
          Error.error "parameter type constraints do not converge"
        else stabilize (current :: seen) inferred))
  in
  Result.map
    (fun inferred ->
      let names, types = List.split inferred in
      match (Type_solver.generalize (TTuple types)).body with
      | TTuple generalized -> List.combine names generalized
      | _ -> assert false)
    (Result.bind
       (infer_record_constraints_all
          (constrain_maybe_reduced_callbacks params body_forms) body_forms)
       (stabilize []))
