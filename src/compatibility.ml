open Types

let static_seqable_element_type ty =
  match Types.constraint_value_type ty with
  | TList element_ty | TVector element_ty | TSet element_ty | TSeq element_ty
  | TArray element_ty ->
      Some element_ty
  | value_ty -> Types.seqable_constraint_element value_ty

let is_optional_type = function
  | TNullable _ | TOcaml_app ("option", [ _ ]) -> true
  | _ -> false

let optional_payload = function
  | TNullable ty | TOcaml_app ("option", [ ty ]) -> Some ty
  | _ -> None

let is_truthy_constraint ty = Option.is_some (Types.truthy_constraint_info ty)

let overloaded_arity_parameters (arity : fn_arity) argument_count =
  let fixed_count = List.length arity.fixed_params in
  if argument_count < fixed_count then None
  else
    match arity.rest_param with
    | None ->
        if argument_count = fixed_count then Some arity.fixed_params else None
    | Some rest_ty ->
        Some
          (arity.fixed_params
      @ List.init (argument_count - fixed_count) (fun _ -> rest_ty))

let every_function_type = function
  | TFn ([ TFn ([ _ ], truthy); seqable ], TBool)
    when Option.is_some (Types.truthy_constraint_info truthy)
         && Option.is_some (Types.seqable_constraint_info seqable) ->
      true
  | _ -> false

let is_edn_value_type = Edn_value_elaborator.is_value_type

let edn_compatible_static_type = Types.edn_compatible_static_type

let expects_dynamic_value = Types.is_dynamic

let rec callback_type_compatible expected actual =
  Types.assignable ~policy:Host_boundary ~expected ~actual
  || Result.is_ok (Type_solver.unify Type_solver.empty expected actual)
  ||
  (match (expected, actual) with
   | TNamed_record expected_record, TNamed_record actual_record
     when not (String.equal expected_record.type_name actual_record.type_name) ->
       false
   | _, _ -> (
   match (Types.record_fields expected, Types.record_fields actual) with
   | Some expected_fields, Some actual_fields ->
       List.for_all
         (fun (actual_field : field) ->
           match find_field actual_field.keyword expected_fields with
           | Some expected_field ->
               callback_type_compatible expected_field.ty actual_field.ty
           | None -> false)
         actual_fields
   | _ -> false))
  ||
  match Types.capability_constraint_value actual with
  | Some value_ty -> callback_type_compatible expected value_ty
  | None -> (
      match (expected, actual) with
      | TFn (expected_params, expected_return),
        TFn (actual_params, actual_return) ->
          callback_parameters_compatible expected_params actual_params
          && callback_type_compatible expected_return actual_return
      | TOverloaded_fn expected_arities, TOverloaded_fn actual_arities ->
          List.for_all
            (fun (expected_arity : fn_arity) ->
              List.exists
                (fun (actual_arity : fn_arity) ->
                  List.length expected_arity.fixed_params
                  = List.length actual_arity.fixed_params
                  && Option.is_some expected_arity.rest_param
                     = Option.is_some actual_arity.rest_param
                  && callback_parameters_compatible expected_arity.fixed_params
                       actual_arity.fixed_params
                  && callback_type_compatible expected_arity.return_ty
                       actual_arity.return_ty
                  &&
                  match
                    (expected_arity.rest_param, actual_arity.rest_param)
                  with
                  | Some expected, Some actual ->
                      callback_type_compatible expected actual
                  | None, None -> true
                  | Some _, None | None, Some _ -> false)
                actual_arities)
            expected_arities
      | _ -> false)

and callback_parameters_compatible expected actual =
  List.length expected = List.length actual
  && List.for_all2 callback_type_compatible expected actual

let rec argument_compatible expected actual =
  if Types.is_dynamic expected then true
  else if is_edn_value_type expected then
    is_edn_value_type actual || edn_compatible_static_type actual
  else if Option.is_some (Types.protocol_constraint_info expected) then true
  else if Option.is_some (Types.truthy_constraint_info expected) then true
  else if Option.is_some (Types.nil_predicate_constraint_info expected) then
    true
  else if Option.is_some (Types.printable_constraint_info expected) then true
  else if Option.is_some (Types.exception_data_constraint_info expected) then
    true
  else if Option.is_some (Types.hashable_constraint_info expected) then true
  else if Option.is_some (Types.comparable_constraint_info expected) then true
  else if Option.is_some (Types.array_index_constraint_info expected) then true
  else if Option.is_some (Types.symbol_predicate_constraint_info expected) then
    true
  else if Option.is_some (Types.contains_constraint_info expected) then
    Collection_capability.accepts_contains actual
  else if Option.is_some (Types.nil_predicate_constraint_info actual) then
    argument_compatible expected
      (Option.get (Types.nil_predicate_constraint_info actual))
  else if Option.is_some (Types.seqable_constraint_info expected) then
    match (Types.seqable_constraint_info expected, actual) with
    | Some ((`Optional | `Optional_sequential), _, _), TNil -> true
    | _, (TNullable actual | TOcaml_app ("option", [ actual ])) ->
        argument_compatible expected actual
    | Some (_, expected_element, _),
      (TList actual_element | TVector actual_element | TSet actual_element
      | TSeq actual_element | TArray actual_element) ->
        Type_solver.is_open expected_element
        || Type_solver.is_open actual_element
        || argument_compatible expected_element actual_element
    | Some (_, expected_element, _), TString ->
        Type_solver.is_open expected_element
        || argument_compatible expected_element TChar
    | _, actual when is_edn_value_type actual -> true
    | _, ty when Types.is_dynamic ty -> true
    | Some (_, expected_element, _), actual -> (
        match Types.seqable_constraint_info actual with
        | Some (_, actual_element, _) ->
            Type_solver.is_open expected_element
            || Type_solver.is_open actual_element
            || argument_compatible expected_element actual_element
        | None -> false)
    | None, _ -> false
  else
    match (expected, actual) with
    | TPoly_variant expected, TPoly_variant actual ->
        Variant_row.compatible_payloads argument_compatible expected actual
    | (TNullable _ | TOcaml_app ("option", [ _ ])), TNil -> true
    | ( (TNullable expected | TOcaml_app ("option", [ expected ])),
        (TNullable actual | TOcaml_app ("option", [ actual ])) ) ->
        argument_compatible expected actual
    | (TNullable expected | TOcaml_app ("option", [ expected ])), actual ->
        argument_compatible expected actual
    | TFloat, TInt -> true
    | TUnit, TNil -> true
    | TOcaml "int", TInt | TInt, TOcaml "int" -> true
    | expected, actual
      when
        let value_ty = Types.constraint_value_type actual in
        not (Types.equal value_ty actual)
        && argument_compatible expected value_ty ->
        true
    | TFn ([ TUnit ], expected_return), TFn ([], actual_return)
    | TFn ([], expected_return), TFn ([ TUnit ], actual_return) ->
        argument_compatible expected_return actual_return
    | expected, (TNullable actual | TOcaml_app ("option", [ actual ]))
      when (match expected with
           | TRecord _ | TNamed_record _ | TArray _
           | TOcaml_app ("array", [ _ ]) ->
               true
           | _ -> false)
           && argument_compatible expected actual ->
        true
    | TNamed_record _, TRecord _
      when Types.assignable ~policy:Host_boundary ~expected ~actual ->
        true
    | TNamed_record expected_record, TNamed_record actual_record
      when expected_record.type_name = actual_record.type_name ->
        Types.assignable ~policy:Host_boundary ~expected ~actual
    | (TRecord _ | TNamed_record { nominal = false; _ }), actual
      when Option.is_some (Types.contains_constraint_info actual)
           || Option.is_some (Types.dynamic_map_types actual) ->
        true
    | ( (TRecord expected_fields | TNamed_record { fields = expected_fields; _ }),
        (TRecord actual_fields | TNamed_record { fields = actual_fields; _ }) )
      ->
        List.for_all
          (fun (expected : field) ->
            match find_field expected.keyword actual_fields with
            | Some actual -> argument_compatible expected.ty actual.ty
            | None ->
                Types.is_record_extension_field expected
                || is_optional_type expected.ty
                || is_truthy_constraint expected.ty)
          expected_fields
    | expected_map,
      (TRecord actual_fields | TNamed_record { fields = actual_fields; _ })
      when Option.is_some (Types.dynamic_map_types expected_map)
           && Types.is_homogeneous_record actual_fields ->
        let expected_key, expected_value =
          Option.get (Types.dynamic_map_types expected_map)
        in
        let actual_value =
          Types.homogeneous_record_value_type actual_fields |> Option.get
        in
        argument_compatible expected_key TKeyword
        && argument_compatible expected_value actual_value
    | expected_map, actual
      when Option.is_some (Types.dynamic_map_types expected_map)
           && not (Types.equal actual (Types.constraint_value_type actual)) ->
        argument_compatible expected_map (Types.constraint_value_type actual)
    | expected_map, actual_map
      when Option.is_some (Types.dynamic_map_types expected_map) -> (
        match actual_map with
        | TUnknown | TMeta _ | TVar _ -> true
        | actual_map -> (
            match Types.dynamic_map_types actual_map with
            | Some (actual_key, actual_value) ->
                let expected_key, expected_value =
                  Option.get (Types.dynamic_map_types expected_map)
                in
                argument_compatible expected_key actual_key
                && argument_compatible expected_value actual_value
            | None -> false))
    | TList expected_element, TList actual_element
    | TVector expected_element, TVector actual_element
    | TArray expected_element, TArray actual_element
    | TSeq expected_element, TSeq actual_element
    | TSet expected_element, TSet actual_element ->
        argument_compatible expected_element actual_element
    | _ when Types.assignable ~policy:Host_boundary ~expected ~actual -> true
    | TFn (expected_params, expected_return), TFn (actual_params, actual_return)
      when callback_parameters_compatible expected_params actual_params -> (
        if
          Types.equal expected_return TBool
          && expects_dynamic_value actual_return
        then true
        else if
          argument_compatible expected_return actual_return
          || callback_type_compatible expected_return actual_return
        then true
        else
        match Types.maybe_reduced_callback_element expected_return with
        | Some expected_inner -> (
            match Types.reduced_element actual_return with
            | Some actual_inner ->
                  Types.assignable ~policy:Host_boundary
                    ~expected:expected_inner ~actual:actual_inner
            | None ->
                  Types.assignable ~policy:Host_boundary
                    ~expected:expected_inner ~actual:actual_return)
        | None -> false)
    | TFn (expected_params, _) as expected_fn, TOverloaded_fn arities ->
        List.exists
          (fun arity ->
            match
              overloaded_arity_parameters arity (List.length expected_params)
            with
            | None -> false
            | Some actual_params ->
                argument_compatible expected_fn
                  (TFn (actual_params, arity.return_ty)))
          arities
    | TOverloaded_fn expected_arities, (TFn _ as actual_fn) ->
        let function_type (arity : fn_arity) =
          let parameters =
            match arity.rest_param with
            | None -> arity.fixed_params
            | Some rest_ty -> arity.fixed_params @ [ TSeq rest_ty ]
          in
          TFn (parameters, arity.return_ty)
        in
        let parameter_compatible expected actual =
          argument_compatible expected actual
          || Result.is_ok (Type_solver.unify Type_solver.empty actual expected)
          || Result.is_ok (Type_solver.unify Type_solver.empty expected actual)
          ||
          (match (expected, actual) with
          | TSet expected_element, TFn ([ actual_element ], actual_return) ->
              argument_compatible actual_element expected_element
              && (Types.equal actual_return TBool
                 || Option.is_some (Types.truthy_constraint_info actual_return)
                 || Option.is_some (optional_payload actual_return))
          | _ -> false)
          ||
          match
            ( static_seqable_element_type expected,
              Types.seqable_constraint_info actual )
          with
          | Some expected_element, Some (_, actual_element, _) ->
              argument_compatible actual_element expected_element
          | _ -> false
        in
        let generic_function_compatible expected_fn =
          match (expected_fn, actual_fn) with
          | ( TFn (expected_params, expected_return),
              TFn (actual_params, actual_return) )
            when List.length expected_params = List.length actual_params ->
              (List.for_all2 parameter_compatible expected_params actual_params
              && argument_compatible expected_return actual_return)
              ||
              (every_function_type actual_fn
              &&
              match (expected_params, actual_params) with
              | [ _predicate_ty; collection_ty ], [ _; _ ]
                when Types.equal collection_ty TNil
                     || (match collection_ty with
                        | TUnknown | TMeta _ | TVar _ -> true
                        | _ -> false)
                     || Option.is_some
                          (static_seqable_element_type collection_ty) ->
                  argument_compatible expected_return TBool
              | _ -> false)
          | _ -> argument_compatible expected_fn actual_fn
        in
        List.for_all
          (fun expected -> generic_function_compatible (function_type expected))
          expected_arities
    | TOverloaded_fn expected_arities, TOverloaded_fn actual_arities ->
        let function_type (arity : fn_arity) =
          let parameters =
            match arity.rest_param with
            | None -> arity.fixed_params
            | Some rest_ty -> arity.fixed_params @ [ TSeq rest_ty ]
          in
          TFn (parameters, arity.return_ty)
        in
        List.for_all
          (fun (expected : fn_arity) ->
            actual_arities
            |> List.find_opt (fun (actual : fn_arity) ->
                   List.length actual.fixed_params
                   = List.length expected.fixed_params
                   && Option.is_some actual.rest_param
                      = Option.is_some expected.rest_param)
            |> Option.fold ~none:false ~some:(fun actual ->
                   argument_compatible (function_type expected)
                     (function_type actual)))
          expected_arities
    | _ -> false

let named_argument_compatible expected actual =
  argument_compatible expected actual
  ||
  ((match expected with
   | TInt | TFloat | TChar | TString | TBool | TKeyword | TSymbol -> true
   | _ -> false)
  && Option.is_none (optional_payload expected)
  && Option.fold ~none:false ~some:(argument_compatible expected)
       (optional_payload actual))

let sequence_argument_compatible expected actual =
  let element_type = function
    | TSeq element | TList element | TVector element | TSet element
    | TArray element ->
        Some element
    | ty -> Types.next_seq_element ty
  in
  let expects_sequence =
    match expected with
    | TSeq _ -> true
    | ty -> Option.is_some (Types.next_seq_element ty)
  in
  let requires_representation_conversion =
    match actual with
    | TList _ | TVector _ | TSet _ | TArray _ -> true
    | _ -> false
  in
  let compatible =
    expects_sequence && requires_representation_conversion
    &&
    match (element_type expected, element_type actual) with
    | Some expected_element, Some actual_element ->
        Types.assignable ~policy:Host_boundary ~expected:expected_element
          ~actual:actual_element
    | _ -> false
  in
  compatible

let rec row_argument_compatible expected_fields actual_ty =
  match actual_ty with
  | ty when Types.is_dynamic ty -> true
  | TNullable actual_ty | TOcaml_app ("option", [ actual_ty ]) ->
      row_argument_compatible expected_fields actual_ty
  | TRecord actual_fields | TNamed_record { fields = actual_fields; _ } ->
      List.for_all
        (fun (expected : field) ->
          if Types.is_record_extension_field expected then true
          else
            match find_field expected.keyword actual_fields with
            | None -> is_optional_type expected.ty
            | Some actual ->
                Types.assignable ~policy:Host_boundary ~expected:expected.ty
                  ~actual:actual.ty)
        expected_fields
  | TNil -> true
  | _ -> false
