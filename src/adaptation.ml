open Semantic_type

type protocol_witness = {
  protocol_id : Protocol_id.t;
  expected : ty;
  source_ty : ty;
  implementation_available : bool;
}

type numeric_conversion = Int_to_float

type sequence_representation_source =
  | List_source
  | Vector_source
  | Sequence_source

type t =
  | Identity
  | Numeric_conversion of numeric_conversion
  | Host_int_boundary
  | Metadata_boundary
  | Symbol_string_boundary
  | Unit_after_effect
  | Tuple_elements of t list
  | Variant_payloads of (string * (ty * t) option) list
  | Tuple_to_vector of tuple_to_vector
  | Nullable of t
  | Optional_map of t
  | Result_map of t * t
  | Option_boundary of t
  | Optional_unwrap of t
  | Optional_payload of t
  | Protocol_storage_passthrough
  | Capability_payload of t
  | Nullable_none
  | Row_projection of row_projection
  | Structural_projection of structural_projection
  | Protocol_witness of protocol_witness
  | Sequence_witness of sequence_witness
  | Callback of callback
  | Constrained_result_callback of constrained_result_callback
  | Constant_function of constant_function
  | Map_callable of map_callable
  | Record_callable of record_callable
  | Set_callable of set_callable
  | Overload_to_variadic of overload_to_variadic
  | Overload of overload
  | Function_overload of function_overload
  | Overloaded_callback of overloaded_callback
  | Reduced_callback of reduced_callback
  | Sequence_representation of sequence_representation
  | Vector_from_sequence of sequence_representation
  | Collection_representation of collection_representation
  | Map_representation of map_representation
  | Record_to_map of record_to_map
  | Capability_witness of capability_witness

and sequence_witness = {
  requirement : seqable_requirement;
  expected_element : ty;
  storage_ty : ty;
  source_ty : ty;
  row_type_name : string option;
  element_adaptation : (ty * t) option;
}

and callback = {
  expected_params : ty list;
  actual_params : ty list;
  actual_return : ty;
  argument_adaptations : t list;
  result_adaptation : t;
}

and constrained_result_callback = {
  expected_params : ty list;
  actual_params : ty list;
  expected_return : ty;
  actual_return : ty;
  argument_adaptations : t list;
}

and constant_function = {
  expected_params : ty list;
  actual_return : ty;
  result_adaptation : t;
}

and map_callable = {
  expected_key : ty;
  actual_key : ty;
  actual_value : ty;
  key_adaptation : t;
  result_adaptation : t option;
  truthy_result : bool;
}

and record_callable = {
  fields : field list;
  result_adaptations : t list;
  missing_adaptation : t option;
  truthy_result : bool;
}

and set_callable = { adaptation : t }

and overload_to_variadic = {
  expected_arity : fn_arity;
  actual_arities : fn_arity list;
}

and sequence_representation = {
  source : sequence_representation_source;
  expected_element : ty;
  actual_element : ty;
  element_adaptation : t;
}

and tuple_to_vector = {
  expected_element : ty;
  actual_elements : ty list;
  element_adaptations : t list;
}

and overload = { arities : overload_arity list }

and function_overload = {
  actual_params : ty list;
  actual_return : ty;
  arities : function_overload_arity list;
}

and overloaded_callback = {
  actual_index : int;
  actual_arity : fn_arity;
  expected_params : ty list;
  actual_params : ty list;
  actual_return : ty;
  argument_adaptations : t list;
  result_adaptation : t option;
  truthy_result : bool;
}

and reduced_callback = {
  expected_params : ty list;
  actual_params : ty list;
  actual_return : ty;
  argument_adaptations : t list;
  result_adaptation : t;
  actual_returns_reduced : bool;
}

and function_overload_arity =
  | Planned_function_arity of t
  | Fixed_to_variadic_arity of {
      expected : fn_arity;
      argument_adaptations : t list;
      result_adaptation : t;
    }
  | Every_special_arity of { expected_ty : ty }

and overload_arity = {
  actual_index : int;
  actual_ty : ty;
  adaptation : t;
}

and collection_kind =
  | List_collection
  | Vector_collection
  | Sequence_collection
  | Array_collection
  | Set_collection

and collection_representation = {
  kind : collection_kind;
  expected_element : ty;
  actual_element : ty;
  element_adaptation : t;
}

and map_representation = {
  expected_key : ty;
  actual_key : ty;
  actual_value : ty;
  key_adaptation : t;
  value_adaptation : t;
}

and record_to_map = {
  expected_key : ty;
  source_ty : ty;
  entries : record_map_entry list;
}

and record_map_entry = {
  field : field;
  key_adaptation : t;
  value_adaptation : t;
}

and capability_witness = {
  expected : ty;
  source_ty : ty;
}

and row_projection = {
  type_name : string;
  expected_fields : field list;
  source_ty : ty;
  field_plans : row_field_plan list;
}

and structural_projection = {
  expected_fields : field list;
  source_ty : ty;
  field_plans : row_field_plan list;
}

and row_field_plan =
  | Source_field of {
      expected : field;
      actual : field;
      adaptation : t;
    }
  | Missing_optional_field of field
  | Missing_constrained_field of {
      expected : field;
      adaptation : t;
    }
  | Missing_extension_field of {
      expected : field;
      adaptation : t;
    }

type error =
  | Missing_row_field of string
  | Incompatible_row_field of {
      keyword : string;
      expected : ty;
      actual : ty;
    }
  | Non_seqable of ty
  | Incompatible_types of {
      expected : ty;
      actual : ty;
    }

let optional_type = function
  | TNullable _ | TOcaml_app ("option", [ _ ]) -> true
  | _ -> false

let open_leaf = function TUnknown | TMeta _ | TVar _ -> true | _ -> false

let plan_row_projection ~plan_field type_name expected_fields actual =
  let source_ty = Types.constraint_value_type actual in
  match Types.record_fields source_ty with
  | None -> Error (Incompatible_types { expected = TRecord expected_fields; actual })
  | Some actual_fields ->
      let rec build field_plans = function
        | [] ->
            let field_plans = List.rev field_plans in
            Ok
              (match type_name with
              | Some type_name ->
                  Row_projection
                    { type_name; expected_fields; source_ty; field_plans }
              | None ->
                  Structural_projection
                    { expected_fields; source_ty; field_plans })
        | (expected : field) :: rest -> (
            match Types.find_field expected.keyword actual_fields with
            | Some actual_field ->
                (match plan_field expected.ty actual_field.ty with
                | Ok adaptation ->
                    build
                      (Source_field
                         { expected; actual = actual_field; adaptation }
                      :: field_plans)
                      rest
                | Error (Incompatible_types _) ->
                    Error
                      (Incompatible_row_field
                         {
                           keyword = expected.keyword;
                           expected = expected.ty;
                           actual = actual_field.ty;
                         })
                | Error error -> Error error)
            | None when optional_type expected.ty ->
                build (Missing_optional_field expected :: field_plans) rest
            | None when Types.is_record_extension_field expected ->
                Result.bind
                  (plan_field expected.ty source_ty)
                  (fun adaptation ->
                    build
                      (Missing_extension_field { expected; adaptation }
                      :: field_plans)
                      rest)
            | None when Option.is_some (Types.truthy_constraint_info expected.ty) ->
                Result.bind
                  (plan_field expected.ty TNil)
                  (fun adaptation ->
                    build
                      (Missing_constrained_field { expected; adaptation }
                      :: field_plans)
                      rest)
            | None -> Error (Missing_row_field expected.keyword))
      in
      build [] expected_fields

let nullable_payload = function
  | TNullable payload | TOcaml_app ("option", [ payload ]) -> Some payload
  | _ -> None

let sequence_representation_type_name name =
  Types.is_next_seq_type_name name || name = "Seq.t" || name = "Seq"

let sequence_element_type = function
  | TList element | TVector element | TSet element | TSeq element
  | TArray element ->
      Some element
  | TOcaml_app (name, [ element ])
    when sequence_representation_type_name name ->
      Some element
  | TString -> Some TChar
  | actual ->
      Option.map
        (fun (_, element, _) -> element)
        (Types.seqable_constraint_info actual)

let rec sequence_element_compatible ~sequence_satisfies ~element_adapts expected
    actual =
  match expected with
  | TNamed_record record when not record.nominal ->
      element_adapts expected actual
  | TRecord _ -> element_adapts expected actual
  | TConstraint
      (Seqable_constraint { requirement; element = expected_element; _ }) ->
      sequence_source_compatible ~sequence_satisfies ~element_adapts requirement
        expected_element actual
  | TConstraint (Protocol_constraint { value; _ })
    when Option.is_none (Types.capability_constraint_value actual) ->
      sequence_element_compatible ~sequence_satisfies ~element_adapts value actual
  | _ ->
      Type_solver.is_open expected
      || Type_solver.is_open actual
      || Types.assignable ~policy:Types.Host_boundary ~expected ~actual

and sequence_source_compatible ~sequence_satisfies ~element_adapts requirement
    expected_element actual =
  let rec compatible actual =
    if Types.is_dynamic actual || Type_solver.is_open actual then true
    else
      match actual with
      | TNil -> requirement <> Required
      | TNullable inner | TOcaml_app ("option", [ inner ]) -> compatible inner
      | actual -> (
          match sequence_element_type actual with
          | Some actual_element ->
              sequence_element_compatible ~sequence_satisfies ~element_adapts
                expected_element actual_element
          | None -> sequence_satisfies requirement actual)
  in
  compatible actual

let nested_non_seqable_element ~sequence_satisfies expected_element actual =
  let rec find expected actual =
    match expected with
    | TConstraint
        (Seqable_constraint { requirement; element = expected_element; _ }) ->
        if Types.is_dynamic actual then None
        else
          (match actual with
          | TNullable inner | TOcaml_app ("option", [ inner ]) ->
              find expected inner
          | TNil when requirement <> Required -> None
          | actual -> (
              match sequence_element_type actual with
              | None ->
                  if sequence_satisfies requirement actual then None
                  else Some actual
              | Some actual_element -> find expected_element actual_element))
    | _ -> None
  in
  match sequence_element_type actual with
  | Some actual_element -> find expected_element actual_element
  | None -> None

let identity_compatible expected actual =
  (* Recursive host aliases may revisit a pair while their variant rows are expanded. *)
  let rec compatible seen expected actual =
    Types.equal expected actual
    || List.exists (fun (left, right) -> Types.equal left expected && Types.equal right actual) seen
    ||
    let identity_compatible = compatible ((expected, actual) :: seen) in
    match (expected, actual) with
    | (TUnknown | TMeta _ | TVar _), (TUnknown | TMeta _ | TVar _) -> true
    | TOcaml expected, TOcaml actual ->
        Ocaml_signature.same_type_path expected actual
    | TPoly_variant _, TOcaml name -> (
        match Ocaml_signature.of_compiler_type
                (Lg_compiler_support.Ocaml_value.Constructor (name, [])) with
        | TPoly_variant _ as manifest -> identity_compatible expected manifest
        | _ -> false)
    | TOcaml name, TPoly_variant _ -> (
        match Ocaml_signature.of_compiler_type
                (Lg_compiler_support.Ocaml_value.Constructor (name, [])) with
        | TPoly_variant _ as manifest -> identity_compatible manifest actual
        | _ -> false)
    | TPoly_variant expected, TPoly_variant actual ->
        Variant_row.compatible_payloads identity_compatible expected actual
    | TNullable expected, TNullable actual
    | TArray expected, TArray actual
    | TRef expected, TRef actual
    | TList expected, TList actual
    | TVector expected, TVector actual
    | TSet expected, TSet actual
    | TSeq expected, TSeq actual ->
        identity_compatible expected actual
    | TNullable expected, TOcaml_app ("option", [ actual ])
    | TOcaml_app ("option", [ expected ]), TNullable actual ->
        identity_compatible expected actual
    | TOcaml_app (expected_name, expected_args),
      TOcaml_app (actual_name, actual_args)
      when Ocaml_signature.same_type_path expected_name actual_name
           && List.length expected_args = List.length actual_args ->
        List.for_all2
          (fun expected actual ->
            open_leaf expected || open_leaf actual
            || identity_compatible expected actual)
          expected_args actual_args
    | TTuple expected, TTuple actual
      when List.length expected = List.length actual ->
        List.for_all2 identity_compatible expected actual
    | TNamed_record expected, TNamed_record actual ->
        (Type_id.equal expected.type_id actual.type_id
         || (not (String.equal expected.type_name actual.type_name)
             && Ocaml_signature.same_type_path expected.type_name actual.type_name))
        && List.length expected.type_arguments = List.length actual.type_arguments
        && List.for_all2 identity_compatible expected.type_arguments
             actual.type_arguments
    | TNamed_record record, TOcaml_app (name, arguments)
    | TOcaml_app (name, arguments), TNamed_record record ->
        (Ocaml_signature.same_type_path name record.type_name
        || String.equal name (Type_id.name record.type_id))
        && List.length record.type_arguments = List.length arguments
        && List.for_all2 identity_compatible record.type_arguments arguments
    | TNamed_record record, TOcaml name | TOcaml name, TNamed_record record ->
        record.type_arguments = []
        && (Ocaml_signature.same_type_path name record.type_name
           || String.equal name (Type_id.name record.type_id))
    | _ -> false
  in
  compatible [] expected actual

let overload_covers_variadic_identity expected_arity actual_arities =
  (* An unresolved expected type (inference variable) accepts anything. *)
  let compatible_with expected actual =
    open_leaf expected || identity_compatible expected actual
  in
  match expected_arity.rest_param with
  | None -> false
  | Some expected_rest ->
      let compatible (actual : fn_arity) =
        List.for_all (compatible_with expected_rest) actual.fixed_params
        && Option.fold ~none:true
             ~some:(compatible_with expected_rest)
             actual.rest_param
        && compatible_with expected_arity.return_ty actual.return_ty
      in
      let variadic_fixed_count =
        actual_arities
        |> List.find_opt (fun arity ->
               Option.is_some arity.rest_param && compatible arity)
        |> Option.map (fun arity -> List.length arity.fixed_params)
      in
      Option.fold ~none:false
        ~some:(fun minimum ->
          List.for_all compatible actual_arities
          && List.init minimum Fun.id
             |> List.for_all (fun count ->
                    List.exists
                      (fun arity ->
                        Option.is_none arity.rest_param
                        && List.length arity.fixed_params = count)
                      actual_arities))
        variadic_fixed_count

let external_record_type = function
  | TOcaml type_name -> (
      match Ocaml_signature.record_type type_name with
      | Ok (TNamed_record _ as record) -> record
      | Ok _ | Error _ -> TOcaml type_name)
  | TOcaml_app (type_name, arguments) -> (
      match Ocaml_signature.record_type type_name with
      | Ok (TNamed_record record)
        when List.length record.type_parameters = List.length arguments ->
          let substitutions =
            List.combine record.type_parameters arguments
            |> List.map (fun (parameter, argument) ->
                   (Type_solver.Declared parameter, argument))
            |> Type_solver.of_list
          in
          Type_solver.apply substitutions (TNamed_record record)
      | Ok _ | Error _ -> TOcaml_app (type_name, arguments))
  | ty -> ty

let rec plan ?row_type_name ~row_type_name_for ~protocol_satisfies
    ~sequence_satisfies expected actual =
  let row_type_name =
    match (row_type_name, expected) with
    | Some _ as name, _ -> name
    | None, TRecord fields -> row_type_name_for fields
    | None, _ -> None
  in
  let actual = external_record_type actual in
  match expected with
  | TRecord _ when open_leaf (Types.constraint_value_type actual) -> Ok Identity
  | TRecord expected_fields -> (
      let project actual =
        plan_row_projection
          ~plan_field:(fun expected actual ->
            plan ~row_type_name_for ~protocol_satisfies ~sequence_satisfies
              expected actual)
          row_type_name expected_fields actual
      in
      match nullable_payload actual with
      | Some actual_payload ->
          Result.map (fun adaptation -> Optional_payload adaptation)
            (project actual_payload)
      | None -> project actual)
  | (TNamed_record _ as expected)
    when identity_compatible expected (Types.constraint_value_type actual) ->
      if Types.equal actual (Types.constraint_value_type actual) then Ok Identity
      else Ok (Capability_payload Identity)
  | TNamed_record _ when open_leaf (Types.constraint_value_type actual) ->
      Ok Identity
  | TNamed_record record when not record.nominal ->
      plan_row_projection
        ~plan_field:(fun expected actual ->
          plan ~row_type_name_for ~protocol_satisfies ~sequence_satisfies
            expected actual)
        (Some (Structural_map.record_type_application record)) record.fields
        actual
  | _ -> (
      match (expected, actual) with
      | TUnit, (TNil | TNullable TUnit | TOcaml_app ("option", [ TUnit ])) ->
          Ok Unit_after_effect
      | TNullable expected, TOcaml_app ("option", [ actual ])
      | TOcaml_app ("option", [ expected ]), TNullable actual ->
          Result.map
            (fun adaptation -> Option_boundary adaptation)
            (plan ?row_type_name ~row_type_name_for ~protocol_satisfies
               ~sequence_satisfies expected actual)
      | TOcaml_app ("result", [ expected_ok; expected_error ]),
        TOcaml_app ("result", [ actual_ok; actual_error ]) ->
          Result.bind
            (plan ~row_type_name_for ~protocol_satisfies ~sequence_satisfies expected_ok actual_ok)
            (fun success ->
              Result.map (fun error -> Result_map (success, error))
                (plan ~row_type_name_for ~protocol_satisfies ~sequence_satisfies expected_error actual_error))
      | TOcaml "int", TInt | TInt, TOcaml "int" -> Ok Host_int_boundary
      | expected, actual
        when Option.is_some (Types.reduced_element expected)
             && Option.is_some (Types.maybe_reduced_callback_element actual)
             && identity_compatible
                  (Types.reduced_element expected |> Option.get)
                  (Types.maybe_reduced_callback_element actual |> Option.get) ->
          Ok Identity
      | _ ->
      if Types.equal expected actual then Ok Identity
      else if
        (not (open_leaf expected)
        || not (open_leaf (Types.constraint_value_type actual))
        || Option.is_none (Types.truthy_constraint_info actual))
        &&
        (match expected with TConstraint _ -> false | _ -> true)
        && not (Types.equal actual (Types.constraint_value_type actual))
      then
        Result.map
          (fun adaptation -> Capability_payload adaptation)
          (plan ?row_type_name ~row_type_name_for ~protocol_satisfies
             ~sequence_satisfies expected (Types.constraint_value_type actual))
      else if identity_compatible expected actual then Ok Identity
      else if
        (open_leaf expected || open_leaf actual)
        &&
        match expected with
        | TConstraint
            (Exception_data_constraint _ | Protocol_constraint _) -> (
            (* Constrained values are stored as (witness, value) pairs; a
               raw open source cannot supply the witness, so this is not a
               plain identity. A source that is itself constrained already
               carries the pair representation. *)
            match actual with
            | TConstraint _ -> true
            | _ -> not (open_leaf actual))
        | _ -> true
      then Ok Identity
      else if
        Types.equal expected (TOcaml "Lg_edn_backend.t")
        && Types.edn_compatible_static_type actual
      then Ok Metadata_boundary
      else if
        (Types.equal expected TString && Types.equal actual TSymbol)
        || (Types.equal expected TSymbol && Types.equal actual TString)
      then Ok Symbol_string_boundary
      else if Types.equal expected TFloat && Types.equal actual TInt then
        Ok (Numeric_conversion Int_to_float)
      else
        match nullable_payload expected with
        | Some _ when Types.equal actual TNil -> Ok Nullable_none
        | Some expected_payload -> (
            match nullable_payload actual with
            | Some actual_payload ->
                Result.map
                  (fun adaptation -> Optional_map adaptation)
                  (plan ?row_type_name ~row_type_name_for ~protocol_satisfies
                     ~sequence_satisfies expected_payload actual_payload)
            | None ->
                Result.map
                  (fun adaptation -> Nullable adaptation)
                  (plan ?row_type_name ~row_type_name_for ~protocol_satisfies
                     ~sequence_satisfies expected_payload actual))
        | None -> (
            match (expected, actual) with
            | (TFn _ as expected_fn), TSet element_ty ->
                Result.map
                  (fun adaptation -> Set_callable { adaptation })
                  (plan ~row_type_name_for ~protocol_satisfies
                     ~sequence_satisfies expected_fn
                     (TFn ([ element_ty ], TNullable element_ty)))
            | TFn (expected_params, expected_return), actual
              when Option.is_some (Types.constant_function_result actual) ->
                let actual_return =
                  Types.constant_function_result actual |> Option.get
                in
                Result.map
                  (fun result_adaptation ->
                    Constant_function
                      {
                        expected_params;
                        actual_return;
                        result_adaptation;
                      })
                  (plan ~row_type_name_for ~protocol_satisfies
                     ~sequence_satisfies expected_return actual_return)
            | TFn ([ expected_key ], expected_return), actual
              when Option.is_some (Types.dynamic_map_types actual) ->
                let actual_key, actual_value =
                  Types.dynamic_map_types actual |> Option.get
                in
                Result.bind
                  (plan ~row_type_name_for ~protocol_satisfies
                     ~sequence_satisfies actual_key expected_key)
                  (fun key_adaptation ->
                    if Types.equal expected_return TBool then
                      Ok
                        (Map_callable
                           {
                             expected_key;
                             actual_key;
                             actual_value;
                             key_adaptation;
                             result_adaptation = None;
                             truthy_result = true;
                           })
                    else
                      Result.map
                        (fun result_adaptation ->
                          Map_callable
                            {
                              expected_key;
                              actual_key;
                              actual_value;
                              key_adaptation;
                              result_adaptation = Some result_adaptation;
                              truthy_result = false;
                            })
                        (plan ~row_type_name_for ~protocol_satisfies
                           ~sequence_satisfies expected_return
                           (TNullable actual_value)))
            | TFn (expected_params, expected_return),
              TFn (actual_params, actual_return)
              when (match expected_return with
                   | TConstraint (Open_boundary_constraint _) -> false
                   | TConstraint _ -> true
                   | _ -> false)
              ->
                plan_constrained_result_callback ~row_type_name_for
                  ~protocol_satisfies ~sequence_satisfies expected actual
                  expected_params expected_return actual_params actual_return
            | TFn (expected_params, expected_return),
              TFn (actual_params, actual_return)
              when Option.is_some
                     (match Types.maybe_reduced_callback_element expected_return with
                     | Some _ as result -> result
                     | None -> Types.reduced_element expected_return) ->
                plan_reduced_callback ~row_type_name_for ~protocol_satisfies
                  ~sequence_satisfies expected actual expected_params
                  expected_return actual_params actual_return
            | TFn (expected_params, expected_return),
              TFn (actual_params, actual_return) ->
                plan_callback ~row_type_name_for ~protocol_satisfies
                  ~sequence_satisfies expected actual expected_params
                  expected_return actual_params actual_return
            | TFn (expected_params, expected_return),
              TOverloaded_fn actual_arities ->
                plan_overloaded_callback ~row_type_name_for
                  ~protocol_satisfies ~sequence_satisfies expected actual
                  expected_params expected_return actual_arities
            | TOverloaded_fn expected_arities,
              TOverloaded_fn actual_arities ->
                (match expected_arities with
                | [ expected_arity ]
                  when List.is_empty expected_arity.fixed_params
                       && overload_covers_variadic_identity expected_arity
                            actual_arities ->
                    Ok
                      (Overload_to_variadic
                         { expected_arity; actual_arities })
                | _ ->
                    plan_overload ~row_type_name_for ~protocol_satisfies
                      ~sequence_satisfies expected actual expected_arities
                      actual_arities)
            | TOverloaded_fn expected_arities,
              TFn (actual_params, actual_return) ->
                plan_function_overload ~row_type_name_for
                  ~protocol_satisfies ~sequence_satisfies expected actual
                  expected_arities actual_params actual_return
            | TPoly_variant _, TOcaml name -> (
                match Ocaml_signature.of_compiler_type
                        (Lg_compiler_support.Ocaml_value.Constructor (name, [])) with
                | TPoly_variant _ as manifest ->
                    plan ~row_type_name_for ~protocol_satisfies
                      ~sequence_satisfies expected manifest
                | _ -> Error (Incompatible_types { expected; actual }))
            | TOcaml name, TPoly_variant _ -> (
                match Ocaml_signature.of_compiler_type
                        (Lg_compiler_support.Ocaml_value.Constructor (name, [])) with
                | TPoly_variant _ as manifest ->
                    plan ~row_type_name_for ~protocol_satisfies
                      ~sequence_satisfies manifest actual
                | _ -> Error (Incompatible_types { expected; actual }))
            | TPoly_variant expected_row, TPoly_variant actual_row
              when Variant_row.compatible expected_row actual_row ->
                let rec plan_tags planned = function
                  | [] ->
                      if List.for_all
                           (function _, None | _, Some (_, Identity) -> true | _ -> false)
                           planned
                      then Ok Identity
                      else Ok (Variant_payloads (List.rev planned))
                  | (tag, payload) :: rest ->
                      let expected_payload = List.assoc_opt tag expected_row.tags in
                      (match payload, expected_payload with
                       | None, (None | Some None) ->
                           plan_tags ((tag, None) :: planned) rest
                       | Some actual, Some (Some expected) ->
                           Result.bind
                             (plan ~row_type_name_for ~protocol_satisfies
                                ~sequence_satisfies expected actual)
                             (fun adaptation ->
                               plan_tags ((tag, Some (actual, adaptation)) :: planned) rest)
                       | Some actual, None ->
                           plan_tags ((tag, Some (actual, Identity)) :: planned) rest
                       | _ -> Error (Incompatible_types {expected; actual}))
                in
                plan_tags [] actual_row.tags
            | TTuple expected_elements, TTuple actual_elements
              when List.length expected_elements = List.length actual_elements ->
                let rec plan_elements planned expected actual =
                  match (expected, actual) with
                  | [], [] ->
                      let planned = List.rev planned in
                      if
                        List.for_all
                          (function Identity -> true | _ -> false)
                          planned
                      then Ok Identity
                      else Ok (Tuple_elements planned)
                  | expected :: expected_rest, actual :: actual_rest ->
                      Result.bind
                        (plan ~row_type_name_for ~protocol_satisfies
                           ~sequence_satisfies expected actual)
                        (fun adaptation ->
                          plan_elements (adaptation :: planned) expected_rest
                            actual_rest)
                  | _ -> assert false
                in
                plan_elements [] expected_elements actual_elements
            | TVector expected_element, TTuple actual_elements
              when not (List.is_empty actual_elements) ->
                let rec plan_elements planned = function
                  | [] ->
                      Ok
                        (Tuple_to_vector
                           {
                             expected_element;
                             actual_elements;
                             element_adaptations = List.rev planned;
                           })
                  | actual_element :: rest ->
                      Result.bind
                        (plan ~row_type_name_for ~protocol_satisfies
                           ~sequence_satisfies expected_element actual_element)
                        (fun adaptation ->
                          plan_elements (adaptation :: planned) rest)
                in
                plan_elements [] actual_elements
            | TList expected_element, TList actual_element ->
                plan_collection ~row_type_name_for ~protocol_satisfies
                  ~sequence_satisfies List_collection expected_element
                  actual_element
            | TVector expected_element, TVector actual_element ->
                plan_collection ~row_type_name_for ~protocol_satisfies
                  ~sequence_satisfies Vector_collection expected_element
                  actual_element
            | TVector expected_element, TSeq actual_element ->
                Result.map
                  (fun element_adaptation ->
                    Vector_from_sequence
                      {
                        source = Sequence_source;
                        expected_element;
                        actual_element;
                        element_adaptation;
                      })
                  (plan ~row_type_name_for ~protocol_satisfies
                     ~sequence_satisfies expected_element actual_element)
            | TVector expected_element, TOcaml_app (name, [ actual_element ])
              when sequence_representation_type_name name ->
                Result.map
                  (fun element_adaptation ->
                    Vector_from_sequence
                      {
                        source = Sequence_source;
                        expected_element;
                        actual_element;
                        element_adaptation;
                      })
                  (plan ~row_type_name_for ~protocol_satisfies
                     ~sequence_satisfies expected_element actual_element)
            | TSeq expected_element, TSeq actual_element ->
                plan_collection ~row_type_name_for ~protocol_satisfies
                  ~sequence_satisfies Sequence_collection expected_element
                  actual_element
            | TSeq expected_element, TList actual_element ->
                Result.map
                  (fun element_adaptation ->
                    Sequence_representation
                      {
                        source = List_source;
                        expected_element;
                        actual_element;
                        element_adaptation;
                      })
                  (plan ~row_type_name_for ~protocol_satisfies
                     ~sequence_satisfies expected_element actual_element)
            | TSeq expected_element, TVector actual_element ->
                Result.map
                  (fun element_adaptation ->
                    Sequence_representation
                      {
                        source = Vector_source;
                        expected_element;
                        actual_element;
                        element_adaptation;
                      })
                  (plan ~row_type_name_for ~protocol_satisfies
                     ~sequence_satisfies expected_element actual_element)
            | TSeq expected_element, TOcaml_app (name, [ actual_element ])
            | TOcaml_app (name, [ expected_element ]), TSeq actual_element
              when sequence_representation_type_name name ->
                plan_collection ~row_type_name_for ~protocol_satisfies
                  ~sequence_satisfies Sequence_collection expected_element
                  actual_element
            | ( TOcaml_app (expected_name, [ expected_element ]),
                TOcaml_app (actual_name, [ actual_element ]) )
              when sequence_representation_type_name expected_name
                   && sequence_representation_type_name actual_name ->
                plan_collection ~row_type_name_for ~protocol_satisfies
                  ~sequence_satisfies Sequence_collection expected_element
                  actual_element
            | TArray expected_element, TArray actual_element ->
                plan_collection ~row_type_name_for ~protocol_satisfies
                  ~sequence_satisfies Array_collection expected_element
                  actual_element
            | TSet expected_element, TSet actual_element ->
                plan_collection ~row_type_name_for ~protocol_satisfies
                  ~sequence_satisfies Set_collection expected_element
                  actual_element
            | TOcaml_app
                ("Lg_runtime.Runtime_map.t", [ expected_key; expected_value ]),
              TOcaml_app
                ("Lg_runtime.Runtime_map.t", [ actual_key; actual_value ]) ->
                plan_map ~row_type_name_for ~protocol_satisfies
                  ~sequence_satisfies expected_key expected_value actual_key
                  actual_value
            | TOcaml_app
                ("Lg_runtime.Runtime_map.t", [ expected_key; expected_value ]),
              (TRecord fields as source_ty) ->
                plan_record_to_map ~row_type_name_for ~protocol_satisfies
                  ~sequence_satisfies expected_key expected_value source_ty
                  fields
            | ( TConstraint
                (Seqable_constraint
                  {
                    requirement;
                    element = expected_element;
                    storage = storage_ty;
                  }),
                _ ) ->
                let plan_element =
                  plan ?row_type_name ~row_type_name_for ~protocol_satisfies
                    ~sequence_satisfies
                in
                if
                  sequence_source_compatible ~sequence_satisfies
                    ~element_adapts:(fun expected actual ->
                      Result.is_ok (plan_element expected actual))
                    requirement expected_element actual
                then
                  let rec element_plan = function
                    | TNullable inner | TOcaml_app ("option", [ inner ]) ->
                        element_plan inner
                    | source ->
                        match sequence_element_type source with
                        | None -> Ok None
                        | Some actual_element ->
                            Result.map
                              (function
                                | Identity -> None
                                | adaptation -> Some (actual_element, adaptation))
                              (plan_element expected_element actual_element)
                  in
                  Result.map
                    (fun element_adaptation ->
                      Sequence_witness
                        { requirement; expected_element; storage_ty;
                          source_ty = actual; row_type_name; element_adaptation })
                    (element_plan actual)
                else (
                  match
                    nested_non_seqable_element ~sequence_satisfies
                      expected_element actual
                  with
                  | Some actual -> Error (Non_seqable actual)
                  | None -> Error (Incompatible_types { expected; actual }))
            | _ -> (
                match expected with
                | TConstraint
                    (Protocol_constraint { protocol_id; _ }) ->
                    let source_ty = Types.constraint_value_type actual in
                    let implementation_available =
                      protocol_satisfies protocol_id source_ty
                    in
                    Ok
                      (Protocol_witness
                         {
                           protocol_id;
                           expected;
                           source_ty;
                           implementation_available;
                         })
                | TConstraint (Open_boundary_constraint _) ->
                    Error (Incompatible_types { expected; actual })
                | TConstraint _ when open_leaf actual ->
                    (* A capability witness cannot be materialized for a
                       bare open source type; let callers fall back to
                       another arity or adaptation instead of failing at
                       emit. *)
                    Error (Incompatible_types { expected; actual })
                | TConstraint _ ->
                    Ok (Capability_witness { expected; source_ty = actual })
                | _ -> Error (Incompatible_types { expected; actual }))))

and plan_constrained_result_callback ~row_type_name_for ~protocol_satisfies
    ~sequence_satisfies expected actual expected_params expected_return
    actual_params actual_return =
  if List.length expected_params <> List.length actual_params then
    Error (Incompatible_types { expected; actual })
  else
    let actual_params, actual_return =
      if Option.is_some (Types.truthy_constraint_info expected_return) then
        (actual_params, actual_return)
      else
        let substitutions =
          List.fold_left2
            (fun substitutions actual expected ->
              Type_solver.unify substitutions actual expected
              |> Result.value ~default:substitutions)
            Type_solver.empty actual_params expected_params
        in
        ( List.map (Type_solver.apply substitutions) actual_params,
          Type_solver.apply substitutions actual_return )
    in
    let rec plan_arguments planned incoming parameters =
      match (incoming, parameters) with
      | [], [] -> Ok (List.rev planned)
      | incoming :: incoming_rest, parameter :: parameter_rest ->
          Result.bind
            (plan ~row_type_name_for ~protocol_satisfies ~sequence_satisfies
               parameter incoming)
            (fun adaptation ->
              plan_arguments (adaptation :: planned) incoming_rest
                parameter_rest)
      | _ -> Error (Incompatible_types { expected; actual })
    in
    Result.map
      (fun argument_adaptations ->
        Constrained_result_callback
          {
            expected_params;
            actual_params;
            expected_return;
            actual_return;
            argument_adaptations;
          })
      (plan_arguments [] expected_params actual_params)

and plan_reduced_callback ~row_type_name_for ~protocol_satisfies
    ~sequence_satisfies expected actual expected_params expected_return
    actual_params actual_return =
  let expected_payload =
    match Types.maybe_reduced_callback_element expected_return with
    | Some payload -> payload
    | None -> Types.reduced_element expected_return |> Option.get
  in
  let actual_returns_reduced, actual_payload =
    match Types.maybe_reduced_callback_element actual_return with
    | Some payload -> (true, payload)
    | None -> (
        match Types.reduced_element actual_return with
        | Some payload -> (true, payload)
        | None -> (false, actual_return))
  in
  if List.length expected_params <> List.length actual_params then
    Error (Incompatible_types { expected; actual })
  else
    let rec plan_arguments planned incoming parameters =
      match (incoming, parameters) with
      | [], [] -> Ok (List.rev planned)
      | incoming :: incoming_rest, parameter :: parameter_rest ->
          Result.bind
            (plan ~row_type_name_for ~protocol_satisfies ~sequence_satisfies
               parameter incoming)
            (fun adaptation ->
              plan_arguments (adaptation :: planned) incoming_rest
                parameter_rest)
      | _ -> Error (Incompatible_types { expected; actual })
    in
    Result.bind
      (plan_arguments [] expected_params actual_params)
      (fun argument_adaptations ->
        Result.bind
          (plan ~row_type_name_for ~protocol_satisfies ~sequence_satisfies
             expected_payload actual_payload)
          (fun result_adaptation ->
            if actual_returns_reduced && result_adaptation <> Identity then
              Error (Incompatible_types { expected; actual })
            else
              Ok
                (Reduced_callback
                   {
                     expected_params;
                     actual_params;
                     actual_return;
                     argument_adaptations;
                     result_adaptation;
                     actual_returns_reduced;
                   })))

and plan_overloaded_callback ~row_type_name_for ~protocol_satisfies
    ~sequence_satisfies expected actual expected_params expected_return
    actual_arities =
  let arity_parameters (arity : fn_arity) =
    let fixed_count = List.length arity.fixed_params in
    if List.length expected_params < fixed_count then None
    else
      match arity.rest_param with
      | None ->
          if List.length expected_params = fixed_count then
            Some arity.fixed_params
          else None
      | Some rest_ty ->
          Some
            (arity.fixed_params
            @ List.init
                (List.length expected_params - fixed_count)
                (Fun.const rest_ty))
  in
  let rec plan_arguments planned incoming parameters =
    match (incoming, parameters) with
    | [], [] -> Ok (List.rev planned)
    | incoming :: incoming_rest, parameter :: parameter_rest ->
        Result.bind
          (plan ~row_type_name_for ~protocol_satisfies ~sequence_satisfies
             parameter incoming)
          (fun adaptation ->
            plan_arguments (adaptation :: planned) incoming_rest parameter_rest)
    | _ -> Error (Incompatible_types { expected; actual })
  in
  let plan_arity actual_index (actual_arity : fn_arity) =
    match arity_parameters actual_arity with
    | None -> Error (Incompatible_types { expected; actual })
    | Some actual_params ->
        Result.bind
          (plan_arguments [] expected_params actual_params)
          (fun argument_adaptations ->
            let truthy_result =
              Types.equal expected_return TBool
              && Types.is_dynamic actual_arity.return_ty
            in
            let result_plan =
              if truthy_result then Ok None
              else
                Result.map Option.some
                  (plan ~row_type_name_for ~protocol_satisfies
                     ~sequence_satisfies expected_return actual_arity.return_ty)
            in
            Result.map
              (fun result_adaptation ->
                Overloaded_callback
                  {
                    actual_index;
                    actual_arity;
                    expected_params;
                    actual_params;
                    actual_return = actual_arity.return_ty;
                    argument_adaptations;
                    result_adaptation;
                    truthy_result;
                  })
              result_plan)
  in
  let rec select index = function
    | [] -> Error (Incompatible_types { expected; actual })
    | arity :: rest -> (
        match plan_arity index arity with
        | Ok plan -> Ok plan
        | Error _ -> select (index + 1) rest)
  in
  select 0 actual_arities

and plan_callback ~row_type_name_for ~protocol_satisfies ~sequence_satisfies
    expected actual expected_params expected_return actual_params actual_return =
  let normalize_thunk_parameters = function [] -> [ TUnit ] | params -> params in
  let expected_params = normalize_thunk_parameters expected_params in
  let actual_params = normalize_thunk_parameters actual_params in
  if List.length expected_params <> List.length actual_params then
    Error (Incompatible_types { expected; actual })
  else
    let substitutions =
      List.fold_left2
        (fun substitutions actual expected ->
          Type_solver.unify substitutions actual expected
          |> Result.value ~default:substitutions)
        Type_solver.empty actual_params expected_params
    in
    let actual_params =
      List.map (Type_solver.apply substitutions) actual_params
    in
    let actual_return = Type_solver.apply substitutions actual_return in
    let structural_callback_accepts_record structural incoming =
      let structural_fields =
        match structural with
        | TRecord fields | TNamed_record { fields; nominal = false; _ } ->
            Some fields
        | _ -> None
      in
      match (structural_fields, external_record_type incoming) with
      | Some structural_fields, TNamed_record incoming_record ->
          List.for_all
            (fun (structural_field : field) ->
              match
                List.find_opt
                  (fun (incoming_field : field) ->
                    String.equal incoming_field.keyword structural_field.keyword)
                  incoming_record.fields
              with
              | Some incoming_field ->
                  identity_compatible structural_field.ty incoming_field.ty
                  || open_leaf structural_field.ty
                  || open_leaf incoming_field.ty
              | None -> false)
            structural_fields
      | _ -> false
    in
    let rec plan_arguments adaptations expected actual =
      match (expected, actual) with
      | [], [] -> Ok (List.rev adaptations)
      | expected :: expected_rest, actual :: actual_rest ->
          let planned =
            if structural_callback_accepts_record actual expected then
              Ok Identity
            else
              plan ~row_type_name_for ~protocol_satisfies ~sequence_satisfies
                actual expected
          in
          Result.bind planned
            (fun adaptation ->
              plan_arguments (adaptation :: adaptations) expected_rest
                actual_rest)
      | _ -> assert false
    in
    Result.bind
      (plan_arguments [] expected_params actual_params)
      (fun argument_adaptations ->
        Result.map
          (fun result_adaptation ->
            if
              List.for_all
                (function Identity -> true | _ -> false)
                argument_adaptations
              && match result_adaptation with Identity -> true | _ -> false
            then Identity
            else
              Callback
                {
                  expected_params;
                  actual_params;
                  actual_return;
                  argument_adaptations;
                  result_adaptation;
                })
          (plan ~row_type_name_for ~protocol_satisfies ~sequence_satisfies
             expected_return actual_return))

and plan_overload ~row_type_name_for ~protocol_satisfies ~sequence_satisfies
    expected actual expected_arities actual_arities =
  let stored_arity_type (arity : fn_arity) =
    TFn
      ( arity.fixed_params
        @ Option.fold ~none:[] ~some:(fun rest -> [ TSeq rest ])
            arity.rest_param,
        arity.return_ty )
  in
  let matching_arity expected =
    actual_arities
    |> List.mapi (fun index actual -> (index, actual))
    |> List.find_opt (fun (_, actual) ->
           List.length expected.fixed_params
           = List.length actual.fixed_params
           && Option.is_some expected.rest_param
              = Option.is_some actual.rest_param)
  in
  let rec plan_arities planned = function
    | [] -> Ok (Overload { arities = List.rev planned })
    | expected_arity :: rest -> (
        match matching_arity expected_arity with
        | None -> Error (Incompatible_types { expected; actual })
        | Some (actual_index, actual_arity) ->
            let actual_ty = stored_arity_type actual_arity in
            Result.bind
              (plan ~row_type_name_for ~protocol_satisfies ~sequence_satisfies
                 (stored_arity_type expected_arity) actual_ty)
              (fun adaptation ->
                plan_arities
                  ({ actual_index; actual_ty; adaptation } :: planned)
                  rest))
  in
  plan_arities [] expected_arities

and plan_function_overload ~row_type_name_for ~protocol_satisfies
    ~sequence_satisfies expected actual expected_arities actual_params
    actual_return =
  let stored_arity_type (arity : fn_arity) =
    TFn
      ( arity.fixed_params
        @ Option.fold ~none:[] ~some:(fun rest -> [ TSeq rest ])
            arity.rest_param,
        arity.return_ty )
  in
  let every_function_type = function
    | TFn ([ TFn ([ _ ], truthy); seqable ], TBool)
      when Option.is_some (Types.truthy_constraint_info truthy)
           && Option.is_some (Types.seqable_constraint_info seqable) ->
        true
    | _ -> false
  in
  let actual_ty = TFn (actual_params, actual_return) in
  let rec plan_arguments planned incoming actual_parameters =
    match (incoming, actual_parameters) with
    | [], [] -> Ok (List.rev planned)
    | incoming :: incoming_rest, actual_parameter :: actual_rest ->
        Result.bind
          (plan ~row_type_name_for ~protocol_satisfies ~sequence_satisfies
             actual_parameter incoming)
          (fun adaptation ->
            plan_arguments (adaptation :: planned) incoming_rest actual_rest)
    | _ -> Error (Incompatible_types { expected; actual })
  in
  let plan_arity (expected_arity : fn_arity) =
    match expected_arity.rest_param with
    | None -> (
        match
          plan ~row_type_name_for ~protocol_satisfies ~sequence_satisfies
            (stored_arity_type expected_arity) actual_ty
        with
        | Ok adaptation -> Ok (Planned_function_arity adaptation)
        | Error _ when every_function_type actual_ty ->
            Ok
              (Every_special_arity
                 { expected_ty = stored_arity_type expected_arity })
        | Error error -> Error error)
    | Some rest_ty ->
        let fixed_count = List.length expected_arity.fixed_params in
        if List.length actual_params < fixed_count then
          Error (Incompatible_types { expected; actual })
        else
          let extra_count = List.length actual_params - fixed_count in
          let incoming =
            expected_arity.fixed_params @ List.init extra_count (Fun.const rest_ty)
          in
          Result.bind
            (plan_arguments [] incoming actual_params)
            (fun argument_adaptations ->
              Result.map
                (fun result_adaptation ->
                  Fixed_to_variadic_arity
                    {
                      expected = expected_arity;
                      argument_adaptations;
                      result_adaptation;
                    })
                (plan ~row_type_name_for ~protocol_satisfies
                   ~sequence_satisfies expected_arity.return_ty actual_return))
  in
  let rec plan_arities planned = function
    | [] ->
        Ok
          (Function_overload
             {
               actual_params;
               actual_return;
               arities = List.rev planned;
             })
    | expected_arity :: rest ->
        Result.bind (plan_arity expected_arity) (fun planned_arity ->
            plan_arities (planned_arity :: planned) rest)
  in
  plan_arities [] expected_arities

and plan_collection ~row_type_name_for ~protocol_satisfies ~sequence_satisfies
    kind expected_element actual_element =
  Result.map
    (function
      | Identity when kind <> Set_collection -> Identity
      | element_adaptation ->
          Collection_representation
            {
              kind;
              expected_element;
              actual_element;
              element_adaptation;
            })
    (plan ~row_type_name_for ~protocol_satisfies ~sequence_satisfies
       expected_element actual_element)

and plan_map ~row_type_name_for ~protocol_satisfies ~sequence_satisfies
    expected_key expected_value actual_key actual_value =
  Result.bind
    (plan ~row_type_name_for ~protocol_satisfies ~sequence_satisfies expected_key
       actual_key)
    (fun key_adaptation ->
      Result.map
        (fun value_adaptation ->
          match (key_adaptation, value_adaptation) with
          | Identity, Identity -> Identity
          | _ ->
              Map_representation
                {
                  expected_key;
                  actual_key;
                  actual_value;
                  key_adaptation;
                  value_adaptation;
                })
        (plan ~row_type_name_for ~protocol_satisfies ~sequence_satisfies
           expected_value actual_value))

and plan_record_to_map ~row_type_name_for ~protocol_satisfies
    ~sequence_satisfies expected_key expected_value source_ty fields =
  if
    List.exists
      (fun field ->
        Types.is_record_extension_field field
        || Types.is_record_identity_field field)
      fields
  then
    Error
      (Incompatible_types
         { expected = Types.dynamic_map expected_key expected_value; actual = source_ty })
  else
    let rec plan_entries entries = function
      | [] ->
          Ok
            (Record_to_map
               { expected_key; source_ty; entries = List.rev entries })
      | field :: rest ->
          Result.bind
            (plan ~row_type_name_for ~protocol_satisfies ~sequence_satisfies
               expected_key TKeyword)
            (fun key_adaptation ->
              Result.bind
                (plan ~row_type_name_for ~protocol_satisfies ~sequence_satisfies
                   expected_value field.ty)
                (fun value_adaptation ->
                  plan_entries
                    ({ field; key_adaptation; value_adaptation } :: entries)
                    rest))
    in
    plan_entries [] fields

let plan_record_callable ~row_type_name_for ~protocol_satisfies
    ~sequence_satisfies expected actual =
  match (expected, Types.record_fields actual) with
  | TFn ([ key_ty ], expected_return), Some fields
    when Types.equal key_ty TKeyword ->
      if Types.equal expected_return TBool then
        Ok
          (Record_callable
             {
               fields;
               result_adaptations = [];
               missing_adaptation = None;
               truthy_result = true;
             })
      else
        let rec plan_fields planned = function
          | [] ->
              Result.map
                (fun missing_adaptation ->
                  Record_callable
                    {
                      fields;
                      result_adaptations = List.rev planned;
                      missing_adaptation = Some missing_adaptation;
                      truthy_result = false;
                    })
                (plan ~row_type_name_for ~protocol_satisfies
                   ~sequence_satisfies expected_return TNil)
          | (field : field) :: rest ->
              Result.bind
                (plan ~row_type_name_for ~protocol_satisfies
                   ~sequence_satisfies expected_return field.ty)
                (fun adaptation -> plan_fields (adaptation :: planned) rest)
        in
        plan_fields [] fields
  | _ -> Error (Incompatible_types { expected; actual })

let plan_argument ?row_type_name ?(protocol_storage = false)
    ?(allow_optional_unwrap = false)
    ?(allow_record_callable = false)
    ?(row_type_name_for = fun _ -> None)
    ?(protocol_satisfies = fun _ _ -> false)
    ?(sequence_satisfies = fun _ _ -> false) ~expected ~actual () =
  let planned =
    if allow_record_callable then
      match
        plan_record_callable ~row_type_name_for ~protocol_satisfies
          ~sequence_satisfies expected actual
      with
      | Ok _ as planned -> planned
      | Error _ ->
          plan ?row_type_name ~row_type_name_for ~protocol_satisfies
            ~sequence_satisfies expected actual
    else
      plan ?row_type_name ~row_type_name_for ~protocol_satisfies
        ~sequence_satisfies expected actual
  in
  if protocol_storage then
    match nullable_payload actual with
    | None -> planned
    | Some payload -> (
        match
          plan ?row_type_name ~row_type_name_for ~protocol_satisfies
            ~sequence_satisfies expected payload
        with
        | Ok Identity -> Ok Protocol_storage_passthrough
        | Ok _ | Error _ -> planned)
  else if allow_optional_unwrap then
    match nullable_payload actual with
    | None -> planned
    | Some payload ->
        Result.map
          (fun adaptation -> Optional_unwrap adaptation)
          (plan ?row_type_name ~row_type_name_for ~protocol_satisfies
             ~sequence_satisfies expected payload)
  else planned
