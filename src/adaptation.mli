type protocol_witness = {
  protocol_id : Protocol_id.t;
  expected : Semantic_type.ty;
  source_ty : Semantic_type.ty;
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
  | Variant_payloads of (string * (Semantic_type.ty * t) option) list
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
  | Sequence_value of sequence_witness
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
  requirement : Semantic_type.seqable_requirement;
  expected_element : Semantic_type.ty;
  storage_ty : Semantic_type.ty;
  source_ty : Semantic_type.ty;
  row_type_name : string option;
  element_adaptation : (Semantic_type.ty * t) option;
}

and callback = {
  expected_params : Semantic_type.ty list;
  actual_params : Semantic_type.ty list;
  actual_return : Semantic_type.ty;
  argument_adaptations : t list;
  result_adaptation : t;
}

and constrained_result_callback = {
  expected_params : Semantic_type.ty list;
  actual_params : Semantic_type.ty list;
  expected_return : Semantic_type.ty;
  actual_return : Semantic_type.ty;
  argument_adaptations : t list;
  result_adaptation : t;
}

and constant_function = {
  expected_params : Semantic_type.ty list;
  actual_return : Semantic_type.ty;
  result_adaptation : t;
}

and map_callable = {
  expected_key : Semantic_type.ty;
  actual_key : Semantic_type.ty;
  actual_value : Semantic_type.ty;
  key_adaptation : t;
  result_adaptation : t option;
  truthy_result : bool;
}

and record_callable = {
  fields : Semantic_type.field list;
  result_adaptations : t list;
  missing_adaptation : t option;
  truthy_result : bool;
}

and set_callable = { adaptation : t }

and overload_to_variadic = {
  expected_arity : Semantic_type.fn_arity;
  actual_arities : Semantic_type.fn_arity list;
}

and sequence_representation = {
  source : sequence_representation_source;
  expected_element : Semantic_type.ty;
  actual_element : Semantic_type.ty;
  element_adaptation : t;
}

and tuple_to_vector = {
  expected_element : Semantic_type.ty;
  actual_elements : Semantic_type.ty list;
  element_adaptations : t list;
}

and overload = { arities : overload_arity list }

and function_overload = {
  actual_params : Semantic_type.ty list;
  actual_return : Semantic_type.ty;
  arities : function_overload_arity list;
}

and overloaded_callback = {
  actual_index : int;
  actual_arity : Semantic_type.fn_arity;
  expected_params : Semantic_type.ty list;
  actual_params : Semantic_type.ty list;
  actual_return : Semantic_type.ty;
  argument_adaptations : t list;
  result_adaptation : t option;
  truthy_result : bool;
}

and reduced_callback = {
  expected_params : Semantic_type.ty list;
  actual_params : Semantic_type.ty list;
  actual_return : Semantic_type.ty;
  argument_adaptations : t list;
  result_adaptation : t;
  actual_returns_reduced : bool;
}

and function_overload_arity =
  | Planned_function_arity of t
  | Fixed_to_variadic_arity of {
      expected : Semantic_type.fn_arity;
      argument_adaptations : t list;
      result_adaptation : t;
    }
  | Every_special_arity of { expected_ty : Semantic_type.ty }

and overload_arity = {
  actual_index : int;
  actual_ty : Semantic_type.ty;
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
  expected_element : Semantic_type.ty;
  actual_element : Semantic_type.ty;
  element_adaptation : t;
}

and map_representation = {
  expected_key : Semantic_type.ty;
  actual_key : Semantic_type.ty;
  actual_value : Semantic_type.ty;
  key_adaptation : t;
  value_adaptation : t;
}

and record_to_map = {
  expected_key : Semantic_type.ty;
  source_ty : Semantic_type.ty;
  entries : record_map_entry list;
}

and record_map_entry = {
  field : Semantic_type.field;
  key_adaptation : t;
  value_adaptation : t;
}

and capability_witness = {
  expected : Semantic_type.ty;
  source_ty : Semantic_type.ty;
}

and row_projection = {
  type_name : string;
  expected_fields : Semantic_type.field list;
  source_ty : Semantic_type.ty;
  field_plans : row_field_plan list;
}

and structural_projection = {
  expected_fields : Semantic_type.field list;
  source_ty : Semantic_type.ty;
  field_plans : row_field_plan list;
}

and row_field_plan =
  | Source_field of {
      expected : Semantic_type.field;
      actual : Semantic_type.field;
      adaptation : t;
    }
  | Missing_optional_field of Semantic_type.field
  | Missing_constrained_field of {
      expected : Semantic_type.field;
      adaptation : t;
    }
  | Missing_extension_field of {
      expected : Semantic_type.field;
      adaptation : t;
    }

type error =
  | Missing_row_field of string
  | Incompatible_row_field of {
      keyword : string;
      expected : Semantic_type.ty;
      actual : Semantic_type.ty;
    }
  | Non_seqable of Semantic_type.ty
  | Incompatible_types of {
      expected : Semantic_type.ty;
      actual : Semantic_type.ty;
    }

val plan_argument :
  ?row_type_name:string ->
  ?protocol_storage:bool ->
  ?allow_optional_unwrap:bool ->
  ?allow_record_callable:bool ->
  ?row_type_name_for:(Semantic_type.field list -> string option) ->
  ?protocol_satisfies:(Protocol_id.t -> Semantic_type.ty -> bool) ->
  ?sequence_satisfies:
    (Semantic_type.seqable_requirement -> Semantic_type.ty -> bool) ->
  expected:Semantic_type.ty ->
  actual:Semantic_type.ty ->
  unit ->
  (t, error) result
