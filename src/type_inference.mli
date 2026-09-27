val replace_param : string -> 'a -> (string * 'a) list -> (string * 'a) list
val refine_type : Types.ty -> Types.ty -> Types.ty
val materialize_dynamic_unknown : Types.ty -> Types.ty

val inferred_form_type :
  ?lookup_binding:(string -> Types.ty) ->
  (string * Types.ty) list -> Ast.form -> Types.ty

val returned_vector_type :
  ?lookup_binding:(string -> Types.ty) ->
  (string * Types.ty) list -> Ast.form -> Types.ty option

val inferred_call_return_type :
  lookup_function_ty:(string -> (Types.ty, 'error) result) ->
  (string * Types.ty) list ->
  Ast.form ->
  Types.ty

val infer_params :
  ?expected_return_ty:Types.ty ->
  ?materialize_open_equality:bool ->
  ?observe_constraint:(Types.ty -> Types.ty -> unit) ->
  ?observe_call:(string -> Ast.form list -> Types.ty list -> unit) ->
  ?lookup_closed_sum_candidates:(Types.ty list -> Types.ty list) ->
  ?lookup_closed_sum_constructors:(Types.ty -> (string * Types.ty list) list) ->
  ?lookup_successful_call_refinement:(string -> (int * Types.ty) option) ->
  ?lookup_call_ty:(string -> Ast.form list -> Types.ty option) ->
  ?expand_form:(Ast.form -> (Ast.form, Error.t) result) ->
  lookup_function_ty:(string -> (Types.ty, 'error) result) ->
  lookup_protocol_constraint:(string -> Types.ty option) ->
  lookup_dynamic_key_record_type:(Types.ty -> Types.ty option) ->
  ?lookup_key_record_type:(string -> string -> Types.ty option) ->
  resolve_named_record:(Types.ty -> Types.ty) ->
  (string * Types.ty) list ->
  Ast.form list ->
  ((string * Types.ty) list, Error.t) result
