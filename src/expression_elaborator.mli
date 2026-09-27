module Env = Compiler_environment
type multi_arity_clause = {
  params : Ast.form;
  body_forms : Ast.form list;
  fixed_count : int;
  rest_index : int option;
  initial_arity : Types.fn_arity;
}
type prepared_multi_arity_clause = {
  target_name : string;
  parts : Expression_support.compiled_fn_parts;
  row_param_types : string option list;
}
type prepared_multi_arity_fn = {
  clauses : prepared_multi_arity_clause list;
  expr : Types.typed_expr;
}
val condp_counter : int ref
val callable_set_counter : int ref
val dynamic_case_counter : int ref
val callable_expression_counter : int ref
val dotimes_counter : int ref
val doseq_counter : int ref
val multi_arity_fn_counter : int ref
val contains_source_macro : string -> Env.t -> Ast.form -> bool
val source_type_tag_symbol :
  string -> Env.t -> string -> Types.typed_expr option
val compile_expr :
  string -> Env.t -> Ast.form -> (Types.typed_expr, Error.t) result
val compile_expr_unlocated :
  string -> Env.t -> Ast.form -> (Types.typed_expr, Error.t) result
val compile_vector :
  string ->
  Env.t -> Ast.form list -> (Types.typed_expr, Error.t) result
val compile_quoted :
  string -> Env.t -> Ast.form -> (Types.typed_expr, Error.t) result
val compile_case :
  string ->
  Env.t ->
  Ast.form -> Ast.form list -> (Types.typed_expr, Error.t) result
val compile_doseq :
  string ->
  Env.t ->
  Ast.form -> Ast.form list -> (Types.typed_expr, Error.t) result
val compile_for :
  string ->
  Env.t -> Ast.form -> Ast.form -> (Types.typed_expr, Error.t) result
val compile_map :
  string ->
  Env.t ->
  (Ast.form * Ast.form) list -> (Types.typed_expr, Error.t) result
val compile_if :
  string ->
  Env.t ->
  Ast.form ->
  Ast.form -> Ast.form -> (Types.typed_expr, Error.t) result
val compile_if_let :
  string ->
  Env.t ->
  Ast.form ->
  Ast.form -> Ast.form -> (Types.typed_expr, Error.t) result
val compile_if_some :
  string ->
  Env.t ->
  Ast.form ->
  Ast.form -> Ast.form -> (Types.typed_expr, Error.t) result
val compile_some_thread :
  string ->
  Env.t -> Ast.form -> Ast.form -> (Types.typed_expr, Error.t) result
val compile_when_let :
  string ->
  Env.t ->
  Ast.form -> Ast.form list -> (Types.typed_expr, Error.t) result
val compile_when_some :
  string ->
  Env.t ->
  Ast.form -> Ast.form list -> (Types.typed_expr, Error.t) result
val compile_let_some :
  string ->
  Env.t ->
  Ast.form ->
  Ast.form -> Ast.form -> (Types.typed_expr, Error.t) result
val compile_condp :
  string ->
  Env.t ->
  Ast.form ->
  Ast.form -> Ast.form list -> (Types.typed_expr, Error.t) result
val compile_logical :
  string ->
  Env.t ->
  [ `And | `Or ] ->
  Ast.form list -> (Types.typed_expr, Error.t) result
val compile_match :
  string ->
  Env.t ->
  Ast.form -> Ast.form list -> (Types.typed_expr, Error.t) result
val compile_body :
  string ->
  Env.t ->
  string -> Ast.form list -> (Types.typed_expr, Error.t) result
val compile_try :
  string ->
  Env.t -> Ast.form list -> (Types.typed_expr, Error.t) result
val loop_branch_type :
  Types.ty -> Types.ty -> (Types.ty, Error.t) result
val compile_recur :
  string ->
  Env.t ->
  string ->
  Types.ty list -> Ast.form list -> (Types.typed_expr, Error.t) result
val compile_loop_tail :
  string ->
  Env.t ->
  string ->
  Types.ty list -> Ast.form -> (Types.typed_expr, Error.t) result
val compile_loop_tail_body :
  string ->
  Env.t ->
  string ->
  Types.ty list -> Ast.form list -> (Types.typed_expr, Error.t) result
val compile_loop :
  string ->
  Env.t ->
  Ast.form -> Ast.form list -> (Types.typed_expr, Error.t) result
val compile_let :
  string ->
  Env.t ->
  Ast.form -> Ast.form list -> (Types.typed_expr, Error.t) result
val compile_letfn :
  string ->
  Env.t ->
  Ast.form -> Ast.form list -> (Types.typed_expr, Error.t) result
val prepare_fn :
  ?param_type_overrides:Types.ty option list ->
  ?additional_inference_params:(string * Types.ty) list ->
  ?refine_inferred_env:((string * Types.ty) list -> Env.t -> Env.t) ->
  ?preferred_record:Types.ty ->
  ?infer_parameters_only:bool ->
  ?variadic_rest_index:int ->
  ?materialize_open_equality:bool ->
  ?refine_open_overrides:bool ->
  ?recur_target:string ->
  ?expected_return_ty:Types.ty ->
  string ->
  Env.t ->
  Ast.form ->
  Ast.form list -> (Expression_support.compiled_fn_parts, Error.t) result
val vector_rest_bindings :
  string -> Ast.form -> (Ast.form list, Error.t) result
val parse_multi_arity_clauses :
  string -> Ast.form list -> (multi_arity_clause list, Error.t) result
val multi_arity_target_name : string -> int -> Types.fn_arity -> string
val multi_arity_value : string list -> Semantic_ir.t
val prepare_multi_arity_fn :
  ?infer_state_return:bool ->
  ?signature:Types.fn_arity list ->
  ocaml_name:string ->
  string ->
  Env.t ->
  string -> Ast.form list -> (prepared_multi_arity_fn, Error.t) result
val lower_prepared_multi_arity :
  prepared_multi_arity_fn ->
  string list * string option list list * Lowered.compiled_item list *
  Lowered.recursive_value list
val prepare_recursive_fn :
  ocaml_name:string ->
  string ->
  Env.t ->
  string ->
  Types.ty ->
  Ast.form ->
  Ast.form list -> (Expression_support.compiled_fn_parts, Error.t) result
val prepare_inferred_recursive_fn_body :
  ?explicit_return_ty:Types.ty ->
  ocaml_name:string ->
  string ->
  Env.t ->
  string ->
  Ast.form ->
  Ast.form list -> (Expression_support.compiled_fn_parts, Error.t) result
val prepare_inferred_recursive_fn :
  ?explicit_return_ty:Types.ty ->
  ocaml_name:string ->
  string ->
  Env.t ->
  string ->
  Ast.form ->
  Ast.form list -> (Expression_support.compiled_fn_parts, Error.t) result
val prepare_inferred_recursive_fn_with_return :
  ocaml_name:string ->
  string ->
  Env.t ->
  string ->
  Types.ty ->
  Ast.form ->
  Ast.form list -> (Expression_support.compiled_fn_parts, Error.t) result
val fn_code :
  ?demote:bool ->
  ?self_name:string ->
  ?row_param_type_names:string option list ->
  Expression_support.compiled_fn_parts -> Types.typed_expr
val compile_multi_arity_fn :
  string ->
  Env.t -> Ast.form list -> (Types.typed_expr, Error.t) result
val compile_fn :
  ?param_type_overrides:Types.ty option list ->
  ?preferred_record:Types.ty ->
  ?use_open_context:bool ->
  string ->
  Env.t ->
  Ast.form -> Ast.form list -> (Types.typed_expr, Error.t) result
val compile_named_fn :
  string ->
  Env.t ->
  string ->
  Ast.form -> Ast.form list -> (Types.typed_expr, Error.t) result
val compile_call :
  string ->
  Env.t ->
  string -> Ast.form list -> (Types.typed_expr, Error.t) result
val context : Elaboration_context.t lazy_t
val compile_args_for :
  string -> Env.t -> Ast.form list -> (Types.typed_expr list, Error.t) result
