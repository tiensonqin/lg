val redefable_roots : bool ref
(* When false, top-level definitions compile to plain OCaml bindings with no
   redefinition cell or wrapper, shrinking generated output. The `--no-redef`
   batch-compile flag clears it; do not use for code that is redefined or
   `with-redefs`-patched later. *)

val function_is_recursive : string -> string -> Ast.form list -> bool

val expression_references_declaration :
  Compiler_environment.t -> Semantic_ir.t -> bool

val compile :
  string ->
  Compiler_environment.t ->
  int ->
  Ast.form ->
  (string * Compiler_environment.t * int * Lowered.compiled_item, Error.t)
  result
