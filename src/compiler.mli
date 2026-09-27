type diagnostic_phase = Error.phase

type compile_error = Error.t = {
  code : string;
  phase : diagnostic_phase;
  title : string;
  message : string;
  location : Location.t option;
  related : Error.related list;
  hints : string list;
  fixes : Error.fix list;
  type_mismatch : Error.type_mismatch option;
}

type diagnostic_severity = [ `Warning ]

type diagnostic = Toolchain.diagnostic = {
  code : string;
  phase : diagnostic_phase;
  message : string;
  severity : diagnostic_severity;
  location : Location.t option;
}

type compilation = Toolchain.compilation = {
  ocaml_source : string;
  ocaml_signature : string option;
  diagnostics : diagnostic list;
}

type repl_form_kind = Toolchain.repl_form_kind =
  | Repl_value
  | Repl_definition of {
      name : string;
      type_name : string;
    }
  | Repl_namespace of string
  | Repl_summary of string

type repl_compilation = Toolchain.repl_compilation = {
  structure : Parsetree.structure;
  kind : repl_form_kind;
}

type state = Toolchain.state
type prepared_source = Toolchain.prepared_source

val empty_state : state
val cacheable_state : state -> state
val with_source_scope : string -> state -> state
val source_scope : state -> string
val state_environment : state -> Env.t
val has_ocaml_environment : state -> bool

val render_error : source:string -> compile_error -> string

(* Each prefix is (ocaml_source, marshaled OCaml signature option). *)
val restore_ocaml_environment :
  ?target:Target.t ->
  packages:string list ->
  state ->
  (string * string option) list ->
  (state, compile_error) result

val compile_string :
  ?target:Target.t -> string -> (string, compile_error) result

val compile_string_with_filename :
  ?target:Target.t ->
  filename:string ->
  string ->
  (string, compile_error) result

val compile_string_with_diagnostics :
  ?target:Target.t -> string -> (compilation, compile_error) result

val compile_string_with_filename_and_diagnostics :
  ?target:Target.t ->
  filename:string ->
  string ->
  (compilation, compile_error) result

val required_ocaml_packages :
  ?target:Target.t ->
  ?filename:string ->
  string ->
  (string list, compile_error) result

val prepare_source :
  ?target:Target.t ->
  ?reader_target:Target.t ->
  ?filename:string ->
  string ->
  (prepared_source, compile_error) result

val prepared_source_required_packages : prepared_source -> string list

val infer_interface :
  ?target:Target.t -> string -> (string, compile_error) result

val infer_interface_with_filename :
  ?target:Target.t ->
  filename:string ->
  string ->
  (string, compile_error) result

val infer_interface_from_state :
  ?target:Target.t ->
  filename:string ->
  state ->
  string ->
  (string, compile_error) result

val compile_parsetree :
  ?target:Target.t -> string -> (Parsetree.structure, compile_error) result

val compile_parsetree_with_filename :
  ?target:Target.t ->
  filename:string ->
  string ->
  (Parsetree.structure, compile_error) result

val typecheck_parsetree :
  ?target:Target.t -> string -> (unit, compile_error) result

val print_parsetree : Parsetree.structure -> string

val compile_chunk :
  ?target:Target.t ->
  state ->
  string ->
  (state * string, compile_error) result

val compile_chunk_with_filename :
  ?target:Target.t ->
  filename:string ->
  state ->
  string ->
  (state * string, compile_error) result

val compile_chunk_with_filename_and_diagnostics :
  ?target:Target.t ->
  ?check_ocaml:bool ->
  filename:string ->
  state ->
  string ->
  (state * compilation, compile_error) result

val compile_prepared_chunk_with_diagnostics :
  ?check_ocaml:bool ->
  state ->
  prepared_source ->
  (state * compilation, compile_error) result

val compile_chunk_parsetree :
  ?target:Target.t ->
  ?check_ocaml:bool ->
  state ->
  string ->
  (state * Parsetree.structure, compile_error) result

val compile_chunk_parsetree_with_filename :
  ?target:Target.t ->
  ?check_ocaml:bool ->
  filename:string ->
  state ->
  string ->
  (state * Parsetree.structure, compile_error) result

val compile_repl_form :
  ?target:Target.t ->
  ?filename:string ->
  ?check_ocaml:bool ->
  state ->
  string ->
  (state * repl_compilation, compile_error) result

val infer_repl_type :
  ?target:Target.t -> state -> string -> (string, compile_error) result
