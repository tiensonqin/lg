type compile_error = Error.t = {
  code : string;
  phase : Error.phase;
  title : string;
  message : string;
  location : Location.t option;
  related : Error.related list;
  hints : string list;
  fixes : Error.fix list;
  type_mismatch : Error.type_mismatch option;
}

type diagnostic_phase = Error.phase

type diagnostic_severity = Toolchain.diagnostic_severity

type diagnostic = Toolchain.diagnostic = {
  code : string;
  phase : Error.phase;
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

let empty_state = Toolchain.empty_state
let cacheable_state = Toolchain.cacheable_state
let with_source_scope = Toolchain.with_source_scope
let source_scope = Toolchain.source_scope
let state_environment = Toolchain.state_environment
let has_ocaml_environment state = Option.is_some state.Toolchain.ocaml_env
let render_error = Error.render

let restore_ocaml_environment ?(target = Target.default) ~packages state
    sources =
  Compiler_session.run (fun () ->
      Toolchain.restore_ocaml_environment ~target ~packages state sources)

let compile_string ?(target = Target.default) source =
  Compiler_session.run (fun () -> Toolchain.implementation ~target source)

let compile_string_with_filename ?(target = Target.default) ~filename source =
  Compiler_session.run (fun () ->
      Toolchain.implementation ~target ~filename source)

let compile_string_with_diagnostics ?(target = Target.default) source =
  Compiler_session.run (fun () ->
      Toolchain.implementation_with_diagnostics ~target source)

let compile_string_with_filename_and_diagnostics ?(target = Target.default)
    ~filename source =
  Compiler_session.run (fun () ->
      Toolchain.implementation_with_diagnostics ~target ~filename source)

let required_ocaml_packages ?(target = Target.default) ?(filename = "<string>")
    source =
  Compiler_session.run (fun () ->
      Toolchain.required_ocaml_packages ~target ~filename source)

let prepare_source ?(target = Target.default) ?reader_target
    ?(filename = "<string>") source =
  Compiler_session.run (fun () ->
      Toolchain.prepare_source ~target ?reader_target ~filename source)

let prepared_source_required_packages =
  Toolchain.prepared_source_required_packages

let infer_interface ?(target = Target.default) source =
  Compiler_session.run (fun () -> Toolchain.interface ~target source)

let infer_interface_with_filename ?(target = Target.default) ~filename source =
  Compiler_session.run (fun () ->
      Toolchain.interface ~target ~filename source)

let infer_interface_from_state ?(target = Target.default) ~filename state source =
  Compiler_session.run (fun () ->
      Toolchain.interface_from_state ~target ~filename state source)

let compile_parsetree ?(target = Target.default) source =
  Compiler_session.run (fun () ->
      Toolchain.implementation_parsetree ~target source)

let compile_parsetree_with_filename ?(target = Target.default) ~filename source
    =
  Compiler_session.run (fun () ->
      Toolchain.implementation_parsetree ~target ~filename source)

let typecheck_parsetree ?(target = Target.default) source =
  Compiler_session.run (fun () ->
      Toolchain.typecheck_parsetree ~target source)

let print_parsetree structure = Toolchain.print_parsetree structure

let compile_chunk ?(target = Target.default) state source =
  Compiler_session.run (fun () ->
      Toolchain.compile_chunk ~target state source)

let compile_chunk_with_filename ?(target = Target.default) ~filename state
    source =
  Compiler_session.run (fun () ->
      Toolchain.compile_chunk ~target ~filename state source)

let compile_chunk_with_filename_and_diagnostics ?(target = Target.default)
    ?(check_ocaml = true) ~filename state source =
  Compiler_session.run (fun () ->
      Toolchain.compile_chunk_with_diagnostics ~target ~filename ~check_ocaml
        state source)

let compile_prepared_chunk_with_diagnostics ?(check_ocaml = true) state
    prepared =
  Compiler_session.run (fun () ->
      Toolchain.compile_prepared_chunk_with_diagnostics ~check_ocaml state
        prepared)

let compile_chunk_parsetree ?(target = Target.default) ?(check_ocaml = true)
    state source =
  Compiler_session.run (fun () ->
      Toolchain.compile_chunk_parsetree ~target ~check_ocaml state source)

let compile_chunk_parsetree_with_filename ?(target = Target.default)
    ?(check_ocaml = true) ~filename state source =
  Compiler_session.run (fun () ->
      Toolchain.compile_chunk_parsetree ~target ~filename ~check_ocaml state
        source)

let compile_repl_form ?(target = Target.default) ?(filename = "<string>")
    ?(check_ocaml = true) state source =
  Compiler_session.run (fun () ->
      Toolchain.compile_repl_form ~target ~filename ~check_ocaml state source)

let infer_repl_type ?(target = Target.default) state source =
  Compiler_session.run (fun () ->
      Toolchain.infer_repl_type ~target state source)
