type t = { mutable compiler_state : Lg.Compiler.state }

type saved_compilation_state = {
  target : Lg.Target.t;
  state : Lg.Compiler.state;
  packages : string list;
  ocaml_source : string;
  ocaml_signatures : string list;
  cache_key : string; [@warning "-69"]
}

(* The bytecode toplevel can only execute units that are linked into its host
   process. These anchors keep the runtime units used by the prototype visible. *)
let _runtime_anchor = Lg_runtime.Runtime_reference.of_value ()
let _rrbvec_anchor = Rrbvec.empty
let _stdlib_anchor = Lg_stdlib_native.clojure_core_inc 0

let infrastructure_error message =
  Error
    ({
       Lg.Compiler.code = "LG9000";
       phase = `Infrastructure;
       title = "INFRASTRUCTURE ERROR";
       message;
       location = None;
       related = [];
       hints = [];
       fixes = [];
       type_mismatch = None;
     }
      : Lg.Compiler.compile_error)

let prepare_toplevel () =
  let output = Buffer.create 128 in
  let formatter = Format.formatter_of_buffer output in
  let succeeded = Toploop.prepare formatter () in
  Format.pp_print_flush formatter ();
  if succeeded then Ok ()
  else
    infrastructure_error
      (let message = Buffer.contents output in
       if String.equal message "" then "failed to prepare the OCaml toplevel"
       else message)

let read_saved_state path : (saved_compilation_state, string) result =
  Lg.Compiler_artifact.read ~kind:"saved-state" ~path

let open_precompiled_stdlib () =
  let lexbuf = Lexing.from_string "open Lg_stdlib_native;;" in
  Location.init lexbuf "<repl-bootstrap>";
  let phrase = !Toploop.parse_toplevel_phrase lexbuf in
  let output = Buffer.create 128 in
  let formatter = Format.formatter_of_buffer output in
  let succeeded = Toploop.execute_phrase false formatter phrase in
  Format.pp_print_flush formatter ();
  if succeeded then Ok ()
  else
    infrastructure_error
      (let message = Buffer.contents output in
       if String.equal message "" then "failed to open the precompiled stdlib"
       else message)

let create_from_stdlib ~state_path =
  match read_saved_state state_path with
  | Error message -> infrastructure_error message
  | Ok saved when saved.target <> Lg.Target.Native ->
      infrastructure_error "REPL prototype requires a Native stdlib state"
  | Ok saved -> (
      match
        Lg.Compiler.restore_ocaml_environment ~target:Lg.Target.Native
          ~packages:saved.packages saved.state
          (match saved.ocaml_signatures with
          | [] -> [ (saved.ocaml_source, None) ]
          | signatures ->
              List.map
                (fun signature -> (saved.ocaml_source, Some signature))
                signatures)
      with
      | Error _ as error -> error
      | Ok compiler_state -> (
          match prepare_toplevel () with
          | Error _ as error -> error
          | Ok () ->
              let stdlib_cmi_directory =
                Filename.concat (Filename.dirname state_path)
                  ".lg_compiled_stdlib_native.objs/byte"
              in
              Topdirs.dir_directory stdlib_cmi_directory;
              Result.map
                (fun () ->
                  {
                    compiler_state =
                      Lg.Compiler.with_source_scope "user" compiler_state;
                  })
                (open_precompiled_stdlib ())))

let execute structure =
  let output = Buffer.create 256 in
  let formatter = Format.formatter_of_buffer output in
  let succeeded =
    Toploop.execute_phrase true formatter (Parsetree.Ptop_def structure)
  in
  Format.pp_print_flush formatter ();
  (succeeded, Buffer.contents output)

let eval session source =
  match Lg.Compiler.compile_chunk_parsetree session.compiler_state source with
  | Error _ as error -> error
  | Ok (next_state, structure) ->
      let succeeded, output = execute structure in
      if succeeded then (
        session.compiler_state <- next_state;
        Ok output)
      else
        infrastructure_error
          (if String.equal output "" then "OCaml toplevel evaluation failed"
           else output)
