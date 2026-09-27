type value = {
  rendered : string;
  type_name : string;
}

type definition = {
  name : string;
  type_name : string;
}

type outcome =
  | Value of value
  | Definition of definition
  | Namespace of string
  | Summary of string

type evaluation = {
  outcome : outcome;
  namespace : string;
}

type completion = {
  candidate : string;
  type_name : string option;
}

type lookup = {
  name : string;
  namespace : string;
  type_name : string option;
  file : string option;
  line : int option;
  column : int option;
}

type t = {
  mutable compiler_state : Lg.Compiler.state;
  loaded_sources : (string, string) Hashtbl.t;
  toplevel_load_directories : string list;
  loaded_compilation_units : (string, unit) Hashtbl.t;
}

type saved_compilation_state = {
  target : Lg.Target.t;
  state : Lg.Compiler.state;
  packages : string list;
  ocaml_source : string;
  cache_key : string; [@warning "-69"]
}

let _runtime_anchor = Lg_runtime.Runtime_reference.of_value ()
let _clock_anchor = Lg_runtime.Runtime_time.now
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
    let message = Buffer.contents output in
    infrastructure_error
      (if String.equal message "" then "failed to prepare the OCaml toplevel"
       else message)

let valid_module_name name =
  let valid_initial = function 'A' .. 'Z' -> true | _ -> false in
  let valid_rest = function
    | 'A' .. 'Z' | 'a' .. 'z' | '0' .. '9' | '_' | '\'' -> true
    | _ -> false
  in
  String.length name > 0
  && valid_initial name.[0]
  && String.for_all valid_rest name

let source_word_char = function
  | 'A' .. 'Z' | 'a' .. 'z' | '0' .. '9' | '_' | '\'' -> true
  | _ -> false

let source_word_end source offset =
  let length = String.length source in
  let rec loop index =
    if index < length && source_word_char source.[index] then loop (index + 1)
    else index
  in
  loop offset
let installed_lg_root state_path =
  let state_directory = Filename.dirname state_path in
  if String.equal (Filename.basename state_directory) "stdlib" then
    let root = Filename.dirname state_directory in
    if Sys.file_exists (Filename.concat root "META") then Some root else None
  else None

let package_include_directories packages =
  packages
  |> List.concat_map (fun package ->
         match Lg.Ocaml_package.query package with
         | Ok directories -> directories
         | Error _ -> [])

let rec has_path_component component path =
  let basename = Filename.basename path in
  if String.equal basename component then true
  else
    let parent = Filename.dirname path in
    not (String.equal parent path) && has_path_component component parent

let is_native_toplevel_directory path =
  not (has_path_component "melange" path)

let add_toplevel_directory path =
  try Topdirs.dir_directory path
  with exn ->
    Printf.eprintf "lg-repl: skipping OCaml toplevel load path %s: %s\n%!" path
      (Printexc.to_string exn)

let configure_toplevel_load_path ~state_path ~packages =
  let state_directory = Filename.dirname state_path in
  let build_directory = Filename.dirname state_directory in
  let development_directories =
    [
      Filename.concat build_directory "vendor/rrbvec";
      Filename.concat build_directory "vendor/rrbvec/.rrbvec.objs/byte";
      Filename.concat build_directory "src";
      Filename.concat build_directory "src/.lg.objs/byte";
      Filename.concat build_directory "runtime";
      Filename.concat build_directory "runtime/.lg_runtime.objs/byte";
      Filename.concat build_directory
        "runtime_edn_backend_native/.lg_edn_backend_native.objs/byte";
    ]
  in
  let package_directories =
    package_include_directories
      ("lg.stdlib.native" :: "lg.runtime" :: "lg.edn-backend.native"
     :: "rrbvec" :: "str" :: packages)
  in
  let installed_directories =
    installed_lg_root state_path
    |> Option.map Lg.Ocaml_package.expand_include_directory
    |> Option.value ~default:[]
  in
  let artifact_directories =
    [
      Filename.concat state_directory "native";
      Filename.concat state_directory
        ".lg_compiled_stdlib_native.objs/byte";
    ]
  in
  let standard_library_directories =
    [
      Filename.concat Config.standard_library "str";
      Filename.concat Config.standard_library "unix";
    ]
  in
  development_directories @ artifact_directories @ package_directories
  @ standard_library_directories
  @ installed_directories
  |> List.filter (fun path ->
         is_native_toplevel_directory path
         && Sys.file_exists path && Sys.is_directory path)
  |> List.sort_uniq String.compare
  |> fun directories ->
  Lg.Ocaml_signature.add_include_dirs directories;
  List.iter add_toplevel_directory directories;
  directories

let namespace session = Lg.Compiler.source_scope session.compiler_state
let prompt session = namespace session ^ "=> "

let lg_source_file path =
  Filename.check_suffix path ".clj"
  || Filename.check_suffix path ".cljc"
  || Filename.check_suffix path ".cljs"
  || Filename.check_suffix path ".lgi"

let excluded_directory name =
  String.equal name "_build" || String.equal name "_opam"
  || String.equal name "duniverse" || String.equal name "node_modules"
  || String.equal name ".build"
  || String.equal name ".git"
  || (String.length name > 0 && name.[0] = '.')

let sorted_readdir path =
  try Sys.readdir path |> Array.to_list |> List.sort String.compare
  with Sys_error _ -> []

let rec lg_files path =
  if Sys.file_exists path && Sys.is_directory path then
    sorted_readdir path
    |> List.filter (fun name -> not (excluded_directory name))
    |> List.concat_map (fun name -> lg_files (Filename.concat path name))
  else if lg_source_file path then [ path ]
  else []

let rec find_repo_root_opt directory =
  if Sys.file_exists (Filename.concat directory "dune-project") then
    Some directory
  else
    let parent = Filename.dirname directory in
    if String.equal parent directory then None else find_repo_root_opt parent

let absolute_path path =
  if Filename.is_relative path then Filename.concat (Sys.getcwd ()) path else path

let source_needs_workspace_dependencies filename source =
  lg_source_file filename
  &&
  match filename with
  | "" | "<string>" | "<repl-query>" -> false
  | _ ->
      let trimmed = String.trim source in
      String.starts_with ~prefix:"(ns " trimmed
      || String.starts_with ~prefix:"(ns\n" trimmed

let read_source_file path =
  try Some (In_channel.with_open_bin path In_channel.input_all)
  with Sys_error _ -> None

let parse_source_forms source =
  match Lg.Lexer.tokenize source with
  | Error _ -> []
  | Ok tokens -> (
      match Lg.Parser.parse tokens with Error _ -> [] | Ok forms -> forms)

let source_token_char = function
  | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '-' | '_' | '.' | '/' -> true
  | _ -> false

let find_substring_from text pattern offset =
  let pattern_length = String.length pattern in
  let text_length = String.length text in
  let limit = text_length - pattern_length in
  let rec loop index =
    if index > limit then None
    else if String.sub text index pattern_length = pattern then Some index
    else loop (index + 1)
  in
  if pattern_length = 0 || offset > limit then None else loop offset

let skip_source_space source offset =
  let length = String.length source in
  let rec loop index =
    if index >= length then index
    else
      match source.[index] with
      | ' ' | '\n' | '\r' | '\t' | ',' -> loop (index + 1)
      | _ -> index
  in
  loop offset

let source_token_end source offset =
  let length = String.length source in
  let rec loop index =
    if index < length && source_token_char source.[index] then loop (index + 1)
    else index
  in
  loop offset

let cmo_filename_for_unit unit_name =
  String.uncapitalize_ascii unit_name ^ ".cmo"

let cma_filename_for_unit unit_name =
  String.uncapitalize_ascii unit_name ^ ".cma"

let same_filename left right =
  String.equal (String.lowercase_ascii left) (String.lowercase_ascii right)

let find_file_named directories filename =
  List.find_map
    (fun directory ->
      let path = Filename.concat directory filename in
      if Sys.file_exists path then Some path
      else
        try
          Sys.readdir directory
          |> Array.find_opt (fun entry -> same_filename entry filename)
          |> Option.map (Filename.concat directory)
        with Sys_error _ -> None)
    directories

let unique_strings values =
  List.fold_left
    (fun unique value ->
      if List.mem value unique then unique else unique @ [ value ])
    [] values

let package_directories_for_unit unit_name =
  unit_name |> String.lowercase_ascii |> Lg.Ocaml_package.query
  |> function Ok directories -> directories | Error _ -> []

let build_directory_unit_directories unit_name =
  let cmi_filename =
    Filename.remove_extension (cmo_filename_for_unit unit_name) ^ ".cmi"
  in
  let root =
    find_repo_root_opt (Sys.getcwd ())
    |> Option.map (fun root -> Filename.concat root "_build/default")
  in
  let rec scan directories path =
    if not (Sys.file_exists path && Sys.is_directory path) then directories
    else
      let entries =
        try Sys.readdir path |> Array.to_list with Sys_error _ -> []
      in
      let directories =
        if List.exists (fun entry -> same_filename entry cmi_filename) entries then
          path :: directories
        else directories
      in
      entries
      |> List.fold_left
           (fun directories entry ->
             let child = Filename.concat path entry in
             if
               Sys.file_exists child && Sys.is_directory child
               && (String.equal entry "byte"
                  || (String.length entry > 0 && not (entry.[0] = '.'))
                  || String.ends_with ~suffix:".objs" entry)
             then scan directories child
             else directories)
           directories
  in
  match root with None -> [] | Some root -> scan [] root

let relative_to_cwd path =
  let cwd = Sys.getcwd () in
  let prefix = cwd ^ Filename.dir_sep in
  if String.starts_with ~prefix path then
    String.sub path (String.length prefix) (String.length path - String.length prefix)
  else path

let rec ensure_directory path =
  if Sys.file_exists path then ()
  else (
    ensure_directory (Filename.dirname path);
    try Unix.mkdir path 0o755 with
    | Unix.Unix_error (Unix.EEXIST, _, _) when Sys.is_directory path -> ())

let write_file path contents =
  let output = open_out_bin path in
  Fun.protect
    ~finally:(fun () -> close_out_noerr output)
    (fun () -> output_string output contents)

let read_channel channel =
  let buffer = Buffer.create 128 in
  (try
     while true do
       Buffer.add_string buffer (input_line channel);
       Buffer.add_char buffer '\n'
     done
   with End_of_file -> ());
  Buffer.contents buffer

let exception_message exn =
  match exn with
  | Symtable.Error error ->
      Format.asprintf "%a" Symtable.report_error error
  | _ -> Printexc.to_string exn

let build_cmo_if_possible directories unit_name =
  let cmi_filename =
    Filename.remove_extension (cmo_filename_for_unit unit_name) ^ ".cmi"
  in
  match find_file_named directories cmi_filename with
  | None -> ()
  | Some cmi_path ->
      let cmo_path = Filename.remove_extension cmi_path ^ ".cmo" in
      let build_root =
        find_repo_root_opt (Sys.getcwd ())
        |> Option.map (fun root -> Filename.concat root "_build/default")
      in
      let in_build_root =
        match build_root with
        | None -> false
        | Some root ->
            String.starts_with ~prefix:(root ^ Filename.dir_sep) cmo_path
      in
      if (not (Sys.file_exists cmo_path)) && in_build_root then
        let target = relative_to_cwd cmo_path in
        let stdout, stdin, stderr =
          Unix.open_process_args_full "dune"
            [| "dune"; "build"; target |]
            (Unix.environment ())
        in
        let output = read_channel stdout in
        let error = read_channel stderr in
        (match Unix.close_process_full (stdout, stdin, stderr) with
        | WEXITED 0 -> ()
        | WEXITED status | WSIGNALED status | WSTOPPED status ->
            if Sys.getenv_opt "LG_REPL_LOAD_DEBUG" = Some "1" then
              Printf.eprintf
                "lg-repl: failed to build %s with dune (%d): %s%s\n%!"
                target status output error)

let library_archive_for_object_directory directory =
  let byte_directory = Filename.basename directory in
  let object_directory = Filename.dirname directory in
  let object_basename = Filename.basename object_directory in
  if
    String.equal byte_directory "byte"
    && String.starts_with ~prefix:"." object_basename
    && String.ends_with ~suffix:".objs" object_basename
  then
    let library_name =
      String.sub object_basename 1
        (String.length object_basename - String.length ".objs" - 1)
    in
    Some (Filename.concat (Filename.dirname object_directory) (library_name ^ ".cma"))
  else None

let build_archive_if_possible archive_path =
  if Sys.file_exists archive_path then ()
  else
    let build_root =
      find_repo_root_opt (Sys.getcwd ())
      |> Option.map (fun root -> Filename.concat root "_build/default")
    in
    match build_root with
    | Some root when String.starts_with ~prefix:(root ^ Filename.dir_sep) archive_path ->
        let target = relative_to_cwd archive_path in
        let stdout, stdin, stderr =
          Unix.open_process_args_full "dune"
            [| "dune"; "build"; target |]
            (Unix.environment ())
        in
        let output = read_channel stdout in
        let error = read_channel stderr in
        (match Unix.close_process_full (stdout, stdin, stderr) with
        | WEXITED 0 -> ()
        | WEXITED status | WSIGNALED status | WSTOPPED status ->
            if Sys.getenv_opt "LG_REPL_LOAD_DEBUG" = Some "1" then
              Printf.eprintf
                "lg-repl: failed to build %s with dune (%d): %s%s\n%!"
                target status output error)
    | _ -> ()

let archive_for_unit_directories directories =
  directories
  |> List.filter_map library_archive_for_object_directory
  |> List.filter (fun archive_path ->
         build_archive_if_possible archive_path;
         Sys.file_exists archive_path)

let undefined_compilation_unit message =
  let marker = "Reference to undefined compilation unit" in
  match find_substring_from message marker 0 with
  | None -> None
  | Some marker_start ->
      let start = marker_start + String.length marker in
      let start = skip_source_space message start in
      if start >= String.length message then None
      else
        let quote =
          match message.[start] with
          | '\'' | '`' -> Some message.[start]
          | _ -> None
        in
        let closes_quote opener ch =
          Char.equal ch opener || (Char.equal opener '`' && Char.equal ch '\'')
        in
        let token_start = if Option.is_some quote then start + 1 else start in
        let rec token_end index =
          if index >= String.length message then index
          else
            match quote with
            | Some quote when closes_quote quote message.[index] -> index
            | Some _ -> token_end (index + 1)
            | None -> (
                match message.[index] with
                | ' ' | '\n' | '\t' | '\r' | '.' -> index
                | _ -> token_end (index + 1))
        in
        let token_end = token_end token_start in
        if token_end > token_start then
          Some (String.sub message token_start (token_end - token_start))
        else None

let load_compilation_unit directories loaded_units unit_name =
  let rec load depth unit_name =
    if Hashtbl.mem loaded_units unit_name then true
    else if depth <= 0 then false
    else (
      let directories =
        directories @ build_directory_unit_directories unit_name
        @ package_directories_for_unit unit_name
        |> unique_strings
      in
      let load_target =
        match find_file_named directories (cmo_filename_for_unit unit_name) with
        | Some cmo_path -> Some cmo_path
        | None -> (
            build_cmo_if_possible directories unit_name;
            match find_file_named directories (cmo_filename_for_unit unit_name) with
            | Some cmo_path -> Some cmo_path
            | None -> (
            match find_file_named directories (cma_filename_for_unit unit_name) with
            | Some cma_path -> Some cma_path
            | None ->
                List.find_opt Sys.file_exists
                  (archive_for_unit_directories directories)))
      in
      match load_target with
      | None ->
          if Sys.getenv_opt "LG_REPL_LOAD_DEBUG" = Some "1" then
            Printf.eprintf
              "lg-repl: no bytecode target for %s in %d directories\n%!"
              unit_name (List.length directories);
          false
      | Some bytecode_path ->
          add_toplevel_directory (Filename.dirname bytecode_path);
          let output = Buffer.create 128 in
          let formatter = Format.formatter_of_buffer output in
          try
            Topdirs.dir_load formatter bytecode_path;
            Format.pp_print_flush formatter ();
            Hashtbl.replace loaded_units unit_name ();
            true
          with exn ->
            Format.pp_print_flush formatter ();
            let message =
              String.concat ""
                [ exception_message exn; Buffer.contents output ]
            in
            (match undefined_compilation_unit message with
            | Some dependency when load (depth - 1) dependency ->
                load (depth - 1) unit_name
            | _ ->
                if Sys.getenv_opt "LG_REPL_LOAD_DEBUG" = Some "1" then
                  Printf.eprintf
                    "lg-repl: failed to load %s from %s: %s%s\n%!" unit_name
                    bytecode_path (exception_message exn)
                    (Buffer.contents output);
                false))
  in
  load 16 unit_name

let bootstrap_module_from_source source =
  let rec search offset =
    match find_substring_from source "module" offset with
    | None -> None
    | Some module_start ->
        let before_ok =
          module_start = 0 || not (source_word_char source.[module_start - 1])
        in
        let after = module_start + String.length "module" in
        let after_ok =
          after >= String.length source || not (source_word_char source.[after])
        in
        if before_ok && after_ok then
          let name_start = skip_source_space source after in
          let name_end = source_word_end source name_start in
          if name_end > name_start then
            let name = String.sub source name_start (name_end - name_start) in
            if valid_module_name name then Some name else search name_end
          else search after
        else search after
  in
  search 0

let module_name_from_state_path state_path =
  let basename = Filename.basename state_path in
  let stem =
    if Filename.check_suffix basename ".state" then
      Filename.chop_suffix basename ".state"
    else Filename.remove_extension basename
  in
  let module_name =
    Lg.Names.module_segment_to_ocaml stem
  in
  if valid_module_name module_name then Some module_name else None

let execute ?resolve_unit structure =
  let output = Buffer.create 256 in
  let formatter = Format.formatter_of_buffer output in
  let rec attempt remaining_attempts =
    match Toploop.execute_phrase false formatter (Parsetree.Ptop_def structure) with
    | exception exn ->
        Format.pp_print_flush formatter ();
        let message = Buffer.contents output in
        Buffer.clear output;
        let detail = exception_message exn in
        let combined =
          String.concat ": "
            (List.filter
               (fun part -> not (String.equal part ""))
               [ detail; message ])
        in
        (match (resolve_unit, undefined_compilation_unit combined) with
        | Some resolve_unit, Some unit_name
          when remaining_attempts > 0 && resolve_unit unit_name ->
            attempt (remaining_attempts - 1)
        | _ ->
            infrastructure_error
              (String.concat ": "
                 (List.filter
                    (fun part -> not (String.equal part ""))
                    [ "OCaml toplevel evaluation failed"; combined ])))
    | succeeded ->
        Format.pp_print_flush formatter ();
        if succeeded then Ok ()
        else
          let message = Buffer.contents output in
          Buffer.clear output;
          (match (resolve_unit, undefined_compilation_unit message) with
          | Some resolve_unit, Some unit_name
            when remaining_attempts > 0 && resolve_unit unit_name ->
              attempt (remaining_attempts - 1)
          | _ ->
              infrastructure_error
                (if String.equal message "" then "OCaml toplevel evaluation failed"
                 else message))
  in
  attempt 16

let open_precompiled_module module_name =
  if not (valid_module_name module_name) then
    infrastructure_error ("invalid bootstrap module " ^ module_name)
  else
    let lexbuf = Lexing.from_string ("open " ^ module_name ^ ";;") in
    Location.init lexbuf "<repl-bootstrap>";
    let phrase = !Toploop.parse_toplevel_phrase lexbuf in
    match phrase with
    | exception exn ->
        infrastructure_error
          ("failed to parse the REPL bootstrap: " ^ Printexc.to_string exn)
    | phrase -> (
        match phrase with
        | Parsetree.Ptop_def structure -> execute structure
        | Parsetree.Ptop_dir _ ->
            infrastructure_error "invalid REPL bootstrap phrase")

let repl_bytecode_cache_directory () =
  match Sys.getenv_opt "LG_CACHE_DIR" with
  | Some path -> Filename.concat path "repl-bytecode"
  | None ->
      let base_directory =
        Option.value (find_repo_root_opt (Sys.getcwd ())) ~default:(Sys.getcwd ())
      in
      Filename.concat base_directory ".lg-cache/repl-bytecode"

let compile_saved_source_to_cmo ~state_path ~include_directories ~module_name
    source =
  let key =
    Digest.string
      (String.concat "\000"
         (state_path :: source :: include_directories))
    |> Digest.to_hex
  in
  let directory = Filename.concat (repl_bytecode_cache_directory ()) key in
  ensure_directory directory;
  let stem = String.uncapitalize_ascii module_name in
  let source_path = Filename.concat directory (stem ^ ".ml") in
  let cmo_path = Filename.concat directory (stem ^ ".cmo") in
  if not (Sys.file_exists cmo_path) then (
    write_file source_path source;
    let command =
      [
        "ocamlc";
        "-g";
      ]
      @ List.concat_map (fun path -> [ "-I"; path ]) include_directories
      @ [ "-c"; source_path; "-o"; cmo_path ]
      |> List.map Filename.quote |> String.concat " "
    in
    match Sys.command command with
    | 0 -> ()
    | status ->
        if Sys.getenv_opt "LG_REPL_LOAD_DEBUG" = Some "1" then
          Printf.eprintf
            "lg-repl: failed to compile saved state bytecode (%d): %s\n%!"
            status command);
  if Sys.file_exists cmo_path then Some (directory, cmo_path) else None

let create_from_state ~include_directories ~state_path ~bootstrap_module =
  let timing_enabled = Sys.getenv_opt "LG_REPL_STARTUP_TIMING" = Some "1" in
  let started_at = Unix.gettimeofday () in
  let mark label =
    if timing_enabled then
      Printf.eprintf "lg-repl startup %s %.3fs\n%!" label
        (Unix.gettimeofday () -. started_at)
  in
  match Lg.Compiler_artifact.read ~kind:"saved-state" ~path:state_path with
  | Error message -> infrastructure_error message
  | Ok saved ->
      mark "read-state";
      let saved = (saved : saved_compilation_state) in
      let bootstrap_module =
        match module_name_from_state_path state_path with
        | Some module_name -> module_name
        | None ->
            bootstrap_module_from_source saved.ocaml_source
            |> Option.value ~default:bootstrap_module
      in
      if saved.target <> Lg.Target.Native then
        infrastructure_error "REPL requires a Native stdlib state"
      else (
        let configured_directories =
          configure_toplevel_load_path ~state_path ~packages:saved.packages
        in
        mark "configure-load-path";
        let include_directories =
          include_directories
          |> List.filter (fun path -> Sys.file_exists path && Sys.is_directory path)
        in
        List.iter add_toplevel_directory include_directories;
        let toplevel_load_directories =
          configured_directories @ include_directories
          |> List.sort_uniq String.compare
        in
        let bootstrap_cmi =
          Filename.remove_extension (cmo_filename_for_unit bootstrap_module)
          ^ ".cmi"
        in
        let toplevel_load_directories =
          match find_file_named toplevel_load_directories bootstrap_cmi with
          | Some _ -> toplevel_load_directories
          | None -> (
              match
                compile_saved_source_to_cmo ~state_path
                  ~include_directories:toplevel_load_directories
                  ~module_name:bootstrap_module saved.ocaml_source
              with
              | None -> toplevel_load_directories
              | Some (directory, _cmo_path) ->
                  add_toplevel_directory directory;
                  Lg.Ocaml_signature.add_include_dirs [ directory ];
                  directory :: toplevel_load_directories
                  |> List.sort_uniq String.compare)
        in
        mark "prepare-bootstrap-bytecode";
        match
          Lg.Compiler.restore_ocaml_environment ~target:Lg.Target.Native
            ~packages:saved.packages saved.state
            [ ("open " ^ bootstrap_module, None) ]
        with
        | Error _ as error -> error
        | Ok compiler_state -> (
            mark "restore-compiler-env";
            match prepare_toplevel () with
            | Error _ as error -> error
            | Ok () ->
                mark "prepare-toplevel";
                let loaded_compilation_units = Hashtbl.create 32 in
                let resolve_unit =
                  load_compilation_unit toplevel_load_directories
                    loaded_compilation_units
                in
                let bootstrap_ready = resolve_unit bootstrap_module in
                let opened =
                  if bootstrap_ready then open_precompiled_module bootstrap_module
                  else
                    infrastructure_error
                      ("unable to load REPL bootstrap module "
                      ^ bootstrap_module)
                in
                mark "open-bootstrap";
                Result.map
                  (fun () ->
                    {
                      compiler_state =
                        Lg.Compiler.with_source_scope "user" compiler_state;
                      loaded_sources = Hashtbl.create 32;
                      toplevel_load_directories;
                      loaded_compilation_units;
                    })
                  opened))

let create_from_stdlib ~state_path =
  create_from_state ~include_directories:[] ~state_path
    ~bootstrap_module:"Lg_stdlib_native"

let source_namespace_lexical source =
  match find_substring_from source "(ns" 0 with
  | None -> None
  | Some ns_start ->
      let token_start = skip_source_space source (ns_start + 3) in
      let token_end = source_token_end source token_start in
      if token_end > token_start then
        Some (String.sub source token_start (token_end - token_start))
      else None

let source_namespace source =
  let open Lg.Ast in
  parse_source_forms source
  |> List.find_map (function
       | FList (FSymbol "ns" :: FSymbol namespace_name :: _) ->
           Some namespace_name
       | _ -> None)
  |> function
  | Some _ as namespace -> namespace
  | None -> source_namespace_lexical source

let namespace_require_keyword = function
  | Lg.Ast.FKeyword "require" | FKeyword ":require" | FSymbol ":require"
  | FSymbol "require" ->
      true
  | _ -> false

let namespace_require_reference = function
  | Lg.Ast.FVector (FSymbol namespace_name :: _)
  | FList (FSymbol namespace_name :: _) ->
      Some namespace_name
  | FSymbol namespace_name -> Some namespace_name
  | _ -> None

let source_required_namespaces source =
  let open Lg.Ast in
  let clause_requires = function
    | FList (keyword :: specs) when namespace_require_keyword keyword ->
        List.filter_map namespace_require_reference specs
    | _ -> []
  in
  parse_source_forms source
  |> List.concat_map (function
       | FList (FSymbol "ns" :: _namespace :: clauses) ->
           List.concat_map clause_requires clauses
       | FList (FSymbol "require" :: specs) ->
           List.filter_map namespace_require_reference specs
       | _ -> [])
  |> fun parsed ->
  if parsed <> [] then parsed
  else
    let length = String.length source in
    let rec vectors limit offset namespaces =
      match find_substring_from source "[" offset with
      | None -> namespaces
      | Some vector_start when vector_start >= limit -> namespaces
      | Some vector_start ->
          let token_start = skip_source_space source (vector_start + 1) in
          let token_end = source_token_end source token_start in
          let namespaces =
            if token_end > token_start then
              String.sub source token_start (token_end - token_start)
              :: namespaces
            else namespaces
          in
          vectors limit token_end namespaces
    in
    let rec requires offset namespaces =
      match find_substring_from source ":require" offset with
      | None -> List.rev namespaces
      | Some require_start ->
          let next = require_start + String.length ":require" in
          let limit =
            find_substring_from source "\n\n" next
            |> Option.value ~default:length
          in
          requires next (vectors limit next namespaces)
    in
    requires 0 []

let compile_source_list compiler_state sources =
  let rec compile compiler_state structures count = function
    | [] -> Ok (compiler_state, List.rev structures |> List.concat, count)
    | (path, source) :: rest -> (
        match
          Lg.Compiler.compile_chunk_parsetree_with_filename ~filename:path
            compiler_state source
        with
        | Error _ as error -> error
        | Ok (candidate_state, structure) ->
            compile candidate_state (structure :: structures) (count + 1) rest)
  in
  compile compiler_state [] 0 sources

let eval_source_list session sources =
  match compile_source_list session.compiler_state sources with
  | Error _ as error -> error
  | Ok (candidate_state, structure, file_count) -> (
      let resolve_unit =
        load_compilation_unit session.toplevel_load_directories
          session.loaded_compilation_units
      in
      match execute ~resolve_unit structure with
      | Error _ as error -> error
      | Ok () ->
          session.compiler_state <- candidate_state;
          List.iter
            (fun (path, source) ->
              Hashtbl.replace session.loaded_sources path source)
            sources;
          Ok file_count)

let workspace_sources_for_file ~filename ~source =
  let filename = absolute_path filename in
  match find_repo_root_opt (Filename.dirname filename) with
  | None -> None
  | Some root ->
      let sources =
        lg_files root
        |> List.filter_map (fun path ->
               if String.equal path filename then None
               else Option.map (fun source -> (path, source)) (read_source_file path))
      in
      Some (filename, (filename, source) :: sources)

let ordered_dependency_sources ~filename sources =
  let source_by_file =
    sources
    |> List.to_seq
    |> Hashtbl.of_seq
  in
  let namespace_provider =
    sources
    |> List.filter_map (fun (path, source) ->
           Option.map (fun namespace -> (namespace, path)) (source_namespace source))
    |> List.to_seq
    |> Hashtbl.of_seq
  in
  let visited = Hashtbl.create 32 in
  let rec visit path ordered =
    if Hashtbl.mem visited path || String.equal path filename then ordered
    else (
      Hashtbl.add visited path ();
      let source = Hashtbl.find source_by_file path in
      let ordered =
        source_required_namespaces source
        |> List.fold_left
             (fun ordered namespace ->
               match Hashtbl.find_opt namespace_provider namespace with
               | Some dependency -> visit dependency ordered
               | None -> ordered)
             ordered
      in
      (path, source) :: ordered)
  in
  let current_source = Hashtbl.find source_by_file filename in
  source_required_namespaces current_source
  |> List.fold_left
       (fun ordered namespace ->
         match Hashtbl.find_opt namespace_provider namespace with
         | Some dependency -> visit dependency ordered
         | None -> ordered)
       []
  |> List.rev

let eval_workspace_dependencies session ~filename source =
  if source_needs_workspace_dependencies filename source then
    match workspace_sources_for_file ~filename ~source with
    | None -> Ok 0
    | Some (filename, sources) ->
        if Sys.getenv_opt "LG_REPL_WORKSPACE_DEBUG" = Some "1" then (
          Printf.eprintf "lg-repl workspace filename=%s sources=%d requires=[%s]\n%!"
            filename (List.length sources)
            (String.concat "," (source_required_namespaces source));
          sources
          |> List.filter_map (fun (path, source) ->
                 Option.map
                   (fun namespace -> namespace ^ "=" ^ path)
                   (source_namespace source))
          |> String.concat "\n"
          |> Printf.eprintf "lg-repl workspace namespaces:\n%s\n%!");
        let dependency_sources =
          ordered_dependency_sources ~filename sources
          |> List.filter (fun (path, source) ->
                 (not (String.equal path filename))
                 &&
                 match Hashtbl.find_opt session.loaded_sources path with
                 | Some loaded_source when String.equal loaded_source source ->
                     false
                 | Some _ | None -> true)
        in
        if dependency_sources = [] then Ok 0
        else eval_source_list session dependency_sources
  else Ok 0

let eval ?(filename = "<string>") session source =
  match eval_workspace_dependencies session ~filename source with
  | Error _ as error -> error
  | Ok _ -> (
      match
        Lg.Compiler.compile_repl_form ~filename session.compiler_state source
      with
  | Error _ as error -> error
  | Ok (candidate_state, compilation) ->
      Lg_runtime.Runtime_repl.clear ();
      let resolve_unit =
        load_compilation_unit session.toplevel_load_directories
          session.loaded_compilation_units
      in
      (match execute ~resolve_unit compilation.structure with
      | Error _ as error -> error
      | Ok () ->
          let outcome =
            match compilation.kind with
            | Lg.Compiler.Repl_value -> (
                match Lg_runtime.Runtime_repl.take () with
                | Some value ->
                    Ok
                      (Value
                         {
                           rendered = value.rendered;
                           type_name = value.type_name;
                         })
                | None -> infrastructure_error "REPL value was not published")
            | Lg.Compiler.Repl_definition definition ->
                Ok
                  (Definition
                     {
                       name = definition.name;
                       type_name = definition.type_name;
                     })
            | Lg.Compiler.Repl_namespace namespace -> Ok (Namespace namespace)
            | Lg.Compiler.Repl_summary summary -> Ok (Summary summary)
          in
          Result.map
            (fun outcome ->
              session.compiler_state <- candidate_state;
              { outcome; namespace = namespace session })
            outcome)
      )

let load_source ?(filename = "<string>") session source =
  match eval_workspace_dependencies session ~filename source with
  | Error _ as error -> error
  | Ok _ -> (
      match eval_source_list session [ (filename, source) ] with
      | Error _ as error -> error
      | Ok file_count ->
          Ok
            {
              outcome =
                Summary
                  (Printf.sprintf "Loaded %d file%s" file_count
                     (if file_count = 1 then "" else "s"));
              namespace = namespace session;
            })

let eval_files session paths =
  paths
  |> List.map (fun path ->
         match read_source_file path with
         | Some source -> Ok (path, source)
         | None -> infrastructure_error ("unable to read " ^ path))
  |> List.fold_left
       (fun result source ->
         match (result, source) with
         | Error _ as error, _ | _, (Error _ as error) -> error
         | Ok sources, Ok source -> Ok (source :: sources))
       (Ok [])
  |> Result.map List.rev
  |> fun sources -> Result.bind sources (eval_source_list session)

let type_of session source =
  Lg.Compiler.infer_repl_type session.compiler_state source

let analyze_symbol session symbol =
  Lg.Language_service.analyze_from_state ~filename:"<repl-query>"
    session.compiler_state symbol

let symbol_name symbol =
  match String.rindex_opt symbol '/' with
  | Some index when index + 1 < String.length symbol ->
      String.sub symbol (index + 1) (String.length symbol - index - 1)
  | Some _ | None -> symbol

let symbol_namespace session symbol =
  match String.rindex_opt symbol '/' with
  | Some index when index > 0 -> String.sub symbol 0 index
  | Some _ | None -> namespace session

let source_location location =
  let position = location.Location.loc_start in
  let file =
    match position.Lexing.pos_fname with
    | "" | "<string>" | "<repl-query>" -> None
    | filename -> Some filename
  in
  let line = if location.Location.loc_ghost then None else Some position.pos_lnum in
  let column =
    if location.Location.loc_ghost then None
    else Some (position.pos_cnum - position.pos_bol + 1)
  in
  (file, line, column)

let lookup session symbol =
  match analyze_symbol session symbol with
  | Error _ -> Ok None
  | Ok analysis ->
      let type_name =
        match type_of session symbol with
        | Ok type_name -> Some type_name
        | Error _ ->
            Lg.Language_service.hover analysis ~offset:0
            |> Option.map (fun hover -> hover.Lg.Language_service.contents)
      in
      let location = Lg.Language_service.definition analysis ~offset:0 in
      Ok
        (match (type_name, location) with
      | None, None -> None
      | _ ->
          let file, line, column =
            location
            |> Option.map source_location
            |> Option.value ~default:(None, None, None)
          in
          Some
            {
              name = symbol_name symbol;
              namespace = symbol_namespace session symbol;
              type_name;
              file;
              line;
              column;
            })

let completions session prefix =
  let limit = if String.length prefix < 2 then 256 else 1024 in
  Lg.Language_service.repl_completions ~prefix ~limit session.compiler_state
  |> List.map (fun (item : Lg.Language_service.completion_item) ->
         { candidate = item.label; type_name = Some item.detail })
  |> List.sort_uniq (fun left right -> String.compare left.candidate right.candidate)
  |> Result.ok
