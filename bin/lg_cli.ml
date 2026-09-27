let usage () =
  prerr_endline
    "Usage: lg <input.cljc> [-o output.ml] | --interface <input.cljc> [-o \
     output.mli] | --run <input.cljc> | --compile-files <input.cljc>... -o \
     output.ml | --compile-files-state <state> <input.cljc>... -o output.ml | \
     --compile-files-from <state> [--emit-state <output-state>] \
     <input.cljc>... -o output.ml | \
     --compile-files-chunk-from <state> [--prefix-interface <prefix.cmi>] \
     [--emit-state <output-state>] <input.cljc>... -o output.ml | \
     --compile-files-from-state <input-state> <output-state> <input.cljc>... -o \
     output.ml | \
     --compile-chunk-from <state> <input.cljc> [-o output.ml] | \
     --compile-chunk-state <input-state> <output-state> <input.cljc> [-o \
     output.ml] | \
     --run-from <state> <implementation.ml> <input.cljc> | \
     --run-files <input.cljc>... | \
     --run-files-from <state> <implementation.ml> <input.cljc>... | repl \
     [--state <lg_stdlib_native.state>] | mobile build [options] [paths...] | \
     test [paths...] | --lsp [--state <saved-state>]. \
     Batch commands default to all .clj, .cljc, .cljs, .lgi, and paired .mli files in the \
     current directory.";
  exit 2

let tune_compiler_gc () =
  let control = Gc.get () in
  let minor_heap_size = 16 * 1024 * 1024 in
  if control.minor_heap_size < minor_heap_size || control.space_overhead < 200
  then
    Gc.set
      {
        control with
        minor_heap_size = max control.minor_heap_size minor_heap_size;
        space_overhead = max control.space_overhead 200;
      }

let read_file path =
  let ic = open_in path in
  Fun.protect
    ~finally:(fun () -> close_in_noerr ic)
    (fun () ->
      let length = in_channel_length ic in
      really_input_string ic length)

let source_extensions = [ ".mli"; ".lgi"; ".clj"; ".cljc"; ".cljs" ]

let sorted_readdir directory =
  try Sys.readdir directory |> Array.to_list |> List.sort String.compare
  with Sys_error _ -> []

let matching_lg_source path =
  let stem = Lg.Ocaml_interface.source_stem path in
  [ ".cljc"; ".clj"; ".cljs" ]
  |> List.find_map (fun extension ->
       let candidate = stem ^ extension in
       if Sys.file_exists candidate then Some candidate else None)

let has_source_extension path =
  if Filename.check_suffix path ".mli" then Option.is_some (matching_lg_source path)
  else List.exists (Filename.check_suffix path) source_extensions

let expand_input_path path =
  if Sys.file_exists path && Sys.is_directory path then
    Sys.readdir path |> Array.to_list |> List.sort String.compare
    |> List.map (Filename.concat path)
    |> List.filter has_source_extension
  else if Sys.file_exists path then
    let interface = Lg.Ocaml_interface.source_stem path ^ ".mli" in
    if not (Lg.Ocaml_interface.is_interface path)
       && has_source_extension path && Sys.file_exists interface
    then [ interface; path ] else [ path ]
  else
    let sources =
      source_extensions
      |> List.map (fun extension -> path ^ extension)
      |> List.filter Sys.file_exists
    in
    if sources = [] then [ path ] else sources

let rec source_files_under directory =
  if not (Sys.file_exists directory && Sys.is_directory directory) then []
  else
    Sys.readdir directory |> Array.to_list |> List.sort String.compare
    |> List.concat_map (fun name ->
           let path = Filename.concat directory name in
           if Sys.file_exists path && Sys.is_directory path then
             source_files_under path
           else if has_source_extension path then [ path ]
           else [])

let expand_test_input_path path =
  if Sys.file_exists path && Sys.is_directory path then source_files_under path
  else expand_input_path path

let expand_test_input_paths paths =
  List.concat_map expand_test_input_path paths

let unique_preserving_order values =
  let rec loop seen values =
    match values with
    | [] -> List.rev seen
    | value :: rest ->
        if List.mem value seen then loop seen rest
        else loop (value :: seen) rest
  in
  loop [] values

let canonical_existing_path path =
  try Unix.realpath path with Unix.Unix_error _ -> path

let unique_paths_preserving_order paths =
  let rec loop seen result = function
    | [] -> List.rev result
    | path :: rest ->
        let canonical = canonical_existing_path path in
        if List.mem canonical seen then loop seen result rest
        else loop (canonical :: seen) (path :: result) rest
  in
  loop [] [] paths

let has_pending_interface state path =
  List.mem_assoc (Lg.Ocaml_interface.source_stem path)
    state.Lg.Toolchain.pending_interfaces

let expand_input_paths ?(state = Lg.Compiler.empty_state) paths =
  let paths = if paths = [] then [ "." ] else paths in
  List.concat_map expand_input_path paths
  |> unique_paths_preserving_order
  |> List.filter (fun path ->
       not (Filename.check_suffix path ".mli" && has_pending_interface state path)
       || List.mem path paths)

type source_namespace_info = {
  path : string;
  namespace : string option;
  requires : string list;
}

let rec source_namespace_info path =
  if Filename.check_suffix path ".mli" then
    match matching_lg_source path with
    | Some implementation -> { (source_namespace_info implementation) with path }
    | None -> { path; namespace = None; requires = [] }
  else
  let source = read_file path in
  match Lg.Lexer.tokenize source with
  | Error _ -> { path; namespace = None; requires = [] }
  | Ok tokens -> (
      match Lg.Parser.parse tokens with
      | Error _ -> { path; namespace = None; requires = [] }
      | Ok forms ->
          let namespace =
            List.find_map
              (function
                | Lg.Ast.FList (FSymbol "ns" :: FSymbol namespace :: _) ->
                    Some namespace
                | _ -> None)
              forms
          in
          let require_keyword = function
            | Lg.Ast.FKeyword "require" | FKeyword ":require"
            | FSymbol ":require" | FSymbol "require" ->
                true
            | _ -> false
          in
          let add_require requires = function
            | Lg.Ast.FVector (FSymbol namespace :: _)
            | FList (FSymbol namespace :: _)
            | FSymbol namespace ->
                namespace :: requires
            | _ -> requires
          in
          let requires =
            forms
            |> List.fold_left
                 (fun requires -> function
                   | Lg.Ast.FList (FSymbol "ns" :: _namespace :: clauses) ->
                       List.fold_left
                         (fun requires -> function
                           | Lg.Ast.FList (keyword :: specs)
                             when require_keyword keyword ->
                               List.fold_left add_require requires specs
                           | _ -> requires)
                         requires clauses
                   | _ -> requires)
                 []
            |> List.rev |> List.sort_uniq String.compare
          in
          { path; namespace; requires })

let project_namespace namespace =
  not
    (String.starts_with ~prefix:"ocaml." namespace
    || String.starts_with ~prefix:"clojure." namespace
    || String.starts_with ~prefix:"cljs." namespace)

let ocaml_namespace_module_root namespace =
  let prefix = "ocaml." in
  if String.starts_with ~prefix namespace then
    let rest =
      String.sub namespace (String.length prefix)
        (String.length namespace - String.length prefix)
    in
    match String.split_on_char '.' rest with
    | module_name :: _ when module_name <> "" -> Some module_name
    | _ -> None
  else None

let local_source_index paths =
  paths |> List.map source_namespace_info
  |> List.filter_map (fun info ->
         Option.map (fun namespace -> (namespace, info)) info.namespace)

let required_project_sources source_index roots =
  let table = Hashtbl.create 64 in
  List.iter
    (fun (namespace, info) ->
      let existing = Hashtbl.find_opt table namespace |> Option.value ~default:[] in
      Hashtbl.replace table namespace (existing @ [ info ]))
    source_index;
  let rec visit namespace (seen, paths) =
    if List.mem namespace seen || not (project_namespace namespace) then
      (seen, paths)
    else
      match Hashtbl.find_opt table namespace with
      | None -> (namespace :: seen, paths)
      | Some infos ->
          List.fold_left
            (fun (seen, paths) info ->
              let seen, paths =
                List.fold_left
                  (fun state required -> visit required state)
                  (seen, paths) info.requires
              in
              (seen, info.path :: paths))
            (namespace :: seen, paths) infos
  in
  let _seen, paths =
    List.fold_left
      (fun state namespace -> visit namespace state)
      ([], []) roots
  in
  List.rev paths |> unique_preserving_order

let order_paths_by_namespace_dependencies paths =
  let infos = List.map source_namespace_info paths in
  let interface_first infos =
    List.sort
      (fun left right ->
        let left_rank =
          if Lg.Ocaml_interface.is_interface left.path then 0 else 1
        in
        let right_rank =
          if Lg.Ocaml_interface.is_interface right.path then 0 else 1
        in
        match Int.compare left_rank right_rank with
        | 0 -> String.compare left.path right.path
        | order -> order)
      infos
  in
  let table = Hashtbl.create 64 in
  List.iter
    (fun info ->
      match info.namespace with
      | Some namespace ->
          let existing =
            Hashtbl.find_opt table namespace |> Option.value ~default:[]
          in
          Hashtbl.replace table namespace (interface_first (info :: existing))
      | None -> ())
    infos;
  let namespace_requires = Hashtbl.create 64 in
  Hashtbl.iter
    (fun namespace infos ->
      let requires =
        infos
        |> List.concat_map (fun info -> info.requires)
        |> List.sort_uniq String.compare
      in
      Hashtbl.replace namespace_requires namespace requires)
    table;
  let local_namespace namespace = Hashtbl.mem table namespace in
  let rec visit visiting visited ordered info =
    if List.mem info.path visited then (visited, ordered)
    else if List.mem info.path visiting then (visited, info.path :: ordered)
    else
      let visiting = info.path :: visiting in
      let visited, ordered =
        match info.namespace with
        | None -> (visited, ordered)
        | Some namespace when Lg.Ocaml_interface.is_interface info.path ->
            let _ = namespace in
            (visited, ordered)
        | Some namespace ->
            Hashtbl.find table namespace
            |> List.filter (fun sibling ->
                   Lg.Ocaml_interface.is_interface sibling.path
                   && sibling.path <> info.path)
            |> List.fold_left
                 (fun (visited, ordered) interface_info ->
                   visit visiting visited ordered interface_info)
                 (visited, ordered)
      in
      let visited, ordered =
        (match info.namespace with
        | Some namespace -> (
            match Hashtbl.find_opt namespace_requires namespace with
            | Some requires -> requires
            | None -> info.requires)
        | None -> info.requires)
        |> List.filter local_namespace
        |> List.fold_left
             (fun (visited, ordered) namespace ->
               Hashtbl.find table namespace
               |> List.fold_left
                    (fun (visited, ordered) dependency ->
                      visit visiting visited ordered dependency)
                    (visited, ordered))
             (visited, ordered)
      in
      (info.path :: visited, info.path :: ordered)
  in
  let _visited, ordered =
    List.fold_left
      (fun (visited, ordered) info -> visit [] visited ordered info)
      ([], []) infos
  in
  List.rev ordered |> unique_preserving_order
  |> List.stable_sort (fun left right ->
       Bool.compare (not (Filename.check_suffix left ".mli"))
         (not (Filename.check_suffix right ".mli")))

let required_ocaml_module_roots sources =
  sources
  |> List.concat_map (fun path -> (source_namespace_info path).requires)
  |> List.filter_map ocaml_namespace_module_root
  |> List.sort_uniq String.compare

let directory_contains_file suffix directory =
  Sys.file_exists directory && Sys.is_directory directory
  && sorted_readdir directory |> List.exists (String.ends_with ~suffix)

let object_include_dirs object_dir =
  let public_cmi = Filename.concat object_dir "public_cmi" in
  let byte = Filename.concat object_dir "byte" in
  if directory_contains_file ".cmi" public_cmi then [ public_cmi ]
  else if directory_contains_file ".cmi" byte then [ byte ]
  else []

let write_output output_path contents =
  match output_path with
  | None -> print_string contents
  | Some path ->
      let oc = open_out path in
      Fun.protect
        ~finally:(fun () -> close_out_noerr oc)
        (fun () -> output_string oc contents)

type cached_prefix_output = {
  source_packages : string list;
  compilation : Lg.Compiler.compilation;
  has_state : bool;
}

type cached_prefix_state = {
  state : Lg.Compiler.state;
}

type cached_prefix_write = {
  write_source_packages : string list;
  write_compilation : Lg.Compiler.compilation;
  write_state : Lg.Compiler.state;
}

type cached_runner_manifest = {
  runner_key : string;
  runner_executable : string;
}

type compiler_state =
  | Live of Lg.Compiler.state
  | Replayed of Lg.Compiler.state
  | Cached of string

type saved_compilation_state = {
  target : Lg.Target.t;
  state : Lg.Compiler.state;
  packages : string list;
  ocaml_source : string;
  (* Marshaled OCaml signatures of the chunk compilations that produced
     [ocaml_source], in order. Restoring adds each to a fresh env instead
     of re-typechecking the prefix source. *)
  ocaml_signatures : string list;
  (* Deterministic provenance key of the compilation that produced this state:
     the prefix-key chain over each input path and source. Marshaled state bytes
     are not reproducible (they contain .cmi-load-order-dependent variable
     identifiers), so consumers chain from this key instead of digesting the
     artifact. *)
  cache_key : string;
}

let compiler_error message =
  Error
    ({ Lg.Compiler.code = "LG9000";
       phase = `Infrastructure;
       title = "INFRASTRUCTURE ERROR";
       message;
       location = None;
       related = [];
       hints = [];
       fixes = [];
       type_mismatch = None }
      : Lg.Compiler.compile_error)

(* Prefixes for [restore_ocaml_environment]: one entry per marshaled chunk
   signature; the raw source (retype fallback) when the state predates
     signature persistence or a chunk was compiled with OCaml checks off. *)
let saved_prefixes saved =
  match saved.ocaml_signatures with
  | [] -> [ (saved.ocaml_source, None) ]
  | signatures ->
      List.map (fun signature -> (saved.ocaml_source, Some signature))
        signatures

let write_saved_compilation_state path saved =
  Lg.Compiler_artifact.write ~kind:"saved-state" ~path saved

let read_saved_compilation_state path =
  match Lg.Compiler_artifact.read ~kind:"saved-state" ~path with
  | Ok saved ->
      (* A restored state introduces its own metavariable ids; drop any
         solutions committed for metas created before the load. *)
      Lg.Type_solver.clear_meta_solutions ();
      Ok (saved : saved_compilation_state)
  | Error message -> compiler_error message

let compile_cache_enabled () =
  Sys.getenv_opt "LG_DISABLE_COMPILE_CACHE" <> Some "1"

let default_compile_cache_max_bytes =
  Int64.mul 2048L (Int64.mul 1024L 1024L)

let compile_cache_max_bytes () =
  match Sys.getenv_opt "LG_COMPILE_CACHE_MAX_BYTES" with
  | Some value ->
      Option.value (Int64.of_string_opt value)
        ~default:default_compile_cache_max_bytes
  | None -> default_compile_cache_max_bytes

let rec find_repo_root_opt dir =
  if Sys.file_exists (Filename.concat dir "dune-project") then Some dir
  else
    let parent = Filename.dirname dir in
    if parent = dir then None else find_repo_root_opt parent

let rec ensure_directory path =
  if Sys.file_exists path then ()
  else (
    ensure_directory (Filename.dirname path);
    try Unix.mkdir path 0o755 with
    | Unix.Unix_error (Unix.EEXIST, _, _) when Sys.is_directory path -> ())

let write_marshal_file path value =
  ensure_directory (Filename.dirname path);
  let oc = open_out_bin path in
  Fun.protect
    ~finally:(fun () -> close_out_noerr oc)
    (fun () -> Marshal.to_channel oc value [])

let read_marshal_file path =
  if not (Sys.file_exists path) then None
  else
    try
      let ic = open_in_bin path in
      Fun.protect
        ~finally:(fun () -> close_in_noerr ic)
        (fun () -> Some (Marshal.from_channel ic))
    with Sys_error _ | End_of_file | Failure _ -> None

let compile_cache_directory () =
  match Sys.getenv_opt "LG_CACHE_DIR" with
  | Some path -> Filename.concat path "compile-files"
  | None ->
      let base_directory =
        Option.value (find_repo_root_opt (Sys.getcwd ())) ~default:(Sys.getcwd ())
      in
      Filename.concat
        base_directory ".lg-cache/compile-files"

let compile_cache_lock_name = ".lock"

let with_compile_cache_lock action =
  let directory = compile_cache_directory () in
  ensure_directory directory;
  let lock_path = Filename.concat directory compile_cache_lock_name in
  let descriptor =
    Unix.openfile lock_path [ Unix.O_CREAT; Unix.O_RDWR ] 0o600
  in
  Fun.protect
    ~finally:(fun () -> Unix.close descriptor)
    (fun () ->
      Unix.lockf descriptor Unix.F_LOCK 0;
      Fun.protect
        ~finally:(fun () -> Unix.lockf descriptor Unix.F_ULOCK 0)
        action)

let compute_compiler_cache_identity () =
  let adjacent_compiler_directory =
    Filename.concat (Filename.dirname Sys.executable_name) "../src"
  in
  let compiler_artifacts directory =
    [ "lg.cmxa"; "lg.cma" ]
    |> List.map (Filename.concat directory)
    |> List.filter Sys.file_exists
  in
  let artifacts =
    match compiler_artifacts adjacent_compiler_directory with
    | _ :: _ as artifacts -> artifacts
    | [] ->
      find_repo_root_opt (Sys.getcwd ())
      |> Option.map (fun repo_root ->
             Filename.concat repo_root "_build/default/src")
      |> Option.map compiler_artifacts
      |> Option.value ~default:[]
      |> (function
           | _ :: _ as artifacts -> artifacts
           | [] -> [ Sys.executable_name ])
  in
  let artifact_identity path =
    Filename.basename path ^ "\000" ^ Digest.to_hex (Digest.file path)
  in
  String.concat "\000"
    (Sys.ocaml_version :: List.map artifact_identity artifacts)
  |> Digest.string |> Digest.to_hex

let compiler_cache_identity =
  let identity = lazy (compute_compiler_cache_identity ()) in
  fun () -> Lazy.force identity

let compile_files_cache_format_version = "compile-files-v8"

let reader_target_cache_key = function
  | None -> "default"
  | Some target -> Lg.Target.to_string target

let next_prefix_key ~target ?reader_target previous_key input_path source =
  Digest.string
    (String.concat "\000"
       [
         previous_key;
         Lg.Target.to_string target;
         reader_target_cache_key reader_target;
         (* Output differs between redef-cell and direct-binding emission;
            without this, one mode's cache would serve the other's output. *)
         string_of_bool !(Lg.Top_level_elaborator.redefable_roots);
         input_path;
         source;
       ])
  |> Digest.to_hex

let compile_cache_generation_directory () =
  Filename.concat (compile_cache_directory ()) (compiler_cache_identity ())

let cache_path key suffix =
  Filename.concat (compile_cache_generation_directory ())
    (key ^ suffix ^ ".marshal")

let runner_cache_path key =
  Filename.concat (compile_cache_generation_directory ())
    ("runner-" ^ key ^ ".exe")

let runner_manifest_path key =
  Filename.concat (compile_cache_generation_directory ())
    ("runner-manifest-" ^ key ^ ".marshal")

type cache_entry_files = {
  paths : string list;
  size : int64;
  modified_at : float;
}

let cache_entry_key filename =
  let suffixes = [ ".output.marshal"; ".state.marshal" ] in
  suffixes
  |> List.find_map (fun suffix ->
         if Filename.check_suffix filename suffix then
           Some
             (String.sub filename 0
                (String.length filename - String.length suffix))
         else None)

let rec remove_cache_tree path =
  match (Unix.lstat path).st_kind with
  | Unix.S_DIR ->
      Sys.readdir path
      |> Array.iter (fun name -> remove_cache_tree (Filename.concat path name));
      Unix.rmdir path
  | _ -> Sys.remove path

let prune_obsolete_cache_generations () =
  let root = compile_cache_directory () in
  if Sys.file_exists root then
    let current = compiler_cache_identity () in
    Sys.readdir root
    |> Array.iter (fun name ->
           if
             (not (String.equal name current))
             && not (String.equal name compile_cache_lock_name)
           then
             let path = Filename.concat root name in
             try remove_cache_tree path with
             | Sys_error _ | Unix.Unix_error _ -> ())

let prune_compile_cache_unlocked () =
  prune_obsolete_cache_generations ();
  let directory = compile_cache_generation_directory () in
  if Sys.file_exists directory then
    let entries = Hashtbl.create 128 in
    Sys.readdir directory
    |> Array.iter (fun filename ->
           match cache_entry_key filename with
           | None -> ()
           | Some key ->
               let path = Filename.concat directory filename in
               let stats = Unix.stat path in
               let existing =
                 Hashtbl.find_opt entries key
                 |> Option.value
                      ~default:{ paths = []; size = 0L; modified_at = 0. }
               in
               Hashtbl.replace entries key
                 {
                   paths = path :: existing.paths;
                   size = Int64.add existing.size (Int64.of_int stats.st_size);
                   modified_at = max existing.modified_at stats.st_mtime;
                 });
    let entries = Hashtbl.to_seq_values entries |> List.of_seq in
    let total =
      List.fold_left
        (fun total entry -> Int64.add total entry.size)
        0L entries
    in
    let maximum = max 0L (compile_cache_max_bytes ()) in
    if Int64.compare total maximum > 0 then
      let oldest_first =
        List.sort
          (fun left right -> Float.compare left.modified_at right.modified_at)
          entries
      in
      ignore
        (List.fold_left
           (fun remaining entry ->
             if Int64.compare remaining maximum <= 0 then remaining
             else (
               List.iter
                 (fun path -> if Sys.file_exists path then Sys.remove path)
                 entry.paths;
               Int64.sub remaining entry.size))
           total oldest_first)

let prune_compile_cache () =
  with_compile_cache_lock prune_compile_cache_unlocked

let touch_cache_entry key =
  let now = Unix.gettimeofday () in
  [ cache_path key ".output"; cache_path key ".state" ]
  |> List.iter (fun path -> if Sys.file_exists path then Unix.utimes path now now)

let report_corrupt_cache_entry key messages =
  if Sys.getenv_opt "LG_COMPILE_CACHE_DEBUG" = Some "1" then
    Printf.eprintf "lg: compile cache ignored corrupt entry %s: %s\n%!" key
      (String.concat "; " messages)

let read_cached_prefix_output key =
  if not (compile_cache_enabled ()) then None
  else
    with_compile_cache_lock (fun () ->
        let output_path = cache_path key ".output" in
        if not (Sys.file_exists output_path) then None
        else
          match
            Lg.Compiler_artifact.read ~kind:"prefix-output" ~path:output_path
          with
          | Ok cached_output ->
            let cached_output = (cached_output : cached_prefix_output) in
            touch_cache_entry key;
            Some cached_output
          | Error message ->
            report_corrupt_cache_entry key [ message ];
            Lg.Compiler_artifact.remove_if_present output_path;
            None)

let read_cached_prefix_state key =
  if not (compile_cache_enabled ()) then None
  else
    with_compile_cache_lock (fun () ->
        let state_path = cache_path key ".state" in
        if not (Sys.file_exists state_path) then None
        else
          match Lg.Compiler_artifact.read ~kind:"prefix-state" ~path:state_path with
          | Ok cached_state ->
            Lg.Type_solver.clear_meta_solutions ();
            touch_cache_entry key;
            Some ((cached_state : cached_prefix_state).state)
          | Error message ->
            report_corrupt_cache_entry key [ message ];
            Lg.Compiler_artifact.remove_if_present state_path;
            None)

(* Output-only entries are usable only through a validated checkpoint. Reading
   the longest cached prefix first avoids recompiling its unchecked gaps. *)
let cached_prefixes ~target ?reader_target initial_key sources =
  let rec scan key entries = function
    | [] -> entries
    | (path, source) :: rest ->
        let key = next_prefix_key ~target ?reader_target key path source in
        match read_cached_prefix_output key with
        | None -> entries
        | Some output -> scan key ((key, output) :: entries) rest
  in
  let rec checkpoint = function
    | [] -> (Hashtbl.create 0, None)
    | (key, output) :: rest as entries ->
        if not output.has_state then checkpoint rest
        else
          match read_cached_prefix_state key with
          | None -> checkpoint rest
          | Some state ->
              let outputs = Hashtbl.create (List.length entries) in
              List.iter (fun (key, output) -> Hashtbl.add outputs key output) entries;
              (outputs, Some (key, state))
  in
  checkpoint (scan initial_key [] sources)

let cached_compiler_state checkpoint key =
  match checkpoint with
  | Some (checkpoint_key, state) when String.equal checkpoint_key key ->
      Replayed state
  | Some _ | None -> Cached key

let prefix_cache_writer () =
  let explicit_interval =
    Option.bind (Sys.getenv_opt "LG_COMPILE_CACHE_MIN_SECONDS")
      float_of_string_opt
  in
  let interval = ref (Option.value explicit_interval ~default:1.) in
  let accumulated = ref 0. in
  fun ~elapsed ~final key (output : cached_prefix_write) ->
    accumulated := !accumulated +. elapsed;
    let has_state = final || !accumulated >= !interval in
    if compile_cache_enabled () then
      try
        let started_at = Sys.time () in
        with_compile_cache_lock (fun () ->
            let directory = compile_cache_generation_directory () in
            ensure_directory directory;
            Lg.Compiler_artifact.write ~kind:"prefix-output"
              ~path:(cache_path key ".output")
              {
                source_packages = output.write_source_packages;
                compilation = output.write_compilation;
                has_state;
              };
            if has_state then
              Lg.Compiler_artifact.write ~kind:"prefix-state"
                ~path:(cache_path key ".state")
                { state = output.write_state });
        let write_elapsed = Sys.time () -. started_at in
        if has_state then (
          accumulated := 0.;
          (* Amortize snapshots to about 5% of compilation CPU time. The final
             state is always saved, even for a single cheap source file. *)
          if Option.is_none explicit_interval then
            interval := max 1. (20. *. write_elapsed));
        if Sys.getenv_opt "LG_COMPILE_TIMINGS" = Some "1" then
          Printf.eprintf "lg: wrote cached prefix: %.3fs\n%!"
            (Sys.time () -. started_at)
      with _ -> ()

let timed_step label f =
  if Sys.getenv_opt "LG_COMPILE_TIMINGS" = Some "1" then (
    let started_at = Unix.gettimeofday () in
    Fun.protect
      ~finally:(fun () ->
        Printf.eprintf "lg: %s: %.3fs\n%!" label
          (Unix.gettimeofday () -. started_at))
      f)
  else f ()

let report_cache_hit input_path =
  if Sys.getenv_opt "LG_COMPILE_CACHE_DEBUG" = Some "1" then
    Printf.eprintf "lg: compile cache hit: %s\n%!" input_path

let report_cache_miss input_path key reason =
  if Sys.getenv_opt "LG_COMPILE_CACHE_DEBUG" = Some "1" then
    let short_key =
      String.sub key 0 (min 8 (String.length key))
    in
    Printf.eprintf "lg: compile cache miss: %s (%s, %s)\n%!" input_path
      short_key reason

type mode =
  | Compile of { input_path : string; output_path : string option }
  | Interface of { input_path : string; output_path : string option }
  | Run of { input_path : string }
  | Run_from of {
      state_path : string;
      implementation_path : string;
      input_path : string;
    }
  | Compile_files of { input_paths : string list; output_path : string }
  | Compile_files_state of {
      state_path : string;
      input_paths : string list;
      output_path : string;
    }
  | Compile_files_from of {
      state_path : string;
      input_paths : string list;
      output_path : string;
      include_prefix : bool;
      prefix_interface : string option;
      emit_state_path : string option;
    }
  | Compile_files_from_state of {
      state_path : string;
      output_state_path : string;
      input_paths : string list;
      output_path : string;
    }
  | Compile_chunk_from of {
      state_path : string;
      input_path : string;
      output_path : string option;
    }
  | Compile_chunk_state of {
      state_path : string;
      output_state_path : string;
      input_path : string;
      output_path : string option;
    }
  | Run_files of { input_paths : string list }
  | Run_files_from of {
      state_path : string;
      implementation_path : string;
      input_paths : string list;
    }
  | Test of { input_paths : string list }
  | Lsp of { state_path : string option }

let extract_compilation_options args =
  let reader_target_of_string = function
    | "clj" -> Ok Lg.Target.Native
    | "cljs" -> Ok Lg.Target.Melange
    | value -> Error ("unknown reader dialect " ^ value ^ "; expected clj or cljs")
  in
  let rec loop target reader_target reversed = function
    | [] -> (target, reader_target, List.rev reversed)
    | "--target" :: value :: rest -> (
        match Lg.Target.of_string value with
        | Ok target -> loop target reader_target reversed rest
        | Error message ->
            prerr_endline ("lg: " ^ message);
            exit 2)
    | "--reader-dialect" :: value :: rest -> (
        match reader_target_of_string value with
        | Ok reader_target -> loop target (Some reader_target) reversed rest
        | Error message ->
            prerr_endline ("lg: " ^ message);
            exit 2)
    | [ "--target" ] -> usage ()
    | [ "--reader-dialect" ] -> usage ()
    | argument :: rest -> loop target reader_target (argument :: reversed) rest
  in
  loop Lg.Target.default None [] args

(* Batch emit modes write a .ml file for compilation, not an interactive
   session, so redefinition cells default off for them; `--redef` opts back
   in for code that patches bindings with `with-redefs`. `--no-redef` is
   still accepted for compatibility. Run/Test/REPL/LSP modes keep cells on:
   a script may legitimately use `with-redefs`. *)
let redef_requested = ref false

let strip_redef_flags args =
  if List.mem "--redef" args then redef_requested := true;
  List.filter
    (fun arg -> arg <> "--redef" && arg <> "--no-redef")
    args

let batch_redef () =
  Lg.Top_level_elaborator.redefable_roots := !redef_requested

let parse_args argv =
  let target, reader_target, args =
    extract_compilation_options (Array.to_list argv)
  in
  let args = strip_redef_flags args in
  let mode =
    match args with
    | [ _program; "--lsp" ] -> Lsp { state_path = None }
    | [ _program; "--lsp"; "--state"; state_path ] ->
        Lsp { state_path = Some state_path }
    | _program :: "test" :: input_paths -> Test { input_paths }
    | [ _program; "--interface"; input ] ->
        batch_redef ();
        Interface { input_path = input; output_path = None }
    | [ _program; "--interface"; input; "-o"; output ] ->
        batch_redef ();
        Interface { input_path = input; output_path = Some output }
    | [ _program; input ] when not (String.starts_with ~prefix:"--" input) ->
        batch_redef ();
        Compile { input_path = input; output_path = None }
    | [ _program; input; "-o"; output ]
      when not (String.starts_with ~prefix:"--" input) ->
        batch_redef ();
        Compile { input_path = input; output_path = Some output }
    | [ _program; "--run"; input ] -> Run { input_path = input }
    | [ _program; "--run-from"; state_path; implementation_path; input_path ] ->
        Run_from { state_path; implementation_path; input_path }
    | _program :: "--compile-files" :: args -> (
        batch_redef ();
        match List.rev args with
        | output_path :: "-o" :: reversed_inputs ->
            Compile_files
              { input_paths = List.rev reversed_inputs; output_path }
        | _ -> usage ())
    | _program :: "--compile-files-state" :: state_path :: args -> (
        batch_redef ();
        match List.rev args with
        | output_path :: "-o" :: reversed_inputs ->
            Compile_files_state
              {
                state_path;
                input_paths = List.rev reversed_inputs;
                output_path;
              }
        | _ -> usage ())
    | _program :: "--compile-files-from" :: state_path :: args -> (
        batch_redef ();
        let emit_state_path, args =
          match args with
          | "--emit-state" :: path :: rest -> (Some path, rest)
          | [ "--emit-state" ] -> usage ()
          | _ -> (None, args)
        in
        match List.rev args with
        | output_path :: "-o" :: reversed_inputs ->
            Compile_files_from
              {
                state_path;
                input_paths = List.rev reversed_inputs;
                output_path;
                include_prefix = true;
                prefix_interface = None;
                emit_state_path;
              }
        | _ -> usage ())
    | _program :: "--compile-files-chunk-from" :: state_path :: args -> (
        batch_redef ();
        let prefix_interface, args =
          match args with
          | "--prefix-interface" :: path :: rest -> (Some path, rest)
          | [ "--prefix-interface" ] -> usage ()
          | _ -> (None, args)
        in
        let emit_state_path, args =
          match args with
          | "--emit-state" :: path :: rest -> (Some path, rest)
          | [ "--emit-state" ] -> usage ()
          | _ -> (None, args)
        in
        match List.rev args with
        | output_path :: "-o" :: reversed_inputs ->
            Compile_files_from
              {
                state_path;
                input_paths = List.rev reversed_inputs;
                output_path;
                include_prefix = false;
                prefix_interface;
                emit_state_path;
              }
        | _ -> usage ())
    | _program :: "--compile-files-from-state" :: state_path
      :: output_state_path :: args -> (
        batch_redef ();
        match List.rev args with
        | output_path :: "-o" :: reversed_inputs ->
            Compile_files_from_state
              {
                state_path;
                output_state_path;
                input_paths = List.rev reversed_inputs;
                output_path;
              }
        | _ -> usage ())
    | [
     _program;
     "--compile-chunk-from";
     state_path;
     input_path;
     "-o";
     output_path;
    ] ->
        batch_redef ();
        Compile_chunk_from
          { state_path; input_path; output_path = Some output_path }
    | [ _program; "--compile-chunk-from"; state_path; input_path ] ->
        batch_redef ();
        Compile_chunk_from { state_path; input_path; output_path = None }
    | [
     _program;
     "--compile-chunk-state";
     state_path;
     output_state_path;
     input_path;
     "-o";
     output_path;
    ] ->
        batch_redef ();
        Compile_chunk_state
          {
            state_path;
            output_state_path;
            input_path;
            output_path = Some output_path;
          }
    | [
     _program;
     "--compile-chunk-state";
     state_path;
     output_state_path;
     input_path;
    ] ->
        batch_redef ();
        Compile_chunk_state
          { state_path; output_state_path; input_path; output_path = None }
    | _program :: "--run-files" :: input_paths ->
        Run_files { input_paths }
    | _program :: "--run-files-from" :: state_path :: implementation_path
      :: input_paths ->
        Run_files_from { state_path; implementation_path; input_paths }
    | _ -> usage ()
  in
  (target, reader_target, mode)

type native_link_layout = {
  include_directories : string list;
  archives : string list;
}

let development_link_layout ?(archive_suffix = ".cmxa") executable_directory =
  let build_directory = Filename.dirname executable_directory in
  let rrbvec_directory = Filename.concat build_directory "vendor/rrbvec" in
  let compiler_directory = Filename.concat build_directory "src" in
  let runtime_directory = Filename.concat build_directory "runtime" in
  let backend_directory =
    Filename.concat build_directory "runtime_edn_backend_native"
  in
  let test_runtime_directory =
    Filename.concat build_directory "test_runner/runtime"
  in
  let test_alcotest_directory =
    Filename.concat build_directory "test_runner/alcotest"
  in
  let compiler_archive = Filename.concat compiler_directory ("lg" ^ archive_suffix) in
  if not (Sys.file_exists compiler_archive) then None
  else
    Some
      {
        include_directories =
          [
            rrbvec_directory;
            Filename.concat rrbvec_directory ".rrbvec.objs/byte";
            compiler_directory;
            Filename.concat compiler_directory ".lg.objs/byte";
            Filename.concat compiler_directory ".lg.objs/native";
            runtime_directory;
            Filename.concat runtime_directory ".lg_runtime.objs/byte";
            Filename.concat runtime_directory ".lg_runtime.objs/native";
            Filename.concat backend_directory
              ".lg_edn_backend_native.objs/byte";
            test_runtime_directory;
            Filename.concat test_runtime_directory
              ".lg_test_runtime.objs/byte";
            test_alcotest_directory;
            Filename.concat test_alcotest_directory
              ".lg_test_alcotest.objs/byte";
          ];
        archives =
          List.filter Sys.file_exists
            [
              Filename.concat rrbvec_directory ("rrbvec" ^ archive_suffix);
              Filename.concat backend_directory ("lg_edn_backend_native" ^ archive_suffix);
              Filename.concat runtime_directory ("lg_runtime" ^ archive_suffix);
              compiler_archive;
              Filename.concat test_runtime_directory
                ("lg_test_runtime" ^ archive_suffix);
              Filename.concat test_alcotest_directory
                ("lg_test_alcotest" ^ archive_suffix);
            ];
      }

let rec dune_files_under_uncached directory =
  if not (Sys.file_exists directory && Sys.is_directory directory) then []
  else
    sorted_readdir directory
    |> List.concat_map (fun name ->
           let path = Filename.concat directory name in
           if name = "_build" || name = ".git" || name = "_opam" then []
           else if Sys.file_exists path && Sys.is_directory path then
             dune_files_under_uncached path
           else if name = "dune" then [ path ]
           else [])

let dune_files_cache = Hashtbl.create 8

let dune_files_under directory =
  match Hashtbl.find_opt dune_files_cache directory with
  | Some files -> files
  | None ->
      let files = dune_files_under_uncached directory in
      Hashtbl.replace dune_files_cache directory files;
      files

let line_value form line =
  let prefix = "(" ^ form ^ " " in
  let line = String.trim line in
  if String.starts_with ~prefix line && String.ends_with ~suffix:")" line then
    let rec trim_closing_parens value =
      let value = String.trim value in
      let length = String.length value in
      if length > 0 && value.[length - 1] = ')' then
        trim_closing_parens (String.sub value 0 (length - 1))
      else value
    in
    let value =
      String.sub line (String.length prefix)
        (String.length line - String.length prefix)
      |> trim_closing_parens
    in
    if value = "" then None else Some value
  else None

let state_references_in_text text =
  let pattern = "%{lib:" in
  let pattern_length = String.length pattern in
  let text_length = String.length text in
  let rec find_pattern offset =
    if offset + pattern_length > text_length then None
    else if String.sub text offset pattern_length = pattern then Some offset
    else find_pattern (offset + 1)
  in
  let rec loop offset references =
    match find_pattern offset with
    | None -> List.rev references
    | Some start -> (
        match String.index_from_opt text (start + pattern_length) '}' with
        | None -> List.rev references
        | Some stop ->
            let body =
              String.sub text (start + pattern_length)
                (stop - start - pattern_length)
            in
            let references =
              match String.split_on_char ':' body with
              | [ library; state_file ]
                when String.ends_with ~suffix:".state" state_file ->
                  (library, state_file) :: references
              | _ -> references
            in
            loop (stop + 1) references)
  in
  loop 0 []

let absolute_path_from directory path =
  if Filename.is_relative path then Filename.concat directory path else path

let split_dune_words text =
  let buffer = Buffer.create 16 in
  let words = ref [] in
  let flush () =
    if Buffer.length buffer > 0 then (
      words := Buffer.contents buffer :: !words;
      Buffer.clear buffer)
  in
  String.iter
    (function
      | '(' | ')' | '"' | '\n' | '\r' | '\t' | ' ' -> flush ()
      | char -> Buffer.add_char buffer char)
    text;
  flush ();
  List.rev !words

let dune_stanza_blocks stanza text =
  let prefix = "(" ^ stanza in
  let rec find offset blocks =
    match String.index_from_opt text offset '(' with
    | None -> List.rev blocks
    | Some start
      when start + String.length prefix <= String.length text
           && String.sub text start (String.length prefix) = prefix ->
        let rec scan index depth in_string escaped =
          if index >= String.length text then String.length text
          else
            let char = text.[index] in
            if in_string then
              scan (index + 1) depth
                (not ((not escaped) && char = '"'))
                ((not escaped) && char = '\\')
            else
              match char with
              | '"' -> scan (index + 1) depth true false
              | '(' -> scan (index + 1) (depth + 1) false false
              | ')' ->
                  if depth = 1 then index + 1
                  else scan (index + 1) (depth - 1) false false
              | _ -> scan (index + 1) depth false false
        in
        let stop = scan start 0 false false in
        find stop (String.sub text start (stop - start) :: blocks)
    | Some start -> find (start + 1) blocks
  in
  find 0 []

let dune_rule_blocks text = dune_stanza_blocks "rule" text

let dune_rule_source_paths dune_dir block =
  let words = split_dune_words block in
  let rec source_roots roots = function
    | "source_tree" :: path :: rest ->
        source_roots (absolute_path_from dune_dir path :: roots) rest
    | _ :: rest -> source_roots roots rest
    | [] -> List.rev roots
  in
  let source_files =
    words
    |> List.filter (fun word ->
           has_source_extension word && not (String.starts_with ~prefix:"%{" word))
    |> List.map (absolute_path_from dune_dir)
  in
  source_roots [] words @ source_files

let project_dune_lg_source_paths root =
  dune_files_under root
  |> List.concat_map (fun dune_file ->
         let dune_dir = Filename.dirname dune_file in
         try
           read_file dune_file |> dune_rule_blocks
           |> List.filter (fun block ->
                  String.contains block '%'
                  && state_references_in_text block <> []
                  && String.contains block '-')
           |> List.concat_map (dune_rule_source_paths dune_dir)
         with Sys_error _ -> [])
  |> List.filter Sys.file_exists
  |> unique_preserving_order

let project_state_paths root =
  dune_files_under root
  |> List.concat_map (fun dune_file ->
         read_file dune_file |> state_references_in_text
         |> List.filter_map (fun (library, state_file) ->
                let library_path =
                  library |> String.split_on_char '.'
                  |> List.fold_left Filename.concat ""
                in
                let path =
                  Filename.concat root
                    (Filename.concat "_build/install/default/lib"
                       (Filename.concat library_path state_file))
                in
                if Sys.file_exists path then Some path else None))
  |> unique_preserving_order

let workspace_module_interface_dirs root module_roots =
  let wanted =
    module_roots
    |> List.map (fun name -> String.lowercase_ascii name ^ ".cmi")
  in
  let build_root = Filename.concat root "_build/default" in
  let rec scan directories directory =
    if not (Sys.file_exists directory && Sys.is_directory directory) then directories
    else
      let basename = Filename.basename directory in
      if
        List.mem basename [ ".git"; ".ppx"; "_doc"; "melange" ]
        || String.ends_with ~suffix:".eobjs" basename
      then directories
      else
        let directories =
          if
            List.mem basename [ "byte"; "public_cmi" ]
            && List.exists
                 (fun file ->
                   List.mem (String.lowercase_ascii file) wanted)
                 (sorted_readdir directory)
          then directory :: directories
          else directories
        in
        sorted_readdir directory
        |> List.fold_left
             (fun directories entry ->
               let child = Filename.concat directory entry in
               if Sys.file_exists child && Sys.is_directory child then
                 scan directories child
               else directories)
             directories
  in
  scan [] build_root |> List.sort_uniq String.compare

let configure_ocaml_module_interface_dirs root module_roots =
  let separator = if Sys.win32 then ';' else ':' in
  let dirs = workspace_module_interface_dirs root module_roots in
  if dirs <> [] then
    let value =
      String.concat (String.make 1 separator)
        (dirs
        @ (Sys.getenv_opt "LG_OCAML_INCLUDE_PATH"
          |> Option.map (String.split_on_char separator)
          |> Option.value ~default:[]))
    in
    Unix.putenv "LG_OCAML_INCLUDE_PATH" value

let local_default_implementation_map_uncached root =
  let map = Hashtbl.create 16 in
  dune_files_under root
  |> List.iter (fun dune_file ->
         let lines = read_file dune_file |> String.split_on_char '\n' in
         let public_names = List.filter_map (line_value "public_name") lines in
         match List.filter_map (line_value "default_implementation") lines with
         | implementation :: _ ->
             List.iter
               (fun public_name -> Hashtbl.replace map public_name implementation)
               public_names
         | [] -> ());
  map

let local_default_implementation_map_cache = Hashtbl.create 8

let local_default_implementation_map root =
  match Hashtbl.find_opt local_default_implementation_map_cache root with
  | Some map -> map
  | None ->
      let map = local_default_implementation_map_uncached root in
      Hashtbl.replace local_default_implementation_map_cache root map;
      map

let resolve_local_default_implementation implementations package =
  Hashtbl.find_opt implementations package |> Option.value ~default:package

let local_package_archives ?(archive_suffix = ".cmxa") root packages =
  let default_implementations = local_default_implementation_map root in
  let requested =
    packages
    |> List.map (resolve_local_default_implementation default_implementations)
    |> List.sort_uniq String.compare
  in
  let build_root = Filename.concat root "_build/default" in
  let archive_for_dune_file dune_file =
    let relative_directory =
      let directory = Filename.dirname dune_file in
      let prefix = root ^ Filename.dir_sep in
      if String.starts_with ~prefix directory then
        String.sub directory (String.length prefix)
          (String.length directory - String.length prefix)
      else directory
    in
    let build_directory = Filename.concat build_root relative_directory in
    let lines = read_file dune_file |> String.split_on_char '\n' in
    let rec loop current_name archives = function
      | [] -> archives
      | line :: rest ->
          let private_archive name =
            let archive =
              Filename.concat build_directory (name ^ archive_suffix)
            in
            if Sys.file_exists archive then
              let object_dir =
                Filename.concat build_directory ("." ^ name ^ ".objs")
              in
              let include_dirs = object_include_dirs object_dir in
              Some (name, archive, include_dirs)
            else None
          in
          let current_name =
            match line_value "name" line with
            | Some name -> Some name
            | None -> current_name
          in
          let archives =
            match (line_value "public_name" line, line_value "name" line) with
            | Some public_name, _ when List.mem public_name requested ->
                let library_name =
                  Option.value current_name
                    ~default:
                      (public_name |> String.map (function '-' -> '_' | c -> c))
                in
                let archive =
                  Filename.concat build_directory
                    (library_name ^ archive_suffix)
                in
                if Sys.file_exists archive then
                  let object_dir =
                    Filename.concat build_directory
                      ("." ^ library_name ^ ".objs")
                  in
                  let include_dirs = object_include_dirs object_dir in
                  (public_name, archive, include_dirs) :: archives
                else archives
            | _, Some name when List.mem name requested -> (
                match private_archive name with
                | Some archive -> archive :: archives
                | None -> archives)
            | (Some _, _) | (None, _) -> archives
          in
          loop current_name archives rest
    in
    loop None [] lines
  in
  dune_files_under root |> List.concat_map archive_for_dune_file
  |> List.sort_uniq (fun (_left_package, left_archive, _left_dirs)
                         (_right_package, right_archive, _right_dirs) ->
         String.compare left_archive right_archive)

let dune_block_atoms text form =
  let marker = "(" ^ form in
  let marker_length = String.length marker in
  let text_length = String.length text in
  let delimiter = function
    | ' ' | '\n' | '\r' | '\t' | '(' | ')' -> true
    | _ -> false
  in
  let atoms block =
    block
    |> String.map (fun char -> if delimiter char then ' ' else char)
    |> String.split_on_char ' '
    |> List.filter (fun atom ->
           atom <> "" && atom <> form
           && not (String.starts_with ~prefix:";" atom)
           && not (String.starts_with ~prefix:":" atom)
           && not (String.starts_with ~prefix:"%" atom)
           && atom <> "->")
  in
  let rec find_from offset =
    if offset + marker_length > text_length then None
    else if String.sub text offset marker_length = marker then Some offset
    else find_from (offset + 1)
  in
  let rec collect offset blocks =
    match find_from offset with
    | None -> List.rev blocks
    | Some start ->
        let rec stop_at index depth =
          if index >= text_length then text_length
          else
            let depth =
              match text.[index] with
              | '(' -> depth + 1
              | ')' -> depth - 1
              | _ -> depth
            in
            if depth = 0 then index + 1 else stop_at (index + 1) depth
        in
        let stop = stop_at start 0 in
        let block = String.sub text start (stop - start) in
        collect stop (block :: blocks)
  in
  collect 0 [] |> List.concat_map atoms

let string_contains_substring text pattern =
  let pattern_length = String.length pattern in
  let text_length = String.length text in
  let rec loop offset =
    if pattern_length = 0 then true
    else if offset + pattern_length > text_length then false
    else if String.sub text offset pattern_length = pattern then true
    else loop (offset + 1)
  in
  loop 0

let project_lg_test_libraries root =
  dune_files_under root
  |> List.concat_map (fun dune_file ->
         try
           read_file dune_file |> dune_stanza_blocks "executable"
           |> List.filter (fun block ->
                  string_contains_substring block "lg-test.runtime"
                  || string_contains_substring block "lg-test.alcotest")
           |> List.concat_map (fun block -> dune_block_atoms block "libraries")
         with Sys_error _ -> [])
  |> unique_preserving_order

let local_package_dependency_map_uncached root =
  let map = Hashtbl.create 64 in
  let default_implementations = local_default_implementation_map root in
  dune_files_under root
  |> List.iter (fun dune_file ->
         let text = read_file dune_file in
         let public_names =
           text |> String.split_on_char '\n'
           |> List.filter_map (line_value "public_name")
         in
         match public_names with
         | [] -> ()
         | _ ->
             let deps =
               dune_block_atoms text "libraries"
               |> List.map
                    (resolve_local_default_implementation
                       default_implementations)
             in
             List.iter
               (fun public_name ->
                 let existing =
                   Hashtbl.find_opt map public_name |> Option.value ~default:[]
                 in
                 Hashtbl.replace map public_name
                   (unique_preserving_order (existing @ deps)))
               public_names);
  map

let local_package_dependency_map_cache = Hashtbl.create 8

let local_package_dependency_map root =
  match Hashtbl.find_opt local_package_dependency_map_cache root with
  | Some map -> map
  | None ->
      let map = local_package_dependency_map_uncached root in
      Hashtbl.replace local_package_dependency_map_cache root map;
      map

let local_package_dependency_closure root packages =
  let dependency_map = local_package_dependency_map root in
  let rec visit seen = function
    | [] -> List.rev seen
    | package :: rest ->
        if List.mem package seen then visit seen rest
        else
          let deps =
            Hashtbl.find_opt dependency_map package |> Option.value ~default:[]
          in
          visit (package :: seen) (deps @ rest)
  in
  visit [] packages

let rec archive_files_under_uncached archive_suffix directory =
  if not (Sys.file_exists directory && Sys.is_directory directory) then []
  else
    sorted_readdir directory
    |> List.concat_map (fun name ->
           let path = Filename.concat directory name in
           if List.mem name [ ".git"; ".ppx"; "_doc"; "melange" ] then []
           else if Sys.file_exists path && Sys.is_directory path then
             archive_files_under_uncached archive_suffix path
           else if String.ends_with ~suffix:archive_suffix name then [ path ]
           else [])

let archive_files_cache = Hashtbl.create 8

let archive_files_under archive_suffix directory =
  let key = archive_suffix ^ "\000" ^ directory in
  match Hashtbl.find_opt archive_files_cache key with
  | Some files -> files
  | None ->
      let files = archive_files_under_uncached archive_suffix directory in
      Hashtbl.replace archive_files_cache key files;
      files

let module_name_of_archive archive =
  Filename.basename archive |> Filename.remove_extension
  |> fun name ->
  if name = "" then name
  else
    String.make 1 (Char.uppercase_ascii name.[0])
    ^ String.sub name 1 (String.length name - 1)

let local_archive_link_priority archive =
  match Filename.basename archive |> Filename.remove_extension with
  | "rrbvec" -> 10
  | "re" -> 14
  | "yojson" -> 15
  | "melange_edn" -> 20
  | "melange_edn_native" -> 30
  | "lg_edn_backend_native" -> 40
  | "lg_runtime" -> 50
  | "lg_test_runtime" -> 60
  | "fmt" -> 61
  | "astring" -> 62
  | "uutf" -> 63
  | "cmdliner" -> 64
  | "alcotest_stdlib_ext" -> 65
  | "alcotest_engine" -> 66
  | "alcotest" -> 67
  | "lg_test_alcotest" -> 70
  | "seq" -> 75
  | "bigstringaf" -> 76
  | "angstrom" -> 77
  | "ptime" -> 78
  | "timedesc_tzdb_full" -> 79
  | "timedesc_tzlocal_unix_or_utc" -> 80
  | "timedesc" -> 81
  | "fsrs" -> 90
  | "datascript_types" -> 100
  | "persistent_sorted_set" | "persistent_sorted_set_native" -> 105
  | "datascript" -> 110
  | "datascript_native" -> 120
  | "datascript_lg" -> 130
  | "transit_core" -> 140
  | "transit_native" -> 150
  | _ -> 1000

let sort_local_archives_for_link archives =
  archives
  |> List.sort (fun left right ->
         let priority_order =
           Int.compare (local_archive_link_priority left)
             (local_archive_link_priority right)
         in
         if priority_order <> 0 then priority_order
         else String.compare left right)

let source_references_ocaml_module source module_name =
  string_contains_substring source (module_name ^ ".")
  || string_contains_substring source (module_name ^ "__")
  || string_contains_substring source ("open " ^ module_name)
  || string_contains_substring source ("module " ^ module_name)
  || string_contains_substring source ("include " ^ module_name)

let referenced_local_module_archives ?(archive_suffix = ".cmxa") root ocaml_source =
  let ignored =
    [
      "Lg";
      "Lg_runtime";
      "Lg_edn_backend";
      "Rrbvec";
      "Lg_test_runtime";
      "Lg_test_alcotest";
    ]
  in
  archive_files_under archive_suffix (Filename.concat root "_build/default")
  |> List.filter_map (fun archive ->
        let module_name = module_name_of_archive archive in
        if
           (not (List.mem module_name ignored))
           && source_references_ocaml_module ocaml_source module_name
        then Some archive
        else None)

let replace_archive_suffix archive suffix =
  (try Filename.chop_extension archive with Invalid_argument _ -> archive)
  ^ suffix

let installed_link_layout ?(archive_suffix = ".cmxa") executable_directory =
  let prefix = Filename.dirname executable_directory in
  let library_directory = Filename.concat prefix "lib/lg" in
  let rrbvec_directory = Filename.concat library_directory "rrbvec" in
  let runtime_directory = Filename.concat library_directory "runtime" in
  let backend_directory = Filename.concat library_directory "edn-backend/native" in
  let test_runtime_directory = Filename.concat prefix "lib/lg-test/runtime" in
  let test_alcotest_directory = Filename.concat prefix "lib/lg-test/alcotest" in
  let compiler_archive =
    Filename.concat library_directory ("lg" ^ archive_suffix)
  in
  if not (Sys.file_exists compiler_archive) then None
  else
    Some
      {
        include_directories =
          [
            library_directory;
            rrbvec_directory;
            runtime_directory;
            backend_directory;
            test_runtime_directory;
            test_alcotest_directory;
          ];
        archives =
          List.filter Sys.file_exists
            [
              Filename.concat rrbvec_directory ("rrbvec" ^ archive_suffix);
              Filename.concat backend_directory
                ("lg_edn_backend_native" ^ archive_suffix);
              Filename.concat runtime_directory ("lg_runtime" ^ archive_suffix);
              compiler_archive;
              Filename.concat test_runtime_directory
                ("lg_test_runtime" ^ archive_suffix);
              Filename.concat test_alcotest_directory
                ("lg_test_alcotest" ^ archive_suffix);
            ];
      }

let native_link_layout ?(archive_suffix = ".cmxa") () =
  let executable_path =
    if Filename.is_relative Sys.executable_name then
      Filename.concat (Sys.getcwd ()) Sys.executable_name
    else Sys.executable_name
  in
  let executable_directory = Filename.dirname executable_path in
  match development_link_layout ~archive_suffix executable_directory with
  | Some _ as layout -> layout
  | None -> installed_link_layout ~archive_suffix executable_directory

let run_ocaml_source ?archive_scan_source packages ocaml_source =
  let ml_path = Filename.temp_file "lg" ".ml" in
  let exe_path = Filename.temp_file "lg" ".exe" in
  let keep_temp_ml = Sys.getenv_opt "LG_KEEP_TEMP_ML" = Some "1" in
  write_output (Some ml_path) ocaml_source;
  if keep_temp_ml then Printf.eprintf "lg: temp ml: %s\n%!" ml_path;
  let archive_scan_source =
    Option.value archive_scan_source ~default:ocaml_source
  in
  let base_packages =
    List.sort_uniq String.compare
      (("melange-edn-native" :: "re" :: "str" :: "unix" :: "yojson" :: packages)
      @
      if List.mem "lg-test.alcotest" packages then
        [ "alcotest"; "alcotest.engine" ]
      else [])
  in
  let root = find_repo_root_opt (Sys.getcwd ()) in
  let cache_runner =
    compile_cache_enabled () && Sys.getenv_opt "LG_DISABLE_RUNNER_CACHE" <> Some "1"
  in
  let runner_source_key =
    Digest.string
      (String.concat "\000"
         [
           compiler_cache_identity ();
           "runner-source-v1";
           Option.value root ~default:(Sys.getcwd ());
           String.concat "," base_packages;
           ocaml_source;
         ])
    |> Digest.to_hex
  in
  if cache_runner then
    match
      (read_marshal_file (runner_manifest_path runner_source_key)
        : cached_runner_manifest option)
    with
    | Some manifest when Sys.file_exists manifest.runner_executable ->
        if Sys.getenv_opt "LG_COMPILE_TIMINGS" = Some "1" then
          Printf.eprintf "lg: runner source cache hit: %s\n%!"
            manifest.runner_key;
        if not keep_temp_ml then Sys.remove ml_path;
        Sys.remove exe_path;
        let exit_code =
          timed_step "native test executable" (fun () ->
              Sys.command (Filename.quote manifest.runner_executable))
        in
        exit exit_code
    | Some _ | None -> ();
  let discover_local_link_inputs archive_suffix =
    timed_step ("discover local link inputs " ^ archive_suffix) (fun () ->
        match root with
        | Some root ->
            let test_libraries = project_lg_test_libraries root in
            let packages =
              local_package_dependency_closure root
                (base_packages
                @ test_libraries
                @ [
                    "lg";
                    "lg.runtime";
                    "lg.rrbvec";
                    "lg.edn-backend.native";
                    "lg-test.runtime";
                    "lg-test.alcotest";
                  ])
            in
            let package_archives =
              local_package_archives ~archive_suffix root packages
            in
            let archive_packages =
              List.map
                (fun (package, _archive, _dirs) -> package)
                package_archives
            in
            let include_directories =
              List.concat_map
                (fun (_package, _archive, dirs) -> dirs)
                package_archives
            in
            let archives =
              List.map
                (fun (_package, archive, _dirs) -> archive)
                package_archives
              @
              (if test_libraries = [] then
                 referenced_local_module_archives ~archive_suffix root
                   archive_scan_source
               else [])
              @ (local_package_archives ~archive_suffix root
                   [ "alcotest_stdlib_ext"; "datascript_types" ]
                |> List.map (fun (_package, archive, _dirs) -> archive))
              |> sort_local_archives_for_link
            in
            (archive_packages, include_directories, archives)
        | None -> ([], [], []))
  in
  let native_local_archive_packages, native_local_include_directories,
      native_local_archives =
    discover_local_link_inputs ".cmxa"
  in
  let bytecode_missing =
    native_local_archives
    |> List.filter (fun archive ->
           not (Sys.file_exists (replace_archive_suffix archive ".cma")))
  in
  let bytecode_layout_available =
    Option.is_some (native_link_layout ~archive_suffix:".cma" ())
  in
  let archive_suffix, compiler =
    match Sys.getenv_opt "LG_TEST_NATIVE" with
    | Some "1" -> (".cmxa", "ocamlopt")
    | _ when bytecode_missing = [] && bytecode_layout_available ->
        (".cma", "ocamlc")
    | _ ->
        (if Sys.getenv_opt "LG_COMPILE_TIMINGS" = Some "1" then
          let missing =
            match bytecode_missing with
            | [] -> "runtime layout"
            | paths -> String.concat ", " (List.map Filename.basename paths)
          in
          Printf.eprintf "lg: bytecode runner unavailable: %s\n%!" missing);
        (".cmxa", "ocamlopt")
  in
  let local_archive_packages, local_include_directories, local_archives =
    if archive_suffix = ".cmxa" then
      ( native_local_archive_packages,
        native_local_include_directories,
        native_local_archives )
    else discover_local_link_inputs archive_suffix
  in
  let local_object_include_directories =
    timed_step "discover local object includes" (fun () ->
        local_archives
        |> List.concat_map (fun archive ->
               let directory = Filename.dirname archive in
               let name =
                 Filename.basename archive |> Filename.remove_extension
               in
               object_include_dirs
                 (Filename.concat directory ("." ^ name ^ ".objs")))
    )
  in
  let packages =
    base_packages
    |> List.filter (fun package ->
           not
             (List.mem package
                [
                  "lg";
                  "lg.runtime";
                  "lg.rrbvec";
                  "lg.edn-backend";
                  "lg.edn-backend.native";
                  "lg-test.runtime";
                  "lg-test.alcotest";
                ]
             || List.mem package local_archive_packages))
  in
  let package_options =
    "-package " ^ Filename.quote (String.concat "," packages) ^ " -linkpkg "
  in
  let layout =
    match native_link_layout ~archive_suffix () with
    | Some layout -> layout
    | None ->
      prerr_endline "lg: could not locate installed native runtime artifacts";
      exit 2
  in
  let local_archive_basenames = List.map Filename.basename local_archives in
  let replaced_layout_archive_dirs =
    layout.archives
    |> List.filter (fun archive ->
           List.mem (Filename.basename archive) local_archive_basenames)
    |> List.map Filename.dirname
  in
  let path_is_inside directory path =
    let prefix = directory ^ Filename.dir_sep in
    path = directory || String.starts_with ~prefix path
  in
  let layout_include_directories =
    layout.include_directories
    |> List.filter (fun directory ->
           not
             (List.exists
                (fun archive_dir -> path_is_inside archive_dir directory)
                replaced_layout_archive_dirs))
  in
  let include_options =
    timed_step "prepare link flags" (fun () ->
        (layout_include_directories
        @ local_include_directories
        @ local_object_include_directories
        @ List.map Filename.dirname local_archives)
        |> unique_preserving_order
        |> List.map (fun directory -> "-I " ^ Filename.quote directory)
        |> String.concat " ")
  in
  let archives =
    (layout.archives
    |> List.filter (fun archive ->
           not (List.mem (Filename.basename archive) local_archive_basenames)))
    @ local_archives
    |> unique_preserving_order
  in
  let archive_identity archive =
    try
      let stat = Unix.stat archive in
      Printf.sprintf "%s:%f:%d" archive stat.Unix.st_mtime stat.st_size
    with Unix.Unix_error _ -> archive
  in
  let runner_key =
    Digest.string
      (String.concat "\000"
         (compiler :: package_options :: include_options :: ocaml_source
          :: List.map archive_identity archives))
    |> Digest.to_hex
  in
  let cached_exe_path = runner_cache_path runner_key in
  if cache_runner && Sys.file_exists cached_exe_path then (
    if Sys.getenv_opt "LG_COMPILE_TIMINGS" = Some "1" then
      Printf.eprintf "lg: runner cache hit: %s\n%!" runner_key;
    write_marshal_file (runner_manifest_path runner_source_key)
      {
        runner_key;
        runner_executable = cached_exe_path;
      };
    if not keep_temp_ml then Sys.remove ml_path;
    Sys.remove exe_path;
    let exit_code =
      timed_step "native test executable" (fun () ->
          Sys.command (Filename.quote cached_exe_path))
    in
    exit exit_code);
  if Sys.getenv_opt "LG_TEST_DEBUG_SOURCES" = Some "1" then
    List.iter (Printf.eprintf "lg native archive: %s\n%!") archives;
  let archives =
    archives
    |> List.map Filename.quote |> String.concat " "
  in
  let compile_cmd =
    Printf.sprintf "ocamlfind %s %s%s -o %s %s %s" compiler package_options
      include_options (Filename.quote exe_path) archives (Filename.quote ml_path)
  in
  let compile_exit =
    timed_step "native link" (fun () -> Sys.command compile_cmd)
  in
  match compile_exit with
  | 0 ->
      let run_path =
        if cache_runner then (
          ensure_directory (Filename.dirname cached_exe_path);
          (try Sys.rename exe_path cached_exe_path with
          | Sys_error _ | Unix.Unix_error _ -> ());
          if Sys.file_exists cached_exe_path then
            write_marshal_file (runner_manifest_path runner_source_key)
              {
                runner_key;
                runner_executable = cached_exe_path;
              };
          if Sys.file_exists cached_exe_path then cached_exe_path else exe_path)
        else exe_path
      in
      let exit_code =
        timed_step "native test executable" (fun () ->
            Sys.command (Filename.quote run_path))
      in
      if not keep_temp_ml then Sys.remove ml_path;
      if run_path = exe_path then Sys.remove exe_path;
      exit exit_code
  | code ->
      if not keep_temp_ml then Sys.remove ml_path;
      Sys.remove exe_path;
      exit code

let executable_directory () =
  let executable_path =
    if Filename.is_relative Sys.executable_name then
      Filename.concat (Sys.getcwd ()) Sys.executable_name
    else Sys.executable_name
  in
  Filename.dirname executable_path

let default_stdlib_artifacts () =
  let executable_directory = executable_directory () in
  let build_directory = Filename.dirname executable_directory in
  let development_state =
    Filename.concat build_directory "stdlib/lg_stdlib_native.state"
  in
  let development_implementation =
    Filename.concat build_directory "stdlib/lg_stdlib_native.ml"
  in
  let prefix = Filename.dirname executable_directory in
  let installed_state =
    Filename.concat prefix "lib/lg/stdlib/lg_stdlib_native.state"
  in
  let installed_implementation =
    Filename.concat prefix "lib/lg/stdlib/lg_stdlib_native.ml"
  in
  match
    List.find_opt
      (fun (state, implementation) ->
        Sys.file_exists state && Sys.file_exists implementation)
      [
        (development_state, development_implementation);
        (installed_state, installed_implementation);
      ]
  with
  | Some artifacts -> artifacts
  | None ->
      prerr_endline
        "lg: unable to find lg stdlib artifacts for test execution";
      exit 2

let default_test_support_directory () =
  let executable_directory = executable_directory () in
  let build_directory = Filename.dirname executable_directory in
  let development_directory =
    Filename.concat build_directory "test_runner/clojure"
  in
  let prefix = Filename.dirname executable_directory in
  let installed_directories =
    [
      Filename.concat prefix "share/lg-test/clojure";
      Filename.concat prefix "lib/lg-test/sources";
    ]
  in
  match
    List.find_opt Sys.file_exists (development_directory :: installed_directories)
  with
  | Some directory -> directory
  | None ->
      prerr_endline "lg: unable to find lg-test support sources";
      exit 2

let test_support_sources () =
  let directory = default_test_support_directory () in
  [
    Filename.concat directory "test.cljc";
    Filename.concat directory "test_native.cljc";
  ]

let test_runner_source () =
  Filename.concat (default_test_support_directory ()) "run.cljc"

let default_lg_test_paths () =
  if Sys.file_exists "lg-test" && Sys.is_directory "lg-test" then [ "lg-test" ]
  else [ "." ]

let local_lg_source_roots () =
  let project_roots =
    if Sys.file_exists "lg" && Sys.is_directory "lg" then [ "lg" ] else []
  in
  let dependency_roots =
    let duniverse = "duniverse" in
    if Sys.file_exists duniverse && Sys.is_directory duniverse then
      sorted_readdir duniverse
      |> List.filter_map (fun name ->
             let root = Filename.concat (Filename.concat duniverse name) "lg" in
             if Sys.file_exists root && Sys.is_directory root then Some root
             else None)
    else []
  in
  project_roots @ dependency_roots

let lg_test_sources input_paths =
  let input_paths =
    if input_paths = [] then default_lg_test_paths () else input_paths
  in
  let test_sources = expand_test_input_paths input_paths in
  let project_context_sources =
    match find_repo_root_opt (Sys.getcwd ()) with
    | Some root ->
        project_dune_lg_source_paths root
        |> List.concat_map expand_test_input_path
    | None -> []
  in
  let local_sources =
    local_lg_source_roots () |> List.concat_map expand_test_input_path
    |> unique_paths_preserving_order
  in
  let source_index =
    local_source_index
      (unique_paths_preserving_order (local_sources @ project_context_sources))
  in
  let required_namespaces =
    test_sources
    |> List.concat_map (fun path -> (source_namespace_info path).requires)
    |> List.filter project_namespace
    |> List.sort_uniq String.compare
  in
  let application_sources =
    required_project_sources source_index required_namespaces
  in
  test_support_sources ()
  @ application_sources
  @ test_sources
  @ [ test_runner_source () ]
  |> unique_paths_preserving_order

let concatenate_compilation_outputs outputs =
  let runtime_open = "open Lg_runtime\n" in
  let runtime_open_length = String.length runtime_open in
  let _, outputs =
    List.fold_left
      (fun (seen_runtime_open, outputs) output ->
        let starts_with_runtime_open =
          String.starts_with ~prefix:runtime_open output
        in
        let output =
          if seen_runtime_open && starts_with_runtime_open then
            String.sub output runtime_open_length
              (String.length output - runtime_open_length)
          else output
        in
        (seen_runtime_open || starts_with_runtime_open, output :: outputs))
      (false, []) outputs
  in
  outputs |> List.rev |> String.concat "\n"

let read_compiler_state = function
  | Live state | Replayed state -> Ok state
  | Cached key -> (
      match read_cached_prefix_state key with
      | Some state -> Ok state
      | None -> compiler_error ("missing cached compiler state " ^ key))

let resume_compiler_state ~target ~packages ~prefixes = function
  | Live state -> Ok state
  | Replayed _ | Cached _ as compiler_state ->
      Result.bind (read_compiler_state compiler_state) (fun state ->
          Lg.Compiler.restore_ocaml_environment ~target ~packages state prefixes)

let order_prepared_sources ?reader_target:_ _target _compiler_state sources =
  let paths =
    sources
    |> List.map (fun (path, _source, _prepared) -> path)
    |> order_paths_by_namespace_dependencies
  in
  let rec reorder ordered = function
    | [] -> Ok (List.rev ordered)
    | path :: rest -> (
        match
          List.find_opt
            (fun (source_path, _source, _prepared) -> source_path = path)
            sources
        with
        | Some source -> reorder (source :: ordered) rest
        | None -> compiler_error ("missing analyzed source " ^ path))
  in
  reorder [] paths

let order_input_paths ?reader_target:_ _target _compiler_state input_paths =
  Ok (order_paths_by_namespace_dependencies input_paths)

let compile_files ?(use_cache = true) ?(check_ocaml = true) ?reader_target
    ?(produced_key = ref "") target input_paths =
  let input_paths = expand_input_paths input_paths in
  let initial_prefix_key =
    Digest.string
      (String.concat "\000"
         [ compiler_cache_identity (); compile_files_cache_format_version ])
    |> Digest.to_hex
  in
  let write_cached_prefix = prefix_cache_writer () in
  let rec loop cached_outputs checkpoint prefix_key compiler_state packages
      outputs diagnostics = function
    | [] ->
        produced_key := prefix_key;
        let packages = List.sort_uniq String.compare packages in
        let outputs = List.rev outputs in
        Result.map
          (fun state ->
            let ocaml_source =
              concatenate_compilation_outputs
                (List.map
                   (fun (c : Lg.Compiler.compilation) -> c.ocaml_source)
                   outputs)
            in
            let ocaml_signatures =
              List.filter_map
                (fun (c : Lg.Compiler.compilation) -> c.ocaml_signature)
                outputs
            in
            ( state,
              packages,
              ocaml_source,
              (if
                 List.length ocaml_signatures = List.length outputs
               then ocaml_signatures
               else []),
              List.concat (List.rev diagnostics) ))
          (read_compiler_state compiler_state)
    | input_path :: rest -> (
        let source = read_file input_path in
        let prefix_key =
          next_prefix_key ~target ?reader_target prefix_key input_path source
        in
        match
          Lg.Compiler.prepare_source ~target ?reader_target
            ~filename:input_path source
        with
        | Error _ as err -> err
        | Ok prepared -> (
            let source_packages =
              Lg.Compiler.prepared_source_required_packages prepared
            in
            match
              Hashtbl.find_opt cached_outputs prefix_key
            with
            | Some cached ->
                report_cache_hit input_path;
                loop cached_outputs checkpoint prefix_key
                  (cached_compiler_state checkpoint prefix_key)
                  (List.rev_append cached.source_packages packages)
                  (cached.compilation :: outputs)
                  (cached.compilation.diagnostics :: diagnostics)
                  rest
            | None ->
                report_cache_miss input_path prefix_key
                  (if Sys.file_exists (cache_path prefix_key ".output") then
                     "unusable"
                   else "missing");
                Result.bind
                  (timed_step "resume OCaml environment" (fun () ->
                       resume_compiler_state ~target ~packages
                         ~prefixes:
                           (List.rev_map
                              (fun (c : Lg.Compiler.compilation) ->
                                (c.ocaml_source, c.ocaml_signature))
                              outputs)
                         compiler_state))
                  (fun state ->
                    if Sys.getenv_opt "LG_COMPILE_TIMINGS" = Some "1" then
                      Printf.eprintf "lg: compiling %s\n%!" input_path;
                    let started_at = Sys.time () in
                      match
                        Lg.Compiler.compile_prepared_chunk_with_diagnostics state
                          ~check_ocaml prepared
                    with
                    | Error _ as err -> err
                    | Ok (state, compilation) ->
                    let elapsed = Sys.time () -. started_at in
                    if use_cache then
                      write_cached_prefix ~elapsed ~final:(rest = []) prefix_key
                        {
                          write_source_packages = source_packages;
                          write_compilation = compilation;
                          write_state = Lg.Compiler.cacheable_state state;
                            };
                        loop cached_outputs checkpoint prefix_key (Live state)
                          (List.rev_append source_packages packages)
                          (compilation :: outputs)
                          (compilation.diagnostics :: diagnostics)
                          rest)))
  in
  let result =
    Result.bind
      (order_input_paths ?reader_target target Lg.Compiler.empty_state input_paths)
      (fun input_paths ->
        let cached_outputs, checkpoint =
          if use_cache then
            cached_prefixes ~target ?reader_target initial_prefix_key
              (List.map (fun path -> (path, read_file path)) input_paths)
          else (Hashtbl.create 0, None)
        in
        loop cached_outputs checkpoint initial_prefix_key
          (Live Lg.Compiler.empty_state) [] [] [] input_paths)
  in
  if use_cache then prune_compile_cache ();
  result

let compile_file ?reader_target target input_path =
  compile_files ~use_cache:false ?reader_target target [input_path]
  |> Result.map
       (fun (_state, packages, ocaml_source, _ocaml_signatures, diagnostics) ->
         ( packages,
           { Lg.Compiler.ocaml_source; ocaml_signature = None; diagnostics } ))

let load_adjacent_interface target input_path state =
  let interface = Lg.Ocaml_interface.source_stem input_path ^ ".mli" in
  if Lg.Ocaml_interface.is_interface input_path
     || has_pending_interface state input_path
     || not (Sys.file_exists interface)
  then Ok state
  else
    Lg.Compiler.compile_chunk_with_filename ~target ~filename:interface state
      (read_file interface)
    |> Result.map fst

let compile_chunk_from_saved_state ?reader_target
    ?(produced_key = ref "") target state_path input_path =
  Result.bind (read_saved_compilation_state state_path) (fun saved ->
      if saved.target <> target then
        compiler_error "saved compiler state target does not match --target"
      else
        let source = read_file input_path in
        produced_key :=
          next_prefix_key ~target ?reader_target saved.cache_key input_path
            source;
        Result.bind
          (Lg.Compiler.prepare_source ~target ?reader_target
             ~filename:input_path source)
          (fun prepared ->
            let source_packages =
              Lg.Compiler.prepared_source_required_packages prepared
            in
            let packages =
              List.sort_uniq String.compare (source_packages @ saved.packages)
            in
            Result.bind
              (Lg.Compiler.restore_ocaml_environment ~target ~packages saved.state
                 (saved_prefixes saved))
              (fun state ->
                Result.bind (load_adjacent_interface target input_path state)
                  (fun state ->
                    Lg.Compiler.compile_prepared_chunk_with_diagnostics
                      state prepared)
                |> Result.map (fun (state, compilation) ->
                       (state, packages, compilation)))))

let prepare_prefix_interface target = function
  | None -> Ok None
  | Some path ->
      if not (Filename.check_suffix path ".cmi") then
        compiler_error "compiled prefix interface must be a .cmi file"
      else
        let name = Filename.basename path |> Filename.remove_extension in
        let module_name = String.capitalize_ascii name in
        let valid_name =
          String.length module_name > 0
          && module_name.[0] >= 'A' && module_name.[0] <= 'Z'
          && String.for_all
               (function
                 | 'A' .. 'Z' | 'a' .. 'z' | '0' .. '9' | '_' | '\'' -> true
                 | _ -> false)
               module_name
        in
        if not valid_name then compiler_error "invalid compiled prefix module name"
        else
          try
            let digest = Digest.file path |> Digest.to_hex in
            let directory = Filename.dirname path in
            let directory =
              if Filename.is_relative directory then
                Filename.concat (Sys.getcwd ()) directory
              else directory
            in
            Lg.Ocaml_signature.set_melange_target (target = Lg.Target.Melange);
            Lg.Ocaml_signature.add_include_dirs [ directory ];
            Ok (Some ("include " ^ module_name ^ "\n", module_name ^ digest))
          with Sys_error message -> compiler_error message

let compile_files_from_saved_state ?(use_cache = true) ?(check_ocaml = true)
    ?reader_target ?prefix_interface ?(produced_key = ref "") target state_path
    input_paths =
  (* Escape hatch for debugging emitted OCaml that fails its own typecheck. *)
  let check_ocaml =
    check_ocaml && Sys.getenv_opt "LG_SKIP_OCAML_CHECK" = None
  in
  Result.bind (prepare_prefix_interface target prefix_interface) (fun prefix ->
  match
    timed_step ("read saved state " ^ state_path) (fun () ->
        read_saved_compilation_state state_path)
  with
  | Error _ as error -> error
  | Ok saved ->
    let input_paths = expand_input_paths ~state:saved.state input_paths in
    if saved.target <> target then
      compiler_error "saved compiler state target does not match --target"
    else (
      if Sys.getenv_opt "LG_COMPILE_TIMINGS" = Some "1" then
        Printf.eprintf "lg: saved state has OCaml env: %b\n%!"
          (Lg.Compiler.has_ocaml_environment saved.state);
    let result =
    let rec read_sources sources packages = function
      | [] -> Ok (List.rev sources, List.sort_uniq String.compare packages)
      | input_path :: rest ->
          let source = read_file input_path in
          Result.bind
            (Lg.Compiler.prepare_source ~target ?reader_target
               ~filename:input_path source)
            (fun prepared ->
              let source_packages =
                Lg.Compiler.prepared_source_required_packages prepared
              in
              read_sources ((input_path, source, prepared) :: sources)
                (List.rev_append source_packages packages)
                rest)
    in
    Result.bind
      (timed_step "prepare sources" (fun () ->
           read_sources [] saved.packages input_paths))
      (fun (sources, packages) ->
        Result.bind
          (timed_step "order sources" (fun () ->
               order_prepared_sources ?reader_target target saved.state sources))
          (fun sources ->
        let initial_prefix_key =
          match prefix with
          | None -> saved.cache_key
          | Some (_, digest) ->
              Digest.to_hex (Digest.string (saved.cache_key ^ digest))
        in
        let cached_outputs, checkpoint =
          if use_cache then
            cached_prefixes ~target ?reader_target initial_prefix_key
              (List.map (fun (path, source, _) -> (path, source)) sources)
          else (Hashtbl.create 0, None)
        in
        let write_cached_prefix = prefix_cache_writer () in
        let rec compile prefix_key compiler_state outputs diagnostics =
          function
          | [] ->
              produced_key := prefix_key;
              Result.map
                (fun state ->
                  let ocaml_signatures =
                    List.filter_map
                      (fun (c : Lg.Compiler.compilation) -> c.ocaml_signature)
                      outputs
                  in
                  ( state,
                    packages,
                    concatenate_compilation_outputs
                      (List.rev_map
                         (fun (c : Lg.Compiler.compilation) -> c.ocaml_source)
                         outputs),
                    (if
                       List.length ocaml_signatures = List.length outputs
                     then List.rev ocaml_signatures
                     else []),
                    List.concat (List.rev diagnostics) ))
                (read_compiler_state compiler_state)
          | (input_path, source, prepared) :: rest -> (
              let prefix_key =
                next_prefix_key ~target ?reader_target prefix_key input_path source
              in
              match
                Hashtbl.find_opt cached_outputs prefix_key
              with
              | Some cached ->
                  report_cache_hit input_path;
                  compile prefix_key (cached_compiler_state checkpoint prefix_key)
                    (cached.compilation :: outputs)
                    (cached.compilation.diagnostics :: diagnostics)
                    rest
              | None ->
                  report_cache_miss input_path prefix_key
                    (if Sys.file_exists (cache_path prefix_key ".output") then
                       "unusable"
                     else "missing");
                  Result.bind
                    (timed_step "resume OCaml environment" (fun () ->
                         if check_ocaml then
                           resume_compiler_state ~target ~packages
                             ~prefixes:
                               ((match prefix with
                                | None -> saved_prefixes saved
                                | Some (source, _) -> [ (source, None) ])
                                @ List.rev_map
                                    (fun (c : Lg.Compiler.compilation) ->
                                      (c.ocaml_source, c.ocaml_signature))
                                    outputs)
                             compiler_state
                         else read_compiler_state compiler_state))
                    (fun state ->
                      if Sys.getenv_opt "LG_COMPILE_TIMINGS" = Some "1" then
                        Printf.eprintf "lg: compiling %s\n%!" input_path;
                      let started_at = Sys.time () in
                      match
                        Lg.Compiler.compile_prepared_chunk_with_diagnostics
                          ~check_ocaml state prepared
                      with
                      | Error _ as err -> err
                      | Ok (state, compilation) ->
                          let elapsed = Sys.time () -. started_at in
                          if use_cache then
                            write_cached_prefix ~elapsed ~final:(rest = []) prefix_key
                              {
                                write_source_packages = [];
                                write_compilation = compilation;
                                write_state = Lg.Compiler.cacheable_state state;
                              };
                          compile prefix_key (Live state)
                            (compilation :: outputs)
                            (compilation.diagnostics :: diagnostics)
                            rest))
        in
        compile initial_prefix_key (Replayed saved.state) [] [] sources))
    in
    if use_cache then prune_compile_cache ();
    result))

let infer_interface target input_path =
  let source = read_file input_path in
  if Sys.file_exists (Lg.Ocaml_interface.source_stem input_path ^ ".mli") then
    Result.bind (load_adjacent_interface target input_path Lg.Compiler.empty_state)
      (fun state ->
        Lg.Compiler.infer_interface_from_state ~target ~filename:input_path state source)
  else Lg.Compiler.infer_interface_with_filename ~target ~filename:input_path source

let report_diagnostics diagnostics =
  List.iter
    (fun (diagnostic : Lg.Compiler.diagnostic) ->
      prerr_endline diagnostic.message)
    diagnostics

let report_error (err : Lg.Compiler.compile_error) =
  let source =
    match err.Lg.Compiler.location with
    | Some location ->
        let filename = location.Location.loc_start.Lexing.pos_fname in
        if filename <> "" && Sys.file_exists filename then read_file filename
        else ""
    | None -> ""
  in
  prerr_endline (Lg.Compiler.render_error ~source err);
  exit 1

let run_tests ?reader_target target input_paths =
  if target <> Lg.Target.Native then (
    prerr_endline "lg: test currently supports the native target";
    exit 2);
  let stdlib_state_path, _stdlib_implementation_path = default_stdlib_artifacts () in
  let state_paths =
    (match find_repo_root_opt (Sys.getcwd ()) with
    | Some root -> project_state_paths root
    | None -> [])
    @ [ stdlib_state_path ]
    |> unique_preserving_order
  in
  let sources =
    timed_step "discover test sources" (fun () -> lg_test_sources input_paths)
  in
  (match find_repo_root_opt (Sys.getcwd ()) with
  | Some root ->
      timed_step "discover OCaml module interfaces" (fun () ->
          configure_ocaml_module_interface_dirs root
            (required_ocaml_module_roots sources))
  | None -> ());
  if Sys.getenv_opt "LG_TEST_DEBUG_SOURCES" = Some "1" then
    List.iter (Printf.eprintf "lg test source: %s\n%!") sources;
  let rec attempt last_error = function
    | [] -> (
        match last_error with
        | Some err -> report_error err
        | None ->
            prerr_endline "lg: unable to find a compiler state for tests";
            exit 2)
    | state_path :: rest -> (
        match
          compile_files_from_saved_state ?reader_target target state_path sources
            ~check_ocaml:false
        with
        | Error err -> attempt (Some err) rest
        | Ok (_state, packages, ocaml_source, _ocaml_signatures, diagnostics) ->
            let saved =
              match read_saved_compilation_state state_path with
              | Ok saved -> saved
              | Error err -> report_error err
            in
            report_diagnostics diagnostics;
            timed_step "run test source" (fun () ->
                run_ocaml_source ~archive_scan_source:ocaml_source packages
                  (concatenate_compilation_outputs
                     [ saved.ocaml_source; ocaml_source ])))
  in
  attempt None state_paths

let run_lsp state_path =
  let executable_directory = Filename.dirname Sys.executable_name in
  let adjacent_executables =
    [
      Filename.concat executable_directory "lg_lsp.exe";
      Filename.concat executable_directory "lg-lsp";
    ]
  in
  let arguments executable =
    match state_path with
    | None -> [| executable |]
    | Some state_path -> [| executable; "--state"; state_path |]
  in
  match List.find_opt Sys.file_exists adjacent_executables with
  | Some executable -> Unix.execv executable (arguments executable)
  | None -> Unix.execvp "lg-lsp" (arguments "lg-lsp")

let run_mobile argv =
  let executable_directory = Filename.dirname Sys.executable_name in
  let repo_script =
    find_repo_root_opt (Sys.getcwd ())
    |> Option.map (fun root -> Filename.concat root "scripts/lg-mobile")
  in
  let candidates =
    Filename.concat executable_directory "lg-mobile"
    :: Option.to_list repo_script
  in
  let executable =
    Option.value (List.find_opt Sys.file_exists candidates) ~default:"lg-mobile"
  in
  let arguments =
    Array.to_list argv
    |> function
    | _program :: "mobile" :: rest -> Array.of_list (executable :: rest)
    | _ -> assert false
  in
  if Filename.is_relative executable && not (String.contains executable '/')
  then Unix.execvp executable arguments
  else Unix.execv executable arguments

let run_repl argv =
  let executable_directory = Filename.dirname Sys.executable_name in
  let candidates =
    [
      Filename.concat executable_directory "lg_repl_worker.bc.exe";
      Filename.concat executable_directory "lg-repl";
    ]
  in
  let executable =
    Option.value (List.find_opt Sys.file_exists candidates) ~default:"lg-repl"
  in
  let arguments =
    Array.to_list argv
    |> function
    | _program :: "repl" :: rest -> Array.of_list (executable :: rest)
    | _ -> assert false
  in
  if Filename.is_relative executable && not (String.contains executable '/')
  then Unix.execvp executable arguments
  else Unix.execv executable arguments

let () =
  if Array.length Sys.argv > 1 && Sys.argv.(1) = "mobile" then
    run_mobile Sys.argv;
  if Array.length Sys.argv > 1 && Sys.argv.(1) = "repl" then
    run_repl Sys.argv;
  let target, reader_target, mode = parse_args Sys.argv in
  (match mode with Lsp _ -> () | _ -> tune_compiler_gc ());
  match mode with
  | Compile { input_path; output_path } -> (
      match compile_file ?reader_target target input_path with
      | Error err -> report_error err
      | Ok (_packages, compilation) ->
          report_diagnostics compilation.diagnostics;
          write_output output_path compilation.ocaml_source)
  | Interface { input_path; output_path } -> (
      match infer_interface target input_path with
      | Error err -> report_error err
      | Ok interface -> write_output output_path interface)
  | Run { input_path } -> (
      match compile_file ?reader_target target input_path with
      | Error err -> report_error err
      | Ok (packages, compilation) ->
          report_diagnostics compilation.diagnostics;
          run_ocaml_source packages compilation.ocaml_source)
  | Run_from { state_path; implementation_path; input_path } -> (
      match
        compile_chunk_from_saved_state ?reader_target target state_path input_path
      with
      | Error err -> report_error err
      | Ok (_state, packages, compilation) ->
          report_diagnostics compilation.diagnostics;
          run_ocaml_source packages
            (concatenate_compilation_outputs
               [ read_file implementation_path; compilation.ocaml_source ]))
  | Compile_files { input_paths; output_path } -> (
      match compile_files ?reader_target target input_paths with
      | Error err -> report_error err
      | Ok (_state, _packages, ocaml_source, _ocaml_signatures, diagnostics) ->
          report_diagnostics diagnostics;
          write_output (Some output_path) ocaml_source)
  | Compile_files_state { state_path; input_paths; output_path } -> (
      let produced_key = ref "" in
      match
        compile_files ~use_cache:false ?reader_target ~produced_key target
          input_paths
      with
      | Error err -> report_error err
      | Ok (state, packages, ocaml_source, ocaml_signatures, diagnostics) ->
          report_diagnostics diagnostics;
          write_output (Some output_path) ocaml_source;
          write_saved_compilation_state state_path
            {
              target;
              state = Lg.Compiler.cacheable_state state;
              packages;
              ocaml_source;
              ocaml_signatures;
              cache_key = !produced_key;
            })
  | Compile_files_from
      {
        state_path;
        input_paths;
        output_path;
        include_prefix;
        prefix_interface;
        emit_state_path;
      } -> (
      let produced_key = ref "" in
      match
        compile_files_from_saved_state ?reader_target ?prefix_interface
          ~produced_key target state_path input_paths
      with
      | Error err -> report_error err
      | Ok (state, packages, ocaml_source, ocaml_signatures, diagnostics) ->
          report_diagnostics diagnostics;
          let saved =
            if include_prefix || Option.is_some emit_state_path then
              match read_saved_compilation_state state_path with
              | Ok saved -> Some saved
              | Error err -> report_error err
            else None
          in
          (match emit_state_path with
          | None -> ()
          | Some output_state_path ->
              let saved = Option.get saved in
              write_saved_compilation_state output_state_path
                {
                  target;
                  state = Lg.Compiler.cacheable_state state;
                  packages;
                  ocaml_source =
                    concatenate_compilation_outputs
                      [ saved.ocaml_source; ocaml_source ];
                  ocaml_signatures =
                    saved.ocaml_signatures @ ocaml_signatures;
                  cache_key = !produced_key;
                });
          let ocaml_source =
            if include_prefix then
              let saved = Option.get saved in
              concatenate_compilation_outputs
                [ saved.ocaml_source; ocaml_source ]
            else
              match prefix_interface with
              | None -> ocaml_source
              | Some path ->
                  let module_name =
                    Filename.basename path |> Filename.remove_extension
                    |> String.capitalize_ascii
                  in
                  (* include (not open) re-exports the prefix's definitions, so
                     deeper chains (`chunk-from` of a state produced by another
                     `chunk-from` module) stay usable as prefixes themselves. *)
                  "include " ^ module_name ^ "\n" ^ ocaml_source
          in
          write_output (Some output_path) ocaml_source)
  | Compile_files_from_state
      { state_path; output_state_path; input_paths; output_path } -> (
      let produced_key = ref "" in
      match
        compile_files_from_saved_state ~use_cache:false ?reader_target
          ~produced_key target state_path input_paths
      with
      | Error err -> report_error err
      | Ok (state, packages, ocaml_source, ocaml_signatures, diagnostics) ->
          report_diagnostics diagnostics;
          write_output (Some output_path) ocaml_source;
          let saved =
            match read_saved_compilation_state state_path with
            | Ok saved -> saved
            | Error err -> report_error err
          in
          let ocaml_source =
            concatenate_compilation_outputs
              [ saved.ocaml_source; ocaml_source ]
          in
          write_saved_compilation_state output_state_path
            {
              target;
              state = Lg.Compiler.cacheable_state state;
              packages;
              ocaml_source;
              ocaml_signatures =
                saved.ocaml_signatures @ ocaml_signatures;
              cache_key = !produced_key;
            })
  | Compile_chunk_from { state_path; input_path; output_path } -> (
      match
        compile_chunk_from_saved_state ?reader_target target state_path input_path
      with
      | Error err -> report_error err
      | Ok (_state, _packages, compilation) ->
          report_diagnostics compilation.diagnostics;
          write_output output_path compilation.ocaml_source)
  | Compile_chunk_state
      { state_path; output_state_path; input_path; output_path } -> (
      let produced_key = ref "" in
      match
        compile_chunk_from_saved_state ?reader_target ~produced_key target
          state_path input_path
      with
      | Error err -> report_error err
      | Ok (state, packages, compilation) ->
          report_diagnostics compilation.diagnostics;
          write_output output_path compilation.ocaml_source;
          let saved =
            match read_saved_compilation_state state_path with
            | Ok saved -> saved
            | Error err -> report_error err
          in
          write_saved_compilation_state output_state_path
            {
              target;
              state = Lg.Compiler.cacheable_state state;
              packages;
              ocaml_source =
                concatenate_compilation_outputs
                  [ saved.ocaml_source; compilation.ocaml_source ];
              ocaml_signatures =
                saved.ocaml_signatures
                @ Option.to_list compilation.ocaml_signature;
              cache_key = !produced_key;
            })
  | Run_files { input_paths } -> (
      match compile_files ?reader_target target input_paths with
      | Error err -> report_error err
      | Ok (_state, packages, ocaml_source, _ocaml_signatures, diagnostics) ->
          report_diagnostics diagnostics;
          run_ocaml_source packages ocaml_source)
  | Run_files_from
      { state_path; implementation_path; input_paths } -> (
      match
        compile_files_from_saved_state ?reader_target target state_path input_paths
      with
      | Error err -> report_error err
      | Ok (_state, packages, ocaml_source, _ocaml_signatures, diagnostics) ->
          report_diagnostics diagnostics;
          run_ocaml_source packages
            (concatenate_compilation_outputs
               [ read_file implementation_path; ocaml_source ]))
  | Test { input_paths } -> run_tests ?reader_target target input_paths
  | Lsp { state_path } -> run_lsp state_path
