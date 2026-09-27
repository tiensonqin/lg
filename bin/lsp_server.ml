open Yojson.Safe.Util

type document = {
  text : string;
  analysis : (Lg.Language_service.t, Lg.Error.t) result option;
  recovered_analysis : Lg.Language_service.t option;
}

type saved_compilation_state = {
  target : Lg.Target.t;
  state : Lg.Compiler.state;
  packages : string list;
  ocaml_source : string;
  ocaml_signatures : string list;
  cache_key : string; [@warning "-69"]
}

let documents = Hashtbl.create 16
let workspace_documents = Hashtbl.create 32
let workspace_sources = Hashtbl.create 32
let workspace_index = ref None
let supports_dynamic_watched_files = ref false
let base_state = ref Lg.Compiler.empty_state
let explicit_state_path = ref false
let configured_state_path = ref None
let state_cache = Hashtbl.create 8

type state_rule = {
  state_path : string;
  source_roots : string list;
  source_files : string list;
  order : int;
}

let state_rules = ref []

let path_of_file_uri uri =
  if String.starts_with ~prefix:"file://" uri then
    String.sub uri 7 (String.length uri - 7)
  else uri

let read_file path =
  let channel = open_in_bin path in
  Fun.protect ~finally:(fun () -> close_in channel) (fun () ->
      really_input_string channel (in_channel_length channel))

let excluded_directory name =
  name = "_build" || name = "_opam" || name = "duniverse"
  || name = "node_modules"
  || name = ".build"
  || name = ".git" || (String.length name > 0 && name.[0] = '.')

let rec find_repo_root_opt directory =
  if Sys.file_exists (Filename.concat directory "dune-project") then
    Some directory
  else
    let parent = Filename.dirname directory in
    if String.equal parent directory then None else find_repo_root_opt parent

let default_state_path () =
  let executable_directory = Filename.dirname Sys.executable_name in
  let repository_state =
    find_repo_root_opt (Sys.getcwd ())
    |> Option.map (fun root ->
           Filename.concat root "stdlib/lg_stdlib_native.state")
  in
  let candidates =
    Option.to_list (Sys.getenv_opt "LG_LSP_STATE")
    @ Option.to_list (Sys.getenv_opt "LG_STDLIB_STATE")
    @ [
        Filename.concat executable_directory "../stdlib/lg_stdlib_native.state";
        Filename.concat executable_directory
          "../lib/lg/stdlib/lg_stdlib_native.state";
        Filename.concat executable_directory "lg_stdlib_native.state";
      ]
    @ Option.to_list repository_state
  in
  List.find_opt Sys.file_exists candidates

let sorted_readdir path =
  if Sys.file_exists path && Sys.is_directory path then
    try Sys.readdir path |> Array.to_list |> List.sort String.compare
    with Sys_error _ -> []
  else []

let rec dune_files path =
  if Sys.is_directory path then
    sorted_readdir path
    |> List.filter (fun name -> not (excluded_directory name))
    |> List.concat_map (fun name -> dune_files (Filename.concat path name))
  else if Filename.basename path = "dune" then [ path ]
  else []

let replace_char source target text =
  String.map (fun char -> if char = source then target else char) text

let unique_preserving_order values =
  let rec loop seen result = function
    | [] -> List.rev result
    | value :: rest when List.mem value seen -> loop seen result rest
    | value :: rest -> loop (value :: seen) (value :: result) rest
  in
  loop [] [] values

let rec state_references_in_text text offset references =
  match String.index_from_opt text offset '%' with
  | None -> List.rev references
  | Some percent when percent + 6 > String.length text ->
      List.rev references
  | Some percent ->
      let prefix = "%{lib:" in
      if
        percent + String.length prefix <= String.length text
        && String.sub text percent (String.length prefix) = prefix
      then
        let library_start = percent + String.length prefix in
        match String.index_from_opt text library_start ':' with
        | None -> List.rev references
        | Some library_end -> (
            match String.index_from_opt text (library_end + 1) '}' with
            | None -> List.rev references
            | Some reference_end ->
                let library =
                  String.sub text library_start (library_end - library_start)
                in
                let state_file =
                  String.sub text (library_end + 1) (reference_end - library_end - 1)
                in
                let references =
                  if Filename.check_suffix state_file ".state" then
                    (library, state_file) :: references
                  else references
                in
                state_references_in_text text (reference_end + 1) references)
      else state_references_in_text text (percent + 1) references

let state_references_in_dune path =
  try state_references_in_text (read_file path) 0 [] with Sys_error _ -> []

let state_path_of_reference root (library, state_file) =
  Filename.concat root
    (Filename.concat "_build/install/default/lib"
       (Filename.concat (replace_char '.' '/' library) state_file))

let project_state_candidates root =
  let dune_candidates =
    dune_files root
    |> List.concat_map state_references_in_dune
    |> List.map (state_path_of_reference root)
  in
  let fallback_candidates =
    [
      "_build/install/default/lib/lg/stdlib/lg_stdlib_native.state";
      "_build/default/stdlib/lg_stdlib_native.state";
    ]
    |> List.map (Filename.concat root)
  in
  (dune_candidates @ fallback_candidates)
  |> List.filter Sys.file_exists
  |> unique_preserving_order

let workspace_state_path root_uri =
  path_of_file_uri root_uri |> project_state_candidates |> List.find_opt Sys.file_exists

let path_is_under ~root path =
  String.equal path root
  ||
  let prefix = if String.ends_with ~suffix:"/" root then root else root ^ "/" in
  String.starts_with ~prefix path

let absolute_path_from directory path =
  if Filename.is_relative path then Filename.concat directory path else path

let split_words text =
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

let rule_blocks text =
  let prefix = "(rule" in
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

let source_roots_in_rule dune_dir words =
  let rec loop roots = function
    | "source_tree" :: path :: rest ->
        loop (absolute_path_from dune_dir path :: roots) rest
    | _ :: rest -> loop roots rest
    | [] -> List.rev roots
  in
  loop [] words

let source_files_in_rule dune_dir words =
  words
  |> List.filter (fun word ->
         (Filename.check_suffix word ".cljc" || Filename.check_suffix word ".lgi"
          || Filename.check_suffix word ".mli")
         && not (String.starts_with ~prefix:"%{" word))
  |> List.map (absolute_path_from dune_dir)

let discover_state_rules root =
  let rules =
    dune_files root
    |> List.mapi (fun dune_index dune_path ->
           let dune_dir = Filename.dirname dune_path in
           try
             read_file dune_path |> rule_blocks
             |> List.mapi (fun rule_index block ->
                    let words = split_words block in
                    let source_roots = source_roots_in_rule dune_dir words in
                    let source_files = source_files_in_rule dune_dir words in
                    state_references_in_text block 0 []
                    |> List.filter_map (fun reference ->
                           let state_path = state_path_of_reference root reference in
                           if
                             Sys.file_exists state_path
                             && (source_roots <> [] || source_files <> [])
                           then
                             Some
                               {
                                 state_path;
                                 source_roots;
                                 source_files;
                                 order = (dune_index * 1000) + rule_index;
                               }
                           else None))
             |> List.concat
           with Sys_error _ -> [])
    |> List.concat
  in
  state_rules := rules

let directory_contains_compiled_interface directory =
  Sys.file_exists directory && Sys.is_directory directory
  && (try
        Sys.readdir directory
        |> Array.exists (String.ends_with ~suffix:".cmi")
      with Sys_error _ -> false)

let workspace_compiled_interface_dirs root =
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
            && directory_contains_compiled_interface directory
          then
            directory :: directories
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

let configure_workspace_include_path root =
  let include_path =
    workspace_compiled_interface_dirs root |> String.concat ":"
  in
  if include_path <> "" then (
    Unix.putenv "LG_OCAML_INCLUDE_PATH" include_path;
    Unix.putenv "OCAMLPATH" include_path)

let load_saved_state path =
  match Lg.Compiler_artifact.read ~kind:"saved-state" ~path with
  | Ok saved ->
      Lg.Type_solver.clear_meta_solutions ();
      let saved = (saved : saved_compilation_state) in
      if saved.target <> Lg.Target.default then
        Error "saved compiler state target does not match LSP target"
      else
        Lg.Compiler.restore_ocaml_environment ~packages:saved.packages saved.state
          (match saved.ocaml_signatures with
          | [] -> [ (saved.ocaml_source, None) ]
          | signatures ->
              List.map
                (fun signature -> (saved.ocaml_source, Some signature))
                signatures)
        |> Result.map (Lg.Compiler.with_source_scope "")
        |> Result.map_error (fun (error : Lg.Compiler.compile_error) ->
               error.message)
  | Error message -> Error message

let configure_base_state = function
  | None -> ()
  | Some path -> (
      match load_saved_state path with
      | Ok state ->
          configured_state_path := Some path;
          Hashtbl.replace state_cache path state;
          base_state := state
      | Error message ->
          prerr_endline ("lg-lsp: unable to load compiler state " ^ path ^ ": " ^ message))

let matching_state_rule path =
  !state_rules
  |> List.filter_map (fun rule ->
         let exact =
           if List.exists (String.equal path) rule.source_files then
             Some max_int
           else None
         in
         let root_score =
           rule.source_roots
           |> List.filter (fun root -> path_is_under ~root path)
           |> List.map String.length
           |> List.sort (fun left right -> compare right left)
           |> List.find_opt (fun _ -> true)
         in
         match (exact, root_score) with
         | None, None -> None
         | Some score, None | None, Some score -> Some (score, rule)
         | Some exact_score, Some root_score ->
             Some (max exact_score root_score, rule))
  |> List.sort (fun (left_score, left) (right_score, right) ->
         match compare right_score left_score with
         | 0 -> compare left.order right.order
         | order -> order)
  |> List.find_opt (fun _ -> true)
  |> Option.map snd

let state_for_uri uri =
  if !explicit_state_path then !base_state
  else
    let path = path_of_file_uri uri in
    match matching_state_rule path with
    | None -> !base_state
    | Some rule -> (
        match Hashtbl.find_opt state_cache rule.state_path with
        | Some state -> state
        | None -> (
            match load_saved_state rule.state_path with
            | Ok state ->
                Hashtbl.replace state_cache rule.state_path state;
                state
            | Error message ->
                prerr_endline
                  ("lg-lsp: unable to load compiler state " ^ rule.state_path
                 ^ ": " ^ message);
                !base_state))

let analyze_document uri text =
  let state = state_for_uri uri in
  let analysis = Lg.Language_service.analyze_from_state ~filename:uri state text in
  {
    text;
    analysis = Some analysis;
    recovered_analysis =
      (match analysis with
      | Ok analysis -> Some analysis
      | Error _ -> Lg.Language_service.recover_completed_prefix ~filename:uri text);
  }

let unanalyzed_document text = { text; analysis = None; recovered_analysis = None }

let semantic_analysis document =
  match document.analysis with
  | Some (Ok analysis) -> Some analysis
  | Some (Error _) -> document.recovered_analysis
  | None -> document.recovered_analysis

let lg_source_file path =
  Filename.check_suffix path ".cljc" || Filename.check_suffix path ".lgi"
  || (Filename.check_suffix path ".mli"
      && Sys.file_exists (Filename.chop_suffix path ".mli" ^ ".cljc"))

let rec lg_files path =
  if Sys.is_directory path then
    Sys.readdir path |> Array.to_list
    |> List.filter (fun name -> not (excluded_directory name))
    |> List.concat_map (fun name -> lg_files (Filename.concat path name))
  else if lg_source_file path then [ path ]
  else []

let rebuild_workspace ?changed_uri () =
  let sources =
    Hashtbl.fold
      (fun uri disk_source sources ->
        let source =
          Hashtbl.find_opt documents uri
          |> Option.map (fun document -> document.text)
          |> Option.value ~default:disk_source
        in
        (uri, source) :: sources)
      workspace_sources []
  in
  let indexed =
    match (!workspace_index, changed_uri) with
    | Some index, Some uri ->
        let source = List.assoc uri sources in
        Lg.Language_service.update_workspace_index_from_state !base_state index
          ~filename:uri ~source
    | _ ->
        Lg.Language_service.create_workspace_index_from_state !base_state sources
        |> Result.map (fun index -> (index, List.map fst sources))
  in
  match indexed with
  | Error _ ->
      workspace_index := None;
      Hashtbl.clear workspace_documents;
      List.iter
        (fun (uri, source) ->
          let document = analyze_document uri source in
          Hashtbl.replace workspace_documents uri document;
          if Hashtbl.mem documents uri then Hashtbl.replace documents uri document)
        sources;
      List.map fst sources
  | Ok (index, affected) ->
      workspace_index := Some index;
      Hashtbl.clear workspace_documents;
      List.iter
        (fun (uri, text) ->
          match Lg.Language_service.workspace_analysis index uri with
          | None -> (
              match Lg.Language_service.workspace_error index uri with
              | None -> ()
              | Some error ->
                  let recovered = analyze_document uri text in
                  let document = { recovered with analysis = Some (Error error) } in
                  Hashtbl.replace workspace_documents uri document;
                  if Hashtbl.mem documents uri then
                    Hashtbl.replace documents uri document)
          | Some analysis ->
          let document = { text; analysis = Some (Ok analysis); recovered_analysis = Some analysis } in
          Hashtbl.replace workspace_documents uri document;
          if Hashtbl.mem documents uri then Hashtbl.replace documents uri document)
        sources;
      affected

let refresh_workspace_document ?text_override index uri =
  match Hashtbl.find_opt workspace_sources uri with
  | None -> Hashtbl.remove workspace_documents uri
  | Some disk_text ->
      let text =
        match text_override with
        | Some text -> text
        | None ->
            Hashtbl.find_opt documents uri
            |> Option.map (fun document -> document.text)
            |> Option.value ~default:disk_text
      in
      let analysis =
        match Lg.Language_service.workspace_analysis index uri with
        | Some analysis -> Ok analysis
        | None -> (
            match Lg.Language_service.workspace_error index uri with
            | Some error -> Error error
            | None -> Lg.Language_service.analyze ~filename:uri text)
      in
      let recovered_analysis =
        match analysis with
        | Ok analysis -> Some analysis
        | Error _ -> Lg.Language_service.recover_completed_prefix ~filename:uri text
      in
      let document = { text; analysis = Some analysis; recovered_analysis } in
      Hashtbl.replace workspace_documents uri document;
      if Hashtbl.mem documents uri then Hashtbl.replace documents uri document

let update_current_workspace_document uri source =
  match !workspace_index with
  | None -> rebuild_workspace ~changed_uri:uri ()
  | Some index -> (
      match
        Lg.Language_service.update_workspace_current_file_from_state
          (state_for_uri uri) index ~filename:uri ~source
      with
      | Error _ -> rebuild_workspace ~changed_uri:uri ()
      | Ok (index, affected) ->
          workspace_index := Some index;
          let affected =
            if List.mem uri affected then affected else uri :: affected
          in
          List.iter
            (fun affected_uri ->
              if affected_uri = uri then
                refresh_workspace_document ~text_override:source index affected_uri
              else refresh_workspace_document index affected_uri)
            affected;
          affected)

let remove_workspace_source uri =
  Hashtbl.remove workspace_sources uri;
  match !workspace_index with
  | None -> rebuild_workspace ()
  | Some index -> (
      match
        Lg.Language_service.remove_workspace_file_from_state !base_state index
          ~filename:uri
      with
      | Error _ -> rebuild_workspace ()
      | Ok (index, affected) ->
          workspace_index := Some index;
          List.iter
            (fun affected_uri ->
              if affected_uri = uri then
                Hashtbl.remove workspace_documents affected_uri
              else refresh_workspace_document index affected_uri)
            affected;
          affected)

let reset_unanalyzed_workspace_index () =
  let sources =
    Hashtbl.fold
      (fun uri source sources -> (uri, source) :: sources)
      workspace_sources []
  in
  workspace_index := Some (Lg.Language_service.create_unanalyzed_workspace_index sources)

let update_watched_workspace_file uri change_type =
  let previously_analyzed =
    Hashtbl.fold (fun uri _ uris -> uri :: uris) workspace_documents []
  in
  Hashtbl.clear workspace_documents;
  if change_type = 3 then (
    Hashtbl.remove workspace_sources uri;
    reset_unanalyzed_workspace_index ();
    uri :: previously_analyzed)
  else
    let path = path_of_file_uri uri in
    if lg_source_file path && Sys.file_exists path then (
      Hashtbl.replace workspace_sources uri (read_file path);
      reset_unanalyzed_workspace_index ();
      uri :: previously_analyzed)
    else []

let index_workspace root_uri =
  Hashtbl.clear workspace_sources;
  let sources =
    path_of_file_uri root_uri |> lg_files
    |> List.map (fun path ->
           let uri = "file://" ^ path in
           let source = read_file path in
           Hashtbl.replace workspace_sources uri source;
           (uri, source))
  in
  workspace_index := Some (Lg.Language_service.create_unanalyzed_workspace_index sources);
  if Sys.getenv_opt "LG_LSP_EAGER_INDEX" = Some "1" then ignore (rebuild_workspace ())

let find_document uri =
  if Hashtbl.mem workspace_sources uri then
    match Hashtbl.find_opt workspace_documents uri with
    | Some _ as document -> document
    | None -> Hashtbl.find_opt documents uri
  else Hashtbl.find_opt documents uri

let ensure_document uri =
  match find_document uri with
  | Some _ as document -> document
  | None -> (
      match Hashtbl.find_opt workspace_sources uri with
      | None -> None
      | Some source ->
          ignore (update_current_workspace_document uri source);
          find_document uri)

let ensure_analyzed_document uri document =
  match document.analysis with
  | Some _ -> document
  | None ->
      if Hashtbl.mem workspace_sources uri then (
        ignore (update_current_workspace_document uri document.text);
        find_document uri |> Option.value ~default:document)
      else
        let document = analyze_document uri document.text in
        Hashtbl.replace documents uri document;
        document

let has_analyzed_workspace_documents () =
  Hashtbl.length workspace_documents > 0

let eager_workspace_file_limit = 16

let should_eager_analyze_workspace () =
  Hashtbl.length workspace_sources <= eager_workspace_file_limit

let should_eager_publish_diagnostics () =
  Sys.getenv_opt "LG_LSP_EAGER_DIAGNOSTICS" = Some "1"

let lazy_large_workspace_document uri document =
  Hashtbl.mem workspace_sources uri
  && Option.is_none document.analysis
  && not (should_eager_analyze_workspace ())

let all_documents () =
  let combined = Hashtbl.copy workspace_documents in
  Hashtbl.iter (Hashtbl.replace combined) documents;
  combined

let find_substring text pattern =
  let pattern_length = String.length pattern in
  let rec loop index =
    if index + pattern_length > String.length text then None
    else if String.sub text index pattern_length = pattern then Some index
    else loop (index + 1)
  in
  if pattern_length = 0 then Some 0 else loop 0

let position line character =
  `Assoc [ ("line", `Int line); ("character", `Int character) ]

let position_coordinates_of_offset text target =
  let rec loop offset line character =
    if offset >= target || offset >= String.length text then
      (line, character)
    else if text.[offset] = '\n' then loop (offset + 1) (line + 1) 0
    else
      let decoded = String.get_utf_8_uchar text offset in
      let byte_length = max 1 (Uchar.utf_decode_length decoded) in
      let codepoint = Uchar.utf_decode_uchar decoded |> Uchar.to_int in
      let units = if codepoint > 0xFFFF then 2 else 1 in
      loop (offset + byte_length) line (character + units)
  in
  loop 0 0 0

let position_of_offset text target =
  let line, character = position_coordinates_of_offset text target in
  position line character

let range_of_offsets text start_offset end_offset =
  `Assoc
    [ ("start", position_of_offset text start_offset);
      ("end", position_of_offset text end_offset) ]

let range_of_location text location =
  range_of_offsets text location.Location.loc_start.Lexing.pos_cnum
    location.loc_end.Lexing.pos_cnum

let diagnostic_range text = function
  | Some location -> range_of_location text location
  | None -> range_of_offsets text 0 (min 1 (String.length text))

let source_text_for_uri uri =
  match find_document uri with
  | Some document -> Some document.text
  | None -> (
      match Hashtbl.find_opt workspace_sources uri with
      | Some source -> Some source
      | None ->
          let path = path_of_file_uri uri in
          if Sys.file_exists path && not (Sys.is_directory path) then
            try Some (read_file path) with Sys_error _ -> None
          else None)

let line_start_range (location : Location.t) =
  let line = max 0 (location.loc_start.Lexing.pos_lnum - 1) in
  `Assoc [ ("start", position line 0); ("end", position line 0) ]

let related_range location =
  let uri = location.Location.loc_start.Lexing.pos_fname in
  match source_text_for_uri uri with
  | Some source -> range_of_location source location
  | None ->
      (* A byte column is not a valid LSP UTF-16 column. If the originating
         source is unavailable, preserve the exact line without inventing a
         misleading character range. *)
      line_start_range location

let diagnostic_phase = function
  | `Lexing -> "lexing"
  | `Parsing -> "parsing"
  | `Semantic -> "semantic"
  | `Lowering -> "lowering"
  | `Ocaml -> "ocaml"
  | `Infrastructure -> "infrastructure"

let rec type_term_json = function
  | Lg.Error.Type_atom name ->
      `Assoc [ ("kind", `String "atom"); ("name", `String name) ]
  | Type_application (name, arguments) ->
      `Assoc
        [ ("kind", `String "application");
          ("name", `String name);
          ("arguments", `List (List.map type_term_json arguments)) ]
  | Type_function (parameters, return_type) ->
      `Assoc
        [ ("kind", `String "function");
          ("parameters", `List (List.map type_term_json parameters));
          ("returnType", type_term_json return_type) ]
  | Type_tuple items ->
      `Assoc
        [ ("kind", `String "tuple");
          ("items", `List (List.map type_term_json items)) ]
  | Type_record fields ->
      `Assoc
        [ ("kind", `String "record");
          ( "fields",
            `List
              (List.map
                 (fun (name, ty) ->
                   `Assoc [ ("name", `String name); ("type", type_term_json ty) ])
                 fields) ) ]

let type_path_json = function
  | Lg.Error.Type_argument index ->
      `Assoc [ ("kind", `String "typeArgument"); ("index", `Int index) ]
  | Function_parameter index ->
      `Assoc [ ("kind", `String "functionParameter"); ("index", `Int index) ]
  | Function_return -> `Assoc [ ("kind", `String "functionReturn") ]
  | Tuple_item index ->
      `Assoc [ ("kind", `String "tupleItem"); ("index", `Int index) ]
  | Record_field name ->
      `Assoc [ ("kind", `String "recordField"); ("name", `String name) ]

let type_context_json = function
  | Lg.Error.Conditional_branch ->
      `Assoc [ ("kind", `String "conditionalBranch") ]
  | Record_property { record_name; property_name } ->
      `Assoc
        [ ("kind", `String "recordProperty");
          ("record", `String record_name);
          ("property", `String property_name) ]
  | Call_argument { callee; index } ->
      `Assoc
        [ ("kind", `String "callArgument");
          ("callee", `String callee);
          ("index", `Int index) ]
  | Protocol_argument { protocol; method_name; index } ->
      `Assoc
        [ ("kind", `String "protocolArgument");
          ("protocol", `String protocol);
          ("method", `String method_name);
          ("index", `Int index) ]
  | Annotation -> `Assoc [ ("kind", `String "annotation") ]
  | Host_boundary { callee; index } ->
      `Assoc
        [ ("kind", `String "hostBoundary");
          ("callee", `String callee);
          ("index", `Int index) ]

let type_mismatch_json (mismatch : Lg.Error.type_mismatch) =
  `Assoc
    [ ("context", type_context_json mismatch.context);
      ("expected", type_term_json mismatch.expected);
      ("actual", type_term_json mismatch.actual);
      ( "difference",
        `Assoc
          [ ("path", `List (List.map type_path_json mismatch.difference.path));
            ("expected", type_term_json mismatch.difference.expected);
            ("actual", type_term_json mismatch.difference.actual) ] ) ]

let diagnostic text ?(severity = 1) ?location ?code ?phase ?title
    ?(related = []) ?(hints = []) ?type_mismatch message =
  let identity =
    match (code, phase) with
    | Some code, Some phase ->
        let data =
          [ ("phase", `String (diagnostic_phase phase)) ]
          @ Option.fold ~none:[]
              ~some:(fun mismatch ->
                [ ("typeMismatch", type_mismatch_json mismatch) ])
              type_mismatch
        in
        [ ("code", `String code);
          ("data", `Assoc data) ]
    | _ -> []
  in
  let message =
    String.concat "\n\n"
      (Option.to_list title @ [ message ]
      @ List.map (fun hint -> "Hint: " ^ hint) hints)
  in
  let related_information =
    match related with
    | [] -> []
    | related ->
        [
          ( "relatedInformation",
            `List
              (List.map
                 (fun (related : Lg.Error.related) ->
                   let uri = related.location.Location.loc_start.Lexing.pos_fname in
                   `Assoc
                     [
                       ( "location",
                         `Assoc
                           [
                             ("uri", `String uri);
                             ("range", related_range related.location);
                           ] );
                       ("message", `String related.message);
                     ])
                 related) );
        ]
  in
  `Assoc
    ([ ("range", diagnostic_range text location);
       ("severity", `Int severity);
       ("source", `String "lg");
       ("message", `String message) ]
    @ identity @ related_information)

let diagnostics document =
  match document.analysis with
  | Some (Ok analysis) ->
      List.map
        (fun (item : Lg.Compiler.diagnostic) ->
          match item.severity with
          | `Warning ->
              diagnostic document.text ~severity:2 ?location:item.location
                ~code:item.code ~phase:item.phase item.message)
        (Lg.Language_service.diagnostics analysis)
  | Some (Error err) ->
      [ diagnostic document.text ?location:err.location ~code:err.code
          ~phase:err.phase ~title:err.title ~related:err.related ~hints:err.hints
          ?type_mismatch:err.type_mismatch err.message ]
  | None -> []

let write_packet json =
  let body = Yojson.Safe.to_string json in
  Printf.printf "Content-Length: %d\r\n\r\n%s%!" (String.length body) body

let publish_diagnostics uri diagnostics =
  write_packet
    (`Assoc
      [ ("jsonrpc", `String "2.0");
        ("method", `String "textDocument/publishDiagnostics");
        ( "params",
          `Assoc
            [ ("uri", `String uri);
              ("diagnostics", `List diagnostics) ] ) ])

let publish_current_diagnostics uri =
  match ensure_document uri with
  | None -> publish_diagnostics uri []
  | Some document -> publish_diagnostics uri (diagnostics document)

let rebuild_and_publish uri =
  let affected =
    if Hashtbl.mem workspace_sources uri then
      rebuild_workspace ~changed_uri:uri ()
    else [ uri ]
  in
  let affected = if List.mem uri affected then affected else uri :: affected in
  List.iter publish_current_diagnostics affected

let read_packet () =
  let rec read_headers content_length =
    match input_line stdin with
    | exception End_of_file -> None
    | line ->
        let line = String.trim line in
        if line = "" then content_length
        else
          let prefix = "content-length:" in
          let lowercase = String.lowercase_ascii line in
          let content_length =
            if String.starts_with ~prefix lowercase then
              String.sub line (String.length prefix)
                (String.length line - String.length prefix)
              |> String.trim |> int_of_string_opt
            else content_length
          in
          read_headers content_length
  in
  match read_headers None with
  | None -> None
  | Some length -> Some (really_input_string stdin length |> Yojson.Safe.from_string)

let response id result =
  write_packet
    (`Assoc
      [ ("jsonrpc", `String "2.0"); ("id", id); ("result", result) ])

let error_response id code message =
  write_packet
    (`Assoc
      [ ("jsonrpc", `String "2.0");
        ("id", id);
        ( "error",
          `Assoc [ ("code", `Int code); ("message", `String message) ] ) ])

let register_watched_files () =
  write_packet
    (`Assoc
      [ ("jsonrpc", `String "2.0");
        ("id", `String "lg-watch-lg-files");
        ("method", `String "client/registerCapability");
        ( "params",
          `Assoc
            [ ( "registrations",
                `List
                  [ `Assoc
                      [ ("id", `String "lg-watch-lg-files");
                        ( "method",
                          `String "workspace/didChangeWatchedFiles" );
                        ( "registerOptions",
                          `Assoc
                            [ ( "watchers",
                                `List
                                  [ `Assoc
                                      [ ( "globPattern",
                                          `String "**/*.cljc" );
                                        ("kind", `Int 7) ] ] ) ] ) ] ] ) ] ) ])

let initialize_result =
  `Assoc
    [ ( "capabilities",
        `Assoc
          [ ("textDocumentSync", `Int 1);
            ("hoverProvider", `Bool true);
            ("declarationProvider", `Bool true);
            ("definitionProvider", `Bool true);
            ("typeDefinitionProvider", `Bool true);
            ("implementationProvider", `Bool true);
            ("documentFormattingProvider", `Bool true);
            ("documentRangeFormattingProvider", `Bool true);
            ("codeActionProvider", `Bool true);
            ("referencesProvider", `Bool true);
            ("documentHighlightProvider", `Bool true);
            ("renameProvider", `Assoc [ ("prepareProvider", `Bool true) ]);
            ("selectionRangeProvider", `Bool true);
            ("documentSymbolProvider", `Bool true);
            ("workspaceSymbolProvider", `Bool true);
            ("foldingRangeProvider", `Bool true);
            ("inlayHintProvider", `Bool true);
            ( "semanticTokensProvider",
              `Assoc
                [ ( "legend",
                    `Assoc
                      [ ( "tokenTypes",
                          `List
                            (List.map
                               (fun token_type -> `String token_type)
                               [ "namespace";
                                 "type";
                                 "function";
                                 "variable";
                                 "parameter";
                                 "property";
                                 "enumMember";
                                 "interface";
                                 "method";
                                 "keyword";
                                 "string";
                                 "number" ] ) );
                        ("tokenModifiers", `List []) ] );
                  ("full", `Bool true) ] );
            ( "completionProvider",
              `Assoc
                [ ("triggerCharacters", `List []);
                  ("resolveProvider", `Bool true) ] );
            ( "signatureHelpProvider",
              `Assoc
                [ ( "triggerCharacters",
                    `List [ `String " "; `String "(" ] ) ] ) ] );
      ( "serverInfo",
        `Assoc
          [ ("name", `String "lg"); ("version", `String "0.1") ] ) ]

let document_uri params =
  params |> member "textDocument" |> member "uri" |> to_string

let dynamic_watched_files_supported params =
  try
    (params |> member "capabilities" |> member "workspace"
   |> member "didChangeWatchedFiles" |> member "dynamicRegistration"
   |> to_bool_option)
    = Some true
  with Type_error _ -> false

let line_start_offset text target_line =
  let rec loop offset line =
    if line = target_line then Some offset
    else if offset >= String.length text then None
    else if text.[offset] = '\n' then loop (offset + 1) (line + 1)
    else loop (offset + 1) line
  in
  if target_line < 0 then None else loop 0 0

let offset_of_position text line character =
  match line_start_offset text line with
  | None -> String.length text
  | Some start ->
      let rec loop offset utf16_units =
        if
          offset >= String.length text || text.[offset] = '\n'
          || utf16_units >= character
        then offset
        else
          let decoded = String.get_utf_8_uchar text offset in
          let byte_length = max 1 (Uchar.utf_decode_length decoded) in
          let codepoint = Uchar.utf_decode_uchar decoded |> Uchar.to_int in
          let units = if codepoint > 0xFFFF then 2 else 1 in
          loop (offset + byte_length) (utf16_units + units)
      in
      loop start 0

let document_position params document =
  let position = params |> member "position" in
  let line = position |> member "line" |> to_int in
  let character = position |> member "character" |> to_int in
  offset_of_position document.text line character

let offset_of_lsp_position text position =
  let line = position |> member "line" |> to_int in
  let character = position |> member "character" |> to_int in
  offset_of_position text line character

let document_range_offsets params document =
  let range = params |> member "range" in
  let start_offset = offset_of_lsp_position document.text (range |> member "start") in
  let end_offset = offset_of_lsp_position document.text (range |> member "end") in
  (min start_offset end_offset, max start_offset end_offset)

let located_forms document =
  match semantic_analysis document with
  | Some analysis -> analysis.Lg.Language_service.forms
  | None -> (
      match Lg.Lexer.tokenize document.text with
      | Error _ -> []
      | Ok tokens -> (
          match
            Lg.Parser.parse_located ~eof_offset:(String.length document.text)
              tokens
          with
          | Ok forms -> forms
          | Error _ -> []))

let hover_json document (hover : Lg.Language_service.hover) =
  `Assoc
    [ ( "contents",
        `Assoc
          [ ("kind", `String "plaintext"); ("value", `String hover.contents) ]
      );
      ( "range",
        range_of_offsets document.text hover.range.start_offset
          hover.range.end_offset ) ]

let hover_result uri document offset =
  match
    Lg.Language_service.source_quick_hover ~state:(state_for_uri uri)
      ~source:document.text ~offset
  with
  | Some hover -> hover_json document hover
  | None -> (
      let document =
        if lazy_large_workspace_document uri document then document
        else ensure_analyzed_document uri document
      in
      match semantic_analysis document with
      | None -> `Null
      | Some analysis -> (
          match Lg.Language_service.hover analysis ~offset with
          | None -> `Null
          | Some hover -> hover_json document hover))

let signature_help_result document offset =
  match semantic_analysis document with
  | None -> `Null
  | Some analysis -> (
      match Lg.Language_service.signature_help analysis ~offset with
      | None -> `Null
      | Some signature ->
          `Assoc
            [ ( "signatures",
                `List
                  [ `Assoc
                      [ ("label", `String signature.label);
                        ( "parameters",
                          `List
                            (List.map
                               (fun label ->
                                 `Assoc [ ("label", `String label) ])
                               signature.parameters) ) ] ] );
              ("activeSignature", `Int 0);
              ("activeParameter", `Int signature.active_parameter) ])

let definition_result uri document offset =
  let location =
    Lg.Language_service.source_quick_definition ~filename:uri
      ~state:(state_for_uri uri) ~source:document.text ~offset
  in
  let location =
    match location with
    | Some _ as location -> location
    | None when lazy_large_workspace_document uri document -> None
    | None ->
        let document = ensure_analyzed_document uri document in
        (match semantic_analysis document with
        | Some analysis -> Lg.Language_service.definition analysis ~offset
        | None -> None)
  in
  match location with
  | None -> `Null
  | Some location ->
          let filename = location.Location.loc_start.Lexing.pos_fname in
          let definition_uri =
            if String.starts_with ~prefix:"file://" filename then filename
            else if filename = "" then uri
            else "file://" ^ filename
          in
          let definition_text =
            find_document definition_uri
            |> Option.map (fun document -> document.text)
            |> (function
                 | Some text -> text
                 | None -> (
                     let path = path_of_file_uri definition_uri in
                     try read_file path with Sys_error _ -> document.text))
          in
          `Assoc
            [ ("uri", `String definition_uri);
              ("range", range_of_location definition_text location) ]

let location_result uri document offset = definition_result uri document offset

let completion_items_json items =
  items
  |> List.map (fun (item : Lg.Language_service.completion_item) ->
         `Assoc
           [ ("label", `String item.label);
             ("kind", `Int 6);
             ("detail", `String item.detail) ])
  |> fun items ->
  `Assoc [ ("isIncomplete", `Bool false); ("items", `List items) ]

let completion_result uri document offset =
  let quick_items =
    Lg.Language_service.source_quick_completions ~state:(state_for_uri uri)
      ~source:document.text ~offset
  in
  if quick_items <> [] then completion_items_json quick_items
  else
    match semantic_analysis document with
    | None -> completion_items_json []
    | Some analysis ->
        Lg.Language_service.completions analysis ~offset
        |> completion_items_json

let completion_resolve_result item = item

let formatting_result document =
  match Lg.Formatter.format document.text with
  | Error _ -> `List []
  | Ok formatted when formatted = document.text -> `List []
  | Ok formatted ->
      `List
        [
          `Assoc
            [ ( "range",
                range_of_offsets document.text 0 (String.length document.text) );
              ("newText", `String formatted) ];
        ]

let range_formatting_result document =
  fun params ->
    let start_offset, end_offset = document_range_offsets params document in
    let source =
      String.sub document.text start_offset (end_offset - start_offset)
    in
    match Lg.Formatter.format source with
    | Error _ -> `List []
    | Ok formatted when formatted = source -> `List []
    | Ok formatted ->
        `List
          [
            `Assoc
              [ ( "range",
                  range_of_offsets document.text start_offset end_offset );
                ("newText", `String formatted) ];
          ]

let code_actions_result uri document =
  match document.analysis with
  | Some (Ok _) | None -> `List []
  | Some (Error error) ->
      error.fixes
      |> List.map (fun (fix : Lg.Error.fix) ->
             `Assoc
               [ ("title", `String fix.title);
                 ("kind", `String "quickfix");
                 ("isPreferred", `Bool true);
                 ( "edit",
                   `Assoc
                     [ ( "changes",
                         `Assoc
                           [ ( uri,
                               `List
                                 (List.map
                                    (fun (edit : Lg.Error.text_edit) ->
                                      `Assoc
                                        [ ( "range",
                                            range_of_location document.text
                                              edit.location );
                                          ("newText", `String edit.replacement) ])
                                    fix.edits) ) ] ) ] ) ])
      |> fun actions -> `List actions

let location_json uri text (range : Lg.Ast.source_span) =
  `Assoc
    [ ("uri", `String uri);
      ( "range",
        range_of_offsets text range.start_offset range.end_offset ) ]

let semantic_documents uri document =
  if Hashtbl.mem workspace_sources uri then workspace_documents
  else
    let local = Hashtbl.create 1 in
    Hashtbl.add local uri document;
    local

let symbol_at_offset document offset =
  match semantic_analysis document with
  | Some analysis -> (
      match Lg.Language_service.symbol_span_at analysis offset with
      | None -> None
      | Some span ->
          Some
            (String.sub document.text span.start_offset
               (span.end_offset - span.start_offset)))
  | None -> None

let lexical_symbol_at_offset text offset =
  match Lg.Lexer.tokenize text with
  | Error _ -> None
  | Ok tokens -> (
      tokens
      |> List.find_opt (fun (token : Lg.Ast.token) ->
             token.span.start_offset <= offset && offset < token.span.end_offset)
      |> function
      | Some { desc = Symbol symbol; _ } -> Some symbol
      | Some _ | None -> None)

let lexical_references symbol text =
  match Lg.Lexer.tokenize text with
  | Error _ -> []
  | Ok tokens ->
      let symbols =
        match String.rindex_opt symbol '/' with
        | None -> [ symbol ]
        | Some separator ->
            [
              symbol;
              String.sub symbol (separator + 1)
                (String.length symbol - separator - 1);
            ]
      in
      tokens
      |> List.filter_map (fun (token : Lg.Ast.token) ->
             match token.desc with
             | Symbol candidate when List.exists (String.equal candidate) symbols ->
                 Some token.span
             | _ -> None)

let references_result uri document offset =
  let quick_locations =
    Lg.Language_service.source_fallback_references ~source:document.text ~offset
    |> List.map (location_json uri document.text)
  in
  if quick_locations <> [] then `List quick_locations
  else if lazy_large_workspace_document uri document then
    match lexical_symbol_at_offset document.text offset with
    | None -> `List []
    | Some symbol ->
        Hashtbl.fold
          (fun reference_uri source locations ->
            lexical_references symbol source
            |> List.map (location_json reference_uri source)
            |> List.rev_append locations)
          workspace_sources []
        |> List.rev |> fun locations -> `List locations
  else
    let document = ensure_analyzed_document uri document in
    match semantic_analysis document with
    | None -> `List []
    | Some analysis -> (
      match Lg.Language_service.semantic_key_at analysis ~offset with
      | None ->
          `List []
      | Some key ->
          let target_symbol = symbol_at_offset document offset in
          Hashtbl.fold
            (fun uri document locations ->
              match semantic_analysis document with
              | None -> locations
              | Some analysis ->
                  Lg.Language_service.references_to_key analysis key
                  |> List.map (location_json uri document.text)
                  |> List.rev_append locations)
            (semantic_documents uri document) []
          |> fun semantic_locations ->
	          (if not (Hashtbl.mem workspace_sources uri) then semantic_locations
	           else
	             Hashtbl.fold
	               (fun reference_uri source locations ->
	                 if Hashtbl.mem workspace_documents reference_uri then locations
	                 else
	                   match target_symbol with
	                   | None -> locations
	                   | Some symbol ->
	                       lexical_references symbol source
	                       |> List.map (location_json reference_uri source)
	                       |> List.rev_append locations)
	               workspace_sources semantic_locations)
	          |> List.rev |> fun locations -> `List locations)

let highlights_result document offset =
  match semantic_analysis document with
  | None -> (
      match lexical_symbol_at_offset document.text offset with
      | None -> `List []
      | Some symbol ->
          lexical_references symbol document.text
          |> List.map (fun (range : Lg.Ast.source_span) ->
                 `Assoc
                   [ ( "range",
                       range_of_offsets document.text range.start_offset
                         range.end_offset );
                     ("kind", `Int 1) ])
          |> fun highlights -> `List highlights)
  | Some analysis ->
      Lg.Language_service.references analysis ~offset
      |> List.map (fun (range : Lg.Ast.source_span) ->
             `Assoc
               [ ( "range",
                   range_of_offsets document.text range.start_offset
                     range.end_offset );
                 ("kind", `Int 1) ])
      |> fun highlights -> `List highlights

let prepare_rename_result document offset =
  match semantic_analysis document with
  | None -> `Null
  | Some analysis -> (
      match Lg.Language_service.prepare_rename analysis ~offset with
      | None -> `Null
      | Some range ->
          let placeholder =
            String.sub document.text range.start_offset
              (range.end_offset - range.start_offset)
          in
          `Assoc
            [ ( "range",
                range_of_offsets document.text range.start_offset range.end_offset );
              ("placeholder", `String placeholder) ])

let rename_result uri document offset new_name =
  match semantic_analysis document with
  | None -> `Null
  | Some analysis -> (
      match Lg.Language_service.semantic_key_at analysis ~offset with
      | None -> `Null
      | Some key ->
          if not (Lg.Language_service.valid_rename_name new_name) then `Null
          else
            let changes =
              Hashtbl.fold
                (fun uri document changes ->
                  match semantic_analysis document with
                  | None -> changes
                  | Some analysis ->
                      let edits =
                        Lg.Language_service.references_to_key analysis key
                        |> List.map (fun (range : Lg.Ast.source_span) ->
                               `Assoc
                                 [ ( "range",
                                     range_of_offsets document.text
                                       range.start_offset range.end_offset );
                                   ("newText", `String new_name) ])
                      in
                      if edits = [] then changes else (uri, `List edits) :: changes)
                (semantic_documents uri document) []
            in
            `Assoc [ ("changes", `Assoc (List.rev changes)) ])

let symbol_kind = function
  | `Module -> 2
  | `Type -> 5
  | `Method -> 6
  | `Field -> 8
  | `Constructor -> 9
  | `Interface -> 11
  | `Function -> 12
  | `Variable -> 13

let rec document_symbol_json text (symbol : Lg.Language_service.document_symbol) =
  `Assoc
    [ ("name", `String symbol.name);
      ("kind", `Int (symbol_kind symbol.kind));
      ( "range",
        range_of_offsets text symbol.range.start_offset symbol.range.end_offset );
      ( "selectionRange",
        range_of_offsets text symbol.selection_range.start_offset
          symbol.selection_range.end_offset );
      ("children", `List (List.map (document_symbol_json text) symbol.children)) ]

let document_symbols_result document =
  match semantic_analysis document with
  | None -> `List []
  | Some analysis ->
      Lg.Language_service.document_symbols analysis
      |> List.map (document_symbol_json document.text)
      |> fun symbols -> `List symbols

let span_contains_offset (span : Lg.Ast.source_span) offset =
  span.start_offset <= offset && offset <= span.end_offset

let span_line_bounds text (span : Lg.Ast.source_span) =
  let start_line, start_character =
    position_coordinates_of_offset text span.start_offset
  in
  let end_line, end_character =
    position_coordinates_of_offset text span.end_offset
  in
  (start_line, start_character, end_line, end_character)

let folding_range_json text (span : Lg.Ast.source_span) =
  let start_line, start_character, end_line, end_character =
    span_line_bounds text span
  in
  `Assoc
    [ ("startLine", `Int start_line);
      ("startCharacter", `Int start_character);
      ("endLine", `Int end_line);
      ("endCharacter", `Int end_character);
      ("kind", `String "region") ]

let rec folding_spans_of_form (form : Lg.Ast.located_form) =
  let nested = List.concat_map folding_spans_of_form form.children in
  form.span :: nested

let folding_ranges_result document =
  located_forms document |> List.concat_map folding_spans_of_form
  |> List.filter (fun span ->
         let start_line, _, end_line, _ = span_line_bounds document.text span in
         end_line > start_line)
  |> List.sort_uniq compare
  |> List.map (folding_range_json document.text)
  |> fun ranges -> `List ranges

let rec selection_spans_at_offset offset (form : Lg.Ast.located_form) =
  if not (span_contains_offset form.span offset) then []
  else
    let nested =
      form.children
      |> List.concat_map (selection_spans_at_offset offset)
    in
    form.span :: nested

let selection_range_chain text fallback_offset spans =
  let spans =
    spans
    |> List.sort (fun (left : Lg.Ast.source_span) right ->
           Int.compare
             (left.end_offset - left.start_offset)
             (right.end_offset - right.start_offset))
  in
  let rec build = function
    | [] ->
        `Assoc
          [
            ( "range",
              range_of_offsets text fallback_offset fallback_offset );
          ]
    | [ (span : Lg.Ast.source_span) ] ->
        `Assoc
          [
            ( "range",
              range_of_offsets text span.start_offset span.end_offset );
          ]
    | (span : Lg.Ast.source_span) :: rest ->
        let fields =
          [
            ( "range",
              range_of_offsets text span.start_offset span.end_offset );
          ]
        in
        let parent = build rest in
        `Assoc (fields @ [ ("parent", parent) ])
  in
  build spans

let selection_ranges_result document params =
  let positions = params |> member "positions" |> to_list in
  let forms = located_forms document in
  positions
  |> List.map (fun position ->
         let offset = offset_of_lsp_position document.text position in
         forms
         |> List.concat_map (selection_spans_at_offset offset)
         |> List.sort_uniq compare
         |> selection_range_chain document.text offset)
  |> fun ranges -> `List ranges

let inlay_hint_for_symbol document analysis
    (symbol : Lg.Language_service.document_symbol) =
  match symbol.kind with
  | `Variable | `Function -> (
      match
        Lg.Language_service.hover analysis
          ~offset:symbol.selection_range.start_offset
      with
      | None -> None
      | Some hover -> (
          match String.index_opt hover.contents ':' with
          | None -> None
          | Some separator ->
              let type_name =
                String.sub hover.contents (separator + 1)
                  (String.length hover.contents - separator - 1)
                |> String.trim
              in
              if String.equal type_name "" then None
              else
                Some
                  (`Assoc
                    [ ( "position",
                        position_of_offset document.text
                          symbol.selection_range.end_offset );
                      ("label", `String (": " ^ type_name));
                      ("kind", `Int 1) ])))
  | `Module | `Type | `Interface | `Method | `Field | `Constructor -> None

let inlay_hints_result document params =
  match semantic_analysis document with
  | None -> `List []
  | Some analysis ->
      let start_offset, end_offset = document_range_offsets params document in
      Lg.Language_service.document_symbols analysis
      |> List.filter (fun (symbol : Lg.Language_service.document_symbol) ->
             symbol.selection_range.start_offset >= start_offset
             && symbol.selection_range.end_offset <= end_offset)
      |> List.filter_map (inlay_hint_for_symbol document analysis)
      |> fun hints -> `List hints

let lexical_symbol_kind = function
  | "module" | "module-alias" | "module-apply" | "module-functor" -> Some 2
  | "def" | "defonce" -> Some 13
  | "defn" | "defn-" -> Some 12
  | "type-alias" | "type-record" | "type-variant" -> Some 5
  | "defprotocol" | "module-signature" -> Some 11
  | _ -> None

let rec lexical_workspace_symbols_of_form uri text query
    (form : Lg.Ast.located_form) =
  match form.children with
  | { form = FSymbol head; _ } :: { form = FSymbol name; span; _ } :: rest ->
      let children =
        match head with
        | "module" | "module-functor" ->
            List.concat_map (lexical_workspace_symbols_of_form uri text query) rest
        | _ -> []
      in
      let current =
        match lexical_symbol_kind head with
        | Some kind when find_substring (String.lowercase_ascii name) query <> None
          ->
            [
              `Assoc
                [
                  ("name", `String name);
                  ("kind", `Int kind);
                  ("location", location_json uri text span);
                ];
            ]
        | Some _ | None -> []
      in
      current @ children
  | _ -> []

let lexical_workspace_symbols uri text query =
  match Lg.Lexer.tokenize text with
  | Error _ -> []
  | Ok tokens -> (
      match
        Lg.Parser.parse_located ~eof_offset:(String.length text) tokens
      with
      | Error _ -> []
      | Ok forms ->
          List.concat_map
            (lexical_workspace_symbols_of_form uri text query)
            forms)

let rec matching_workspace_symbols uri text query
    (symbol : Lg.Language_service.document_symbol) =
  let children =
    List.concat_map (matching_workspace_symbols uri text query) symbol.children
  in
  if find_substring (String.lowercase_ascii symbol.name) query = None then children
  else
    `Assoc
      [ ("name", `String symbol.name);
        ("kind", `Int (symbol_kind symbol.kind));
        ("location", location_json uri text symbol.selection_range) ]
    :: children

let workspace_symbols_result query =
  let query = String.lowercase_ascii query in
  Hashtbl.fold
    (fun uri document symbols ->
      match semantic_analysis document with
      | None -> symbols
      | Some analysis ->
          Lg.Language_service.document_symbols analysis
          |> List.concat_map
               (matching_workspace_symbols uri document.text query)
          |> List.rev_append symbols)
    (all_documents ()) []
  |> fun semantic_symbols ->
  Hashtbl.fold
    (fun uri source symbols ->
      if Hashtbl.mem workspace_documents uri then symbols
      else lexical_workspace_symbols uri source query |> List.rev_append symbols)
    workspace_sources semantic_symbols
  |> List.rev |> fun symbols -> `List symbols

let semantic_token_type = function
  | `Namespace -> 0
  | `Type -> 1
  | `Function -> 2
  | `Variable -> 3
  | `Parameter -> 4
  | `Property -> 5
  | `Enum_member -> 6
  | `Interface -> 7
  | `Method -> 8
  | `Keyword -> 9
  | `String -> 10
  | `Number -> 11

let semantic_token_segments text
    (token : Lg.Language_service.semantic_token) =
  let rec loop segment_start offset segments =
    if offset >= token.range.end_offset then
      if segment_start < offset then (segment_start, offset, token.kind) :: segments
      else segments
    else if text.[offset] = '\n' then
      let segments =
        if segment_start < offset then
          (segment_start, offset, token.kind) :: segments
        else segments
      in
      loop (offset + 1) (offset + 1) segments
    else
      let decoded = String.get_utf_8_uchar text offset in
      loop segment_start
        (offset + max 1 (Uchar.utf_decode_length decoded))
        segments
  in
  loop token.range.start_offset token.range.start_offset [] |> List.rev

let semantic_tokens_result document =
  match semantic_analysis document with
  | None -> `Assoc [ ("data", `List []) ]
  | Some analysis ->
      let segments =
        Lg.Language_service.semantic_tokens analysis
        |> List.concat_map (semantic_token_segments document.text)
      in
      let _, _, reversed_data =
        List.fold_left
          (fun (previous_line, previous_character, data)
               (start_offset, end_offset, kind) ->
            let line, character =
              position_coordinates_of_offset document.text start_offset
            in
            let end_line, end_character =
              position_coordinates_of_offset document.text end_offset
            in
            let length =
              if end_line = line then end_character - character else 0
            in
            let delta_line = line - previous_line in
            let delta_start =
              if delta_line = 0 then character - previous_character else character
            in
            ( line,
              character,
              0 :: semantic_token_type kind :: length :: delta_start :: delta_line
              :: data ))
          (0, 0, []) segments
      in
      `Assoc
        [ ( "data",
            `List
              (List.rev_map (fun value -> `Int value) reversed_data) ) ]

let handle_notification method_ params =
  match method_ with
  | "textDocument/didOpen" ->
      let document = params |> member "textDocument" in
      let uri = document |> member "uri" |> to_string in
      let text = document |> member "text" |> to_string in
      if Hashtbl.mem workspace_sources uri then (
        if should_eager_publish_diagnostics () && should_eager_analyze_workspace () then
          update_current_workspace_document uri text
          |> List.iter publish_current_diagnostics
        else (
          Hashtbl.replace workspace_sources uri text;
          Hashtbl.replace documents uri (unanalyzed_document text);
          reset_unanalyzed_workspace_index ();
          publish_current_diagnostics uri))
      else (
        let document = analyze_document uri text in
        Hashtbl.replace documents uri document;
        publish_current_diagnostics uri)
  | "textDocument/didChange" ->
      let uri = document_uri params in
      let changes = params |> member "contentChanges" |> to_list in
      (match changes with
      | change :: _ ->
          let text = change |> member "text" |> to_string in
          if Hashtbl.mem workspace_sources uri then (
            let update_semantics = has_analyzed_workspace_documents () in
            Hashtbl.replace workspace_sources uri text;
            if update_semantics then
              let affected = rebuild_workspace () in
              let affected =
                if List.mem uri affected then affected else uri :: affected
              in
              List.iter publish_current_diagnostics affected
            else (
              Hashtbl.replace documents uri (unanalyzed_document text);
              reset_unanalyzed_workspace_index ();
              publish_current_diagnostics uri))
          else (
            let document = analyze_document uri text in
            Hashtbl.replace documents uri document;
            publish_current_diagnostics uri)
      | [] -> ())
  | "textDocument/didSave" ->
      let uri = document_uri params in
      let text =
        match params |> member "text" with
        | `String text -> Some text
        | _ -> Hashtbl.find_opt documents uri |> Option.map (fun doc -> doc.text)
      in
      Option.iter
        (fun text ->
          let document = analyze_document uri text in
          Hashtbl.replace documents uri document;
          rebuild_and_publish uri)
        text
  | "textDocument/didClose" ->
      let uri = document_uri params in
      Hashtbl.remove documents uri;
      let affected =
        if Hashtbl.mem workspace_sources uri then
          rebuild_workspace ~changed_uri:uri ()
        else []
      in
      List.iter
        (fun affected_uri ->
          if affected_uri <> uri then publish_current_diagnostics affected_uri)
        affected;
      publish_diagnostics uri []
  | "workspace/didChangeWatchedFiles" ->
      params |> member "changes" |> to_list
      |> List.concat_map (fun change ->
             let uri = change |> member "uri" |> to_string in
             let change_type = change |> member "type" |> to_int in
             update_watched_workspace_file uri change_type)
      |> List.sort_uniq String.compare
      |> List.iter publish_current_diagnostics
  | "initialized" -> ()
  | "exit" -> ()
  | _ -> ()

let rec loop shutdown_requested =
  match read_packet () with
  | None -> ()
  | Some json ->
      let method_ = json |> member "method" |> to_string_option in
      let id = json |> member "id" in
      let params = json |> member "params" in
      (match (method_, id) with
      | Some "initialize", (`Int _ | `String _) ->
          supports_dynamic_watched_files := dynamic_watched_files_supported params;
          (match params |> member "rootUri" with
          | `String root_uri ->
              let root = path_of_file_uri root_uri in
              configure_workspace_include_path root;
              discover_state_rules root;
              if !explicit_state_path then
                configure_base_state !configured_state_path
              else configure_base_state (workspace_state_path root_uri);
              index_workspace root_uri
          | _ -> ());
          response id initialize_result;
          loop shutdown_requested
      | Some "shutdown", (`Int _ | `String _) ->
          response id `Null;
          loop true
      | Some ("textDocument/hover" as method_), (`Int _ | `String _)
      | Some ("textDocument/declaration" as method_), (`Int _ | `String _)
      | Some ("textDocument/definition" as method_), (`Int _ | `String _)
      | Some ("textDocument/typeDefinition" as method_), (`Int _ | `String _)
      | Some ("textDocument/implementation" as method_), (`Int _ | `String _)
      | Some ("textDocument/completion" as method_), (`Int _ | `String _)
      | Some ("textDocument/signatureHelp" as method_), (`Int _ | `String _) ->
          let uri = document_uri params in
          let result =
            match ensure_document uri with
            | None -> `Null
            | Some document ->
                let offset = document_position params document in
                (match method_ with
                | "textDocument/hover" ->
                    hover_result uri document offset
                | "textDocument/declaration" ->
                    location_result uri document offset
                | "textDocument/definition" ->
                    definition_result uri document offset
                | "textDocument/typeDefinition" ->
                    location_result uri document offset
                | "textDocument/implementation" ->
                    location_result uri document offset
                | "textDocument/completion" ->
                    completion_result uri document offset
                | "textDocument/signatureHelp" ->
                    signature_help_result document offset
                | _ -> `Null)
          in
          response id result;
          loop shutdown_requested
      | Some "completionItem/resolve", (`Int _ | `String _) ->
          response id (completion_resolve_result params);
          loop shutdown_requested
      | Some "textDocument/formatting", (`Int _ | `String _) ->
          let uri = document_uri params in
          let result =
            match ensure_document uri with
            | None -> `List []
            | Some document -> formatting_result document
          in
          response id result;
          loop shutdown_requested
      | Some "textDocument/rangeFormatting", (`Int _ | `String _) ->
          let uri = document_uri params in
          let result =
            match ensure_document uri with
            | None -> `List []
            | Some document -> range_formatting_result document params
          in
          response id result;
          loop shutdown_requested
      | Some "textDocument/codeAction", (`Int _ | `String _) ->
          let uri = document_uri params in
          let result =
            match ensure_document uri with
            | None -> `List []
            | Some document -> code_actions_result uri document
          in
          response id result;
          loop shutdown_requested
      | Some ("textDocument/references" as method_), (`Int _ | `String _)
      | Some ("textDocument/documentHighlight" as method_), (`Int _ | `String _)
      | Some ("textDocument/prepareRename" as method_), (`Int _ | `String _)
      | Some ("textDocument/rename" as method_), (`Int _ | `String _) ->
          let uri = document_uri params in
          let result =
            match ensure_document uri with
            | None -> `Null
            | Some document ->
                let offset = document_position params document in
                (match method_ with
                | "textDocument/references" ->
                    references_result uri document offset
                | "textDocument/documentHighlight" ->
                    highlights_result document offset
                | "textDocument/prepareRename" ->
                    prepare_rename_result document offset
                | "textDocument/rename" ->
                    let new_name = params |> member "newName" |> to_string in
                    rename_result uri document offset new_name
                | _ -> `Null)
          in
          response id result;
          loop shutdown_requested
      | Some "textDocument/documentSymbol", (`Int _ | `String _) ->
          let uri = document_uri params in
          let result =
            match ensure_document uri with
            | None -> `List []
            | Some document -> document_symbols_result document
          in
          response id result;
          loop shutdown_requested
      | Some "textDocument/foldingRange", (`Int _ | `String _) ->
          let uri = document_uri params in
          let result =
            match ensure_document uri with
            | None -> `List []
            | Some document -> folding_ranges_result document
          in
          response id result;
          loop shutdown_requested
      | Some "textDocument/selectionRange", (`Int _ | `String _) ->
          let uri = document_uri params in
          let result =
            match ensure_document uri with
            | None -> `List []
            | Some document -> selection_ranges_result document params
          in
          response id result;
          loop shutdown_requested
      | Some "workspace/symbol", (`Int _ | `String _) ->
          let query = params |> member "query" |> to_string in
          response id (workspace_symbols_result query);
          loop shutdown_requested
      | Some "textDocument/inlayHint", (`Int _ | `String _) ->
          let uri = document_uri params in
          let result =
            match ensure_document uri with
            | None -> `List []
            | Some document -> inlay_hints_result document params
          in
          response id result;
          loop shutdown_requested
      | Some "textDocument/semanticTokens/full", (`Int _ | `String _) ->
          let uri = document_uri params in
          let result =
            match ensure_document uri with
            | None -> `Assoc [ ("data", `List []) ]
            | Some document -> semantic_tokens_result document
          in
          response id result;
          loop shutdown_requested
      | Some "exit", `Null -> if shutdown_requested then () else exit 1
      | Some method_, `Null ->
          handle_notification method_ params;
          loop shutdown_requested
      | Some method_, (`Int _ | `String _) ->
          error_response id (-32601) ("unsupported request " ^ method_);
          loop shutdown_requested
      | _ -> loop shutdown_requested)

let usage () =
  prerr_endline "Usage: lg-lsp [--state <saved-state>]";
  exit 2

let parse_args argv =
  let rec loop state_path = function
    | [] -> state_path
    | "--state" :: path :: rest -> loop (Some path) rest
    | [ "--state" ] -> usage ()
    | _ -> usage ()
  in
  loop None (List.tl (Array.to_list argv))

let run ?state_path () =
  let state_path =
    match state_path with
    | Some _ as state_path -> state_path
    | None -> parse_args Sys.argv
  in
  let state_path_was_explicit = Option.is_some state_path in
  let state_path =
    match state_path with Some _ -> state_path | None -> default_state_path ()
  in
  explicit_state_path := state_path_was_explicit;
  configured_state_path := state_path;
  loop false
