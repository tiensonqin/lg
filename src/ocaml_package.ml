let valid_name name =
  name <> ""
  && String.for_all
       (function
         | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | '-' | '.' -> true
         | _ -> false)
       name

let read_lines channel =
  let rec loop acc =
    match input_line channel with
    | line -> loop (if line = "" then acc else line :: acc)
    | exception End_of_file -> List.rev acc
  in
  loop []

let read_file path =
  let ic = open_in path in
  Fun.protect
    ~finally:(fun () -> close_in_noerr ic)
    (fun () ->
      let length = in_channel_length ic in
      really_input_string ic length)

let sorted_readdir directory =
  try Sys.readdir directory |> Array.to_list |> List.sort String.compare
  with Sys_error _ -> []

let contains_compiled_interface directory =
  Sys.file_exists directory && Sys.is_directory directory
  && Sys.readdir directory
     |> Array.exists (String.ends_with ~suffix:".cmi")

let expand_include_directory directory =
  let rec compiled_directories directory =
    if Sys.file_exists directory && Sys.is_directory directory then
      let children =
        Sys.readdir directory |> Array.to_list
        |> List.map (Filename.concat directory)
        |> List.filter (fun path ->
               Sys.file_exists path && Sys.is_directory path)
        |> List.concat_map compiled_directories
      in
      if contains_compiled_interface directory then directory :: children
      else children
    else []
  in
  directory :: compiled_directories directory

let unique_directories directories =
  List.fold_left
    (fun unique directory ->
      if List.mem directory unique then unique else unique @ [ directory ])
    [] directories

let rec find_project_root dir =
  if Sys.file_exists (Filename.concat dir "dune-project") then Some dir
  else
    let parent = Filename.dirname dir in
    if parent = dir then None else find_project_root parent

let rec dune_files_under directory =
  if not (Sys.file_exists directory && Sys.is_directory directory) then []
  else
    sorted_readdir directory
    |> List.concat_map (fun name ->
           let path = Filename.concat directory name in
           if List.mem name [ "_build"; ".git"; "_opam"; "node_modules" ] then
             []
           else if Sys.file_exists path && Sys.is_directory path then
             dune_files_under path
           else if name = "dune" then [ path ]
           else [])

let dune_files_cache = Hashtbl.create 4

let cached_dune_files_under root =
  match Hashtbl.find_opt dune_files_cache root with
  | Some files -> files
  | None ->
      let files = dune_files_under root in
      Hashtbl.replace dune_files_cache root files;
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

let package_library_build_dir_index_cache = Hashtbl.create 4

let package_library_build_dir_index root =
  match Hashtbl.find_opt package_library_build_dir_index_cache root with
  | Some index -> index
  | None ->
      let build_root = Filename.concat root "_build/default" in
      let archive_dirs_for_dune_file dune_file =
        let source_directory = Filename.dirname dune_file in
        let relative_directory =
          let prefix = root ^ Filename.dir_sep in
          if String.starts_with ~prefix source_directory then
            String.sub source_directory (String.length prefix)
              (String.length source_directory - String.length prefix)
          else source_directory
        in
        let build_directory = Filename.concat build_root relative_directory in
        let lines =
          try read_file dune_file |> String.split_on_char '\n'
          with Sys_error _ -> []
        in
        let rec loop current_name entries = function
          | [] -> entries
          | line :: rest ->
              let current_name =
                match line_value "name" line with
                | Some name -> Some name
                | None -> current_name
              in
              let entries =
                match line_value "public_name" line with
                | Some public_name ->
                    let library_name =
                      Option.value current_name
                        ~default:
                          (public_name
                          |> String.map (function '-' -> '_' | c -> c))
                    in
                    let object_dir =
                      Filename.concat build_directory
                        ("." ^ library_name ^ ".objs")
                    in
                    [ Filename.concat object_dir "byte";
                      Filename.concat object_dir "public_cmi" ]
                    |> List.filter contains_compiled_interface
                    |> fun dirs ->
                    if dirs = [] then entries
                    else (public_name, dirs) :: entries
                | None -> entries
              in
              loop current_name entries rest
        in
        loop None [] lines
      in
      let index =
        cached_dune_files_under root
        |> List.concat_map archive_dirs_for_dune_file
      in
      Hashtbl.replace package_library_build_dir_index_cache root index;
      index

let package_library_build_dirs root package =
  package_library_build_dir_index root
  |> List.filter_map (fun (public_name, dirs) ->
         if public_name = package then Some dirs else None)
  |> List.concat
  |> List.sort_uniq String.compare

let package_root_candidates root package =
  let add candidate candidates =
    if candidate = "" || List.mem candidate candidates then candidates
    else candidate :: candidates
  in
  let rec drop_hyphen_suffixes candidates name =
    match String.rindex_opt name '-' with
    | None -> candidates
    | Some index ->
        let prefix = String.sub name 0 index in
        drop_hyphen_suffixes (add prefix candidates) prefix
  in
  let hyphenated = String.map (function '_' -> '-' | c -> c) package in
  let first_component =
    match String.split_on_char '.' hyphenated with
    | first :: _ -> first
    | [] -> hyphenated
  in
  []
  |> add package
  |> add hyphenated
  |> add first_component
  |> fun candidates -> drop_hyphen_suffixes candidates hyphenated
  |> fun candidates -> drop_hyphen_suffixes candidates first_component
  |> add (hyphenated ^ "-ocaml")
  |> List.concat_map (fun name ->
         [ Filename.concat root name;
           Filename.concat (Filename.concat root "duniverse") name ])
  |> List.filter (fun path -> Sys.file_exists path && Sys.is_directory path)
  |> unique_directories

let package_library_build_dirs_under_candidates root package =
  package_root_candidates root package
  |> List.concat_map (fun candidate_root ->
         dune_files_under candidate_root
         |> List.concat_map (fun dune_file ->
                let source_directory = Filename.dirname dune_file in
                let relative_directory =
                  let prefix = root ^ Filename.dir_sep in
                  if String.starts_with ~prefix source_directory then
                    String.sub source_directory (String.length prefix)
                      (String.length source_directory - String.length prefix)
                  else source_directory
                in
                let build_directory =
                  Filename.concat (Filename.concat root "_build/default")
                    relative_directory
                in
                let lines =
                  try read_file dune_file |> String.split_on_char '\n'
                  with Sys_error _ -> []
                in
                let rec loop current_name dirs = function
                  | [] -> dirs
                  | line :: rest ->
                      let current_name =
                        match line_value "name" line with
                        | Some name -> Some name
                        | None -> current_name
                      in
                      let dirs =
                        match line_value "public_name" line with
                        | Some public_name when public_name = package ->
                            let library_name =
                              Option.value current_name
                                ~default:
                                  (public_name
                                  |> String.map (function '-' -> '_' | c -> c))
                            in
                            let object_dir =
                              Filename.concat build_directory
                                ("." ^ library_name ^ ".objs")
                            in
                            [ Filename.concat object_dir "byte";
                              Filename.concat object_dir "public_cmi" ]
                            |> List.filter contains_compiled_interface
                            |> List.rev_append dirs
                        | Some _ | None -> dirs
                      in
                      loop current_name dirs rest
                in
                loop None [] lines))
  |> List.sort_uniq String.compare

let local_dune_package_directories package =
  match find_project_root (Sys.getcwd ()) with
  | None -> []
  | Some root -> (
      match package_library_build_dirs_under_candidates root package with
      | _ :: _ as directories -> directories
      | [] -> package_library_build_dirs root package)

let candidate_local_dune_package_directories package =
  match find_project_root (Sys.getcwd ()) with
  | None -> []
  | Some root -> package_library_build_dirs_under_candidates root package

let skip_local_project_scan package =
  List.mem package
    [
      "alcotest";
      "alcotest.engine";
      "alcotest.stdlib_ext";
      "ctypes-foreign";
      "js_of_ocaml";
      "lg.edn-backend.native";
      "lg.rrbvec";
      "lg.runtime";
      "melange";
      "melange-edn-native";
      "re";
      "str";
      "unix";
      "yojson";
    ]

let direct_ocamlpath_directories package =
  let separator = if Sys.win32 then ';' else ':' in
  let package_components = String.split_on_char '.' package in
  [ Sys.getenv_opt "OCAMLPATH"; Sys.getenv_opt "LG_OCAML_INCLUDE_PATH" ]
  |> List.filter_map Fun.id
  |> String.concat (String.make 1 separator)
  |> String.split_on_char separator
  |> List.filter_map (fun root ->
      if root = "" then None
      else
        let directory =
          List.fold_left Filename.concat root package_components
        in
        if contains_compiled_interface directory then Some directory else None)
  |> List.concat_map expand_include_directory
  |> unique_directories

let standalone_include_directories () =
  let separator = if Sys.win32 then ';' else ':' in
  Sys.getenv_opt "LG_OCAML_INCLUDE_PATH"
  |> Option.value ~default:""
  |> String.split_on_char separator
  |> List.filter (fun root -> root <> "" && contains_compiled_interface root)
  |> List.concat_map expand_include_directory
  |> unique_directories

let query_cache = Hashtbl.create 8

let query package =
  if not (valid_name package) then
    Error.error ~code:Error_code.Interop ("invalid OCaml package name " ^ package)
  else
    let report_timings = Trace.enabled "compile.timing" in
    let started_at = if report_timings then Unix.gettimeofday () else 0.0 in
    let finish result =
      if report_timings then
        Printf.eprintf "lg: OCaml package %s include dirs: %.3fs\n%!" package
          (Unix.gettimeofday () -. started_at);
      result
    in
    let cache_key =
      package ^ "\000"
      ^ (Sys.getenv_opt "OCAMLPATH" |> Option.value ~default:"")
      ^ "\000"
      ^ (Sys.getenv_opt "LG_OCAML_INCLUDE_PATH" |> Option.value ~default:"")
      ^ "\000" ^ Sys.getcwd ()
    in
    match Hashtbl.find_opt query_cache cache_key with
    | Some result -> finish result
    | None ->
        let direct_dirs =
          direct_ocamlpath_directories package
          @ if skip_local_project_scan package then []
            else local_dune_package_directories package
        in
        let direct_dirs =
          match direct_dirs with
          | _ :: _ -> direct_dirs
          | [] when skip_local_project_scan package ->
              candidate_local_dune_package_directories package
          | [] -> []
        in
        let result =
          match direct_dirs with
          | _ :: _ as directories -> Ok (unique_directories directories)
          | [] ->
              let argv =
                [| "ocamlfind"; "query"; "-r"; "-format"; "%d"; package |]
              in
              let stdout, stdin, stderr =
                Unix.open_process_args_full "ocamlfind" argv (Unix.environment ())
              in
              let directories =
                read_lines stdout |> List.concat_map expand_include_directory
                |> List.sort_uniq String.compare
              in
              let _diagnostic = read_lines stderr in
              (match Unix.close_process_full (stdout, stdin, stderr) with
              | WEXITED 0 -> Ok (unique_directories directories)
              | WEXITED _ | WSIGNALED _ | WSTOPPED _ ->
                  Error.error ~code:Error_code.Interop ("OCaml package " ^ package ^ " was not found"))
        in
        Hashtbl.replace query_cache cache_key result;
        finish result

let include_dirs packages =
  let rec loop directories = function
    | [] -> Ok (unique_directories directories)
    | package :: rest -> (
        match query package with
        | Error _ as err -> err
        | Ok package_dirs -> loop (directories @ package_dirs) rest)
  in
  loop (standalone_include_directories ()) packages
