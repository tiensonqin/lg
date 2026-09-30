let read_file path =
  let channel = open_in_bin path in
  Fun.protect
    ~finally:(fun () -> close_in_noerr channel)
    (fun () ->
      let length = in_channel_length channel in
      really_input_string channel length)

let write_file path contents =
  let channel = open_out_bin path in
  Fun.protect
    ~finally:(fun () -> close_out_noerr channel)
    (fun () ->
      output_string channel contents;
      flush channel)

let stdlib_sources =
  [
    "stdlib/clojure/core.lgi";
    "stdlib/clojure/core.cljc";
    "stdlib/clojure/string.lgi";
    "stdlib/clojure/string.cljc";
    "stdlib/clojure/edn.lgi";
    "stdlib/clojure/edn.cljc";
    "stdlib/cljs/reader.lgi";
    "stdlib/cljs/reader.cljc";
    "stdlib/clojure/set.lgi";
    "stdlib/clojure/set.cljc";
    "stdlib/clojure/data.lgi";
    "stdlib/clojure/data.cljc";
    "stdlib/clojure/walk.lgi";
    "stdlib/clojure/walk.cljc";
    "stdlib/clojure/zip.lgi";
    "stdlib/clojure/zip.cljc";
    "stdlib/cljs/cache.cljc";
    "stdlib/cljs/pprint.lgi";
    "stdlib/cljs/pprint.cljc";
    "stdlib/cljs/test.lgi";
    "stdlib/cljs/test.cljc";
  ]

let compile_stdlib filenames =
  let state, _ =
    List.fold_left
      (fun (state, outputs) filename ->
        let source = read_file filename in
        let state, output =
          match
            Lg.Compiler.compile_chunk_with_filename ~target:Lg.Target.default
              ~filename state source
          with
          | Ok compiled -> compiled
          | Error error ->
              failwith ("failed to compile " ^ filename ^ ": " ^ error.message)
        in
        (state, output :: outputs))
      (Lg.Compiler.empty_state, []) filenames
  in
  Lg.Compiler.with_source_scope "" state

let without_header source =
  match String.index_opt source '\n' with
  | None -> (false, source)
  | Some newline ->
      let first_line = String.sub source 0 newline in
      if String.trim first_line = ";; golden: bare" then
        (true, String.sub source (newline + 1) (String.length source - newline - 1))
      else (false, source)

let case_name path =
  let basename = Filename.basename path in
  let suffix = ".cljc" in
  let suffix_length = String.length suffix in
  if
    String.length basename >= suffix_length
    && String.sub basename
         (String.length basename - suffix_length)
         suffix_length
       = suffix
  then String.sub basename 0 (String.length basename - suffix_length)
  else basename

let output_path_for_case output_paths path =
  let expected_name = case_name path ^ ".actual" in
  match
    List.find_opt
      (fun output_path -> Filename.basename output_path = expected_name)
      output_paths
  with
  | Some output_path -> output_path
  | None -> failwith ("missing output target for " ^ path)

let source_filename path =
  "test/golden/cases/" ^ case_name path ^ ".cljc"

let compile_case ~stdlib_state path =
  let source = read_file path in
  let bare, source = without_header source in
  let filename = source_filename path in
  if bare then
    Lg.Compiler.compile_string_with_filename ~target:Lg.Target.default
      ~filename source
  else
    Lg.Compiler.compile_chunk_with_filename ~target:Lg.Target.default
      ~filename (Lazy.force stdlib_state) source
    |> Result.map snd

let output_for_case ~stdlib_state path =
  let source = read_file path in
  match compile_case ~stdlib_state path with
  | Ok _ -> "ok\n"
  | Error error ->
      let _, source = without_header source in
      Lg.Compiler.render_error ~source error ^ "\n"

let () =
  if Array.length Sys.argv < 3 then
    invalid_arg "golden_runner expects an output directory and at least one case";
  let output_paths, stdlib_paths, case_paths =
    if Sys.argv.(1) = "--outputs" then
      let rec split index outputs stdlib =
        if index >= Array.length Sys.argv then
          (List.rev outputs, List.rev stdlib, [])
        else if Sys.argv.(index) = "--stdlib" then
          split (index + 1) outputs stdlib
        else if Sys.argv.(index) = "--cases" then
          let cases =
            List.init
              (Array.length Sys.argv - index - 1)
              (fun offset -> Sys.argv.(index + offset + 1))
          in
          (List.rev outputs, List.rev stdlib, cases)
        else if List.mem "--stdlib" (Array.to_list (Array.sub Sys.argv 0 index))
        then split (index + 1) outputs (Sys.argv.(index) :: stdlib)
        else split (index + 1) (Sys.argv.(index) :: outputs) stdlib
      in
      split 2 [] []
    else
      ([], stdlib_sources, List.init
         (Array.length Sys.argv - 2)
         (fun offset -> Sys.argv.(offset + 2)))
  in
  let stdlib_state = lazy (compile_stdlib stdlib_paths) in
  List.iter
    (fun path ->
      let output_path =
        match output_paths with
        | [] -> Filename.concat Sys.argv.(1) (case_name path ^ ".actual")
        | paths -> output_path_for_case paths path
      in
      write_file output_path (output_for_case ~stdlib_state path))
    case_paths
