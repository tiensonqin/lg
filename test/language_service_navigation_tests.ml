let fail message = failwith message

let expect_substring_index source fragment =
  let fragment_length = String.length fragment in
  let rec search index =
    if index + fragment_length > String.length source then
      fail ("missing source fragment: " ^ fragment)
    else if String.sub source index fragment_length = fragment then index
    else search (index + 1)
  in
  search 0

let string_contains_substring text pattern =
  let pattern_length = String.length pattern in
  let text_length = String.length text in
  let rec search index =
    if pattern_length = 0 then true
    else if index + pattern_length > text_length then false
    else if String.sub text index pattern_length = pattern then true
    else search (index + 1)
  in
  search 0

let expect_definition analysis ~source ~fragment =
  let offset = expect_substring_index source fragment in
  match Lg.Language_service.definition analysis ~offset with
  | Some location -> location
  | None ->
      let hover =
        Lg.Language_service.hover analysis ~offset
        |> Option.map (fun hover -> hover.Lg.Language_service.contents)
        |> Option.value ~default:"<none>"
      in
      let references =
        Lg.Language_service.references analysis ~offset |> List.length
      in
      fail
        (Printf.sprintf "expected definition for %s; hover=%s; refs=%d"
           fragment hover references)

let expect_ok = function
  | Ok value -> value
  | Error error -> fail error.Lg.Error.message

let mkdir_p path =
  let rec loop path =
    if Sys.file_exists path then ()
    else (
      loop (Filename.dirname path);
      Sys.mkdir path 0o755)
  in
  loop path

type saved_compilation_state = {
  target : Lg.Target.t;
  state : Lg.Compiler.state;
  packages : string list;
  ocaml_source : string;
  ocaml_signatures : string list;
  cache_key : string; [@warning "-69"]
}

let stdlib_state_path () =
  match Sys.argv with
  | [| _; path |] -> path
  | _ -> fail "expected stdlib state path"

let stdlib_state () =
  match
    Lg.Compiler_artifact.read ~kind:"saved-state" ~path:(stdlib_state_path ())
  with
  | Ok (saved : saved_compilation_state) ->
      if saved.target <> Lg.Target.Native then
        fail "expected native stdlib state";
      Lg.Compiler.restore_ocaml_environment ~packages:saved.packages saved.state
        (match saved.ocaml_signatures with
        | [] -> [ (saved.ocaml_source, None) ]
        | signatures ->
            List.map
              (fun signature -> (saved.ocaml_source, Some signature))
              signatures)
      |> Result.map (Lg.Compiler.with_source_scope "")
      |> (function
           | Ok state -> state
           | Error error -> fail error.message)
  | Error message -> fail message

let test_require_aliases_resolve_ocaml_module_navigation () =
  let source =
    {|
(ns nav.demo
  (:require [ocaml.Stdlib :as stdlib]))

(defn boom [] (stdlib/failwith "boom"))
|}
  in
  let analysis =
    Lg.Language_service.analyze ~filename:"file:///tmp/nav_demo.cljc" source
    |> expect_ok
  in
  let module_location =
    expect_definition analysis ~source ~fragment:"ocaml.Stdlib"
  in
  if module_location.loc_start.pos_cnum
     <> expect_substring_index source "ocaml.Stdlib"
  then
    fail "external module fallback should point at the require target";
  let alias_location =
    expect_definition analysis ~source ~fragment:"stdlib]"
  in
  if alias_location.loc_start.pos_cnum
     <> expect_substring_index source "ocaml.Stdlib"
  then
    fail "require alias should resolve to its target namespace";
  let member_location =
    expect_definition analysis ~source ~fragment:"failwith"
  in
  if member_location.Location.loc_ghost then
    fail "qualified OCaml alias members should resolve to a real definition";
  let qualifier_location =
    expect_definition analysis ~source ~fragment:"stdlib/failwith"
  in
  if qualifier_location.loc_start.pos_cnum
     <> expect_substring_index source "ocaml.Stdlib"
  then
    fail "qualified OCaml aliases should resolve to their require target"

let test_core_functions_resolve_navigation () =
  let source =
    {|
(ns nav.core)
(def stored (atom 1))
(def updated (reset! stored 2))
(def mapped (map inc [1 2]))
|}
  in
  let analysis =
    Lg.Language_service.analyze_from_state ~filename:"file:///tmp/nav_core.cljc"
      (stdlib_state ()) source
    |> expect_ok
  in
  let atom_offset = expect_substring_index source "atom" in
  let reset_offset = expect_substring_index source "reset!" in
  ignore (expect_definition analysis ~source ~fragment:"atom");
  ignore (expect_definition analysis ~source ~fragment:"reset!");
  if
    Lg.Language_service.references analysis ~offset:atom_offset
    |> List.map (fun (span : Lg.Ast.source_span) -> span.start_offset)
    <> [ atom_offset ]
  then fail "expected source fallback references for atom";
  if
    Lg.Language_service.references analysis ~offset:reset_offset
    |> List.map (fun (span : Lg.Ast.source_span) -> span.start_offset)
    <> [ reset_offset ]
  then fail "expected source fallback references for reset!";
  (match
     Lg.Language_service.hover analysis
       ~offset:(expect_substring_index source "map inc")
   with
  | Some hover
    when String.starts_with ~prefix:"(signature clojure.core/map "
           hover.Lg.Language_service.contents
         && string_contains_substring hover.contents ":overload<"
         && not (string_contains_substring hover.contents "Runtime_reduced") ->
      ()
  | Some hover -> fail ("unexpected source-level map hover: " ^ hover.contents)
  | None -> fail "expected source-level map hover")

let test_core_functions_resolve_from_duniverse_lg_stdlib () =
  let root =
    Filename.concat (Filename.get_temp_dir_name ())
      ("lg-navigation-" ^ string_of_int (Unix.getpid ()))
  in
  let source_dir = Filename.concat root "lg/demo" in
  let stdlib_dir = Filename.concat root "duniverse/lg/stdlib/clojure" in
  mkdir_p source_dir;
  mkdir_p stdlib_dir;
  Out_channel.with_open_text (Filename.concat root "dune-project")
    (fun channel -> output_string channel "(lang dune 3.20)\n");
  Out_channel.with_open_text
    (Filename.concat stdlib_dir "core.cljc")
    (fun channel ->
      output_string channel "(ns clojure.core)\n(defn atom [value] value)\n");
  let source = "(ns nav.core)\n(def stored (atom 1))\n" in
  let analysis =
    Lg.Language_service.analyze_from_state
      ~filename:
        ("file://" ^ Filename.concat source_dir "core.cljc")
      (stdlib_state ()) source
    |> expect_ok
  in
  let location = expect_definition analysis ~source ~fragment:"atom" in
  if
    location.loc_start.pos_fname
    <> Filename.concat stdlib_dir "core.cljc"
  then
    fail
      ("expected duniverse lg stdlib source, got "
      ^ location.loc_start.pos_fname)

let test_quick_definition_resolves_without_semantic_analysis () =
  let root =
    Filename.concat (Filename.get_temp_dir_name ())
      ("lg-quick-definition-" ^ string_of_int (Unix.getpid ()))
  in
  let source_dir = Filename.concat root "lg/demo" in
  let stdlib_dir = Filename.concat root "duniverse/lg/stdlib/clojure" in
  mkdir_p source_dir;
  mkdir_p stdlib_dir;
  Out_channel.with_open_text (Filename.concat root "dune-project")
    (fun channel -> output_string channel "(lang dune 3.20)\n");
  Out_channel.with_open_text
    (Filename.concat stdlib_dir "core.cljc")
    (fun channel ->
      output_string channel
        "(ns clojure.core)\n(defn atom [value] value)\n");
  let source =
    {|
(ns nav.quick
  (:require [ocaml.Stdlib :as stdlib]))

(def stored (atom 1))
(def rendered (stdlib/string-of-int stored))
(defn boom [] (stdlib/failwith "boom"))
|}
  in
  let filename = "file://" ^ Filename.concat source_dir "quick.cljc" in
  let quick fragment =
    Lg.Language_service.source_quick_definition ~filename
      ~state:(stdlib_state ()) ~source
      ~offset:(expect_substring_index source fragment)
  in
  (match quick "ocaml.Stdlib" with
  | Some location when location.loc_start.pos_cnum = expect_substring_index source "ocaml.Stdlib" -> ()
  | Some _ -> fail "quick require target should point at the require target"
  | None -> fail "quick require target definition missing");
  (match quick "failwith" with
  | Some location when not location.Location.loc_ghost -> ()
  | Some _ -> fail "quick alias member should resolve to a real OCaml location"
  | None -> fail "quick alias member definition missing");
  (match quick "string-of-int" with
  | Some location
    when (not location.Location.loc_ghost)
         && String.ends_with ~suffix:"stdlib.mli"
              location.Location.loc_start.pos_fname ->
      ()
  | Some location ->
      fail
        ("quick stdlib member used wrong location: "
       ^ location.loc_start.pos_fname)
  | None -> fail "quick stdlib member definition missing");
  (match quick "atom 1" with
  | Some location
    when location.loc_start.pos_fname = Filename.concat stdlib_dir "core.cljc" ->
      ()
  | Some location ->
      fail ("quick core definition used wrong file: " ^ location.loc_start.pos_fname)
  | None -> fail "quick core definition missing")

let test_quick_hover_resolves_without_semantic_analysis () =
  let source =
    {|
(ns nav.quick-hover
  (:require [ocaml.Stdlib :as stdlib]))

(def stored (atom 1))
(def rendered (stdlib/string-of-int stored))
(defn boom [] (stdlib/failwith "boom"))
|}
  in
  let state = stdlib_state () in
  let quick fragment =
    Lg.Language_service.source_quick_hover ~state ~source
      ~offset:(expect_substring_index source fragment)
  in
  (match quick "failwith" with
  | Some hover
    when String.starts_with ~prefix:"failwith : string ->"
           hover.Lg.Language_service.contents ->
      ()
  | Some hover ->
      fail ("unexpected quick alias member hover: " ^ hover.contents)
  | None -> fail "quick alias member hover missing");
  (match quick "string-of-int" with
  | Some hover
    when String.starts_with ~prefix:"string-of-int : int -> string"
           hover.Lg.Language_service.contents ->
      ()
  | Some hover ->
      fail ("unexpected quick stdlib member hover: " ^ hover.contents)
  | None -> fail "quick stdlib member hover missing");
  (match quick "atom 1" with
  | Some hover
    when String.starts_with ~prefix:"(signature clojure.core/atom "
           hover.contents ->
      ()
  | Some hover -> fail ("unexpected quick core hover: " ^ hover.contents)
  | None -> fail "quick core hover missing")

let test_quick_completion_resolves_qualified_alias_members () =
  let source =
    {|
(ns nav.quick-completion
  (:require [ocaml.Stdlib :as stdlib]))

(def rendered (stdlib/))
|}
  in
  let completions =
    Lg.Language_service.source_quick_completions ~state:(stdlib_state ())
      ~source
      ~offset:(expect_substring_index source "stdlib/" + String.length "stdlib/")
  in
  if
    not
      (List.exists
         (fun (item : Lg.Language_service.completion_item) ->
           String.equal item.label "string-of-int"
           && String.equal item.detail "int -> string")
         completions)
  then fail "quick stdlib completion should include string-of-int";
  if
    not
      (List.exists
         (fun (item : Lg.Language_service.completion_item) ->
           String.equal item.label "result" && String.equal item.detail "type")
         completions)
  then fail "quick stdlib completion should include type names"

let test_quick_completion_resolves_qualified_constructors () =
  let source =
    {|
(ns nav.quick-constructor
  (:require [ocaml.Stdlib :as stdlib]))

(def rendered (stdlib/))
|}
  in
  let completions =
    Lg.Language_service.source_quick_completions ~state:(stdlib_state ())
      ~source
      ~offset:(expect_substring_index source "stdlib/" + String.length "stdlib/")
  in
  List.iter
    (fun expected ->
      if
        not
          (List.exists
             (fun (item : Lg.Language_service.completion_item) ->
               String.equal item.label expected
               && String.equal item.detail "constructor")
             completions)
      then fail ("quick alias completion should include " ^ expected))
    [ "Ok"; "Error" ]

let () =
  test_require_aliases_resolve_ocaml_module_navigation ();
  test_core_functions_resolve_navigation ();
  test_core_functions_resolve_from_duniverse_lg_stdlib ();
  test_quick_definition_resolves_without_semantic_analysis ();
  test_quick_hover_resolves_without_semantic_analysis ();
  test_quick_completion_resolves_qualified_alias_members ();
  test_quick_completion_resolves_qualified_constructors ()
