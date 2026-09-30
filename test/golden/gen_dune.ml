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

let print_paths indent paths =
  List.iter (fun path -> Printf.printf "%s%s\n" indent path) paths

let stdlib_sources =
  [
    "../../stdlib/clojure/core.lgi";
    "../../stdlib/clojure/core.cljc";
    "../../stdlib/clojure/string.lgi";
    "../../stdlib/clojure/string.cljc";
    "../../stdlib/clojure/edn.lgi";
    "../../stdlib/clojure/edn.cljc";
    "../../stdlib/cljs/reader.lgi";
    "../../stdlib/cljs/reader.cljc";
    "../../stdlib/clojure/set.lgi";
    "../../stdlib/clojure/set.cljc";
    "../../stdlib/clojure/data.lgi";
    "../../stdlib/clojure/data.cljc";
    "../../stdlib/clojure/walk.lgi";
    "../../stdlib/clojure/walk.cljc";
    "../../stdlib/clojure/zip.lgi";
    "../../stdlib/clojure/zip.cljc";
    "../../stdlib/cljs/cache.cljc";
    "../../stdlib/cljs/pprint.lgi";
    "../../stdlib/cljs/pprint.cljc";
    "../../stdlib/cljs/test.lgi";
    "../../stdlib/cljs/test.cljc";
  ]

let () =
  let cases =
    Array.to_list Sys.argv
    |> List.tl
    |> List.sort (fun left right ->
           String.compare (case_name left) (case_name right))
  in
  let names = List.map case_name cases in
  Printf.printf "(rule\n";
  Printf.printf " (targets\n";
  print_paths "  " (List.map (fun name -> name ^ ".actual") names);
  Printf.printf " )\n";
  Printf.printf " (deps\n";
  print_paths "  " stdlib_sources;
  print_paths "  " (List.map (fun name -> "cases/" ^ name ^ ".cljc") names);
  Printf.printf " )\n";
  Printf.printf " (action\n";
  Printf.printf "  (run %%{exe:golden_runner.bc} --outputs %%{targets} --stdlib";
  List.iter
    (fun path -> Printf.printf " %%{dep:%s}" path)
    stdlib_sources;
  Printf.printf " --cases";
  List.iter
    (fun name -> Printf.printf " %%{dep:cases/%s.cljc}" name)
    names;
  Printf.printf ")))\n\n";
  List.iteri
    (fun index name ->
      Printf.printf
        "(rule\n (alias runtest)\n (deps cases/%s.expected %s.actual)\n (action \
         (diff cases/%s.expected %s.actual)))\n"
        name name name name;
      if index + 1 < List.length names then print_char '\n')
    names
