(* lg — the lg compiler driver.

   usage: lg check  <file.lg> [-I dir]...
          lg emit   <file.lg> [-o out.ml] [-I dir]...
          lg modes  <file.lg> [-I dir]...        (locality/ownership report)
          lg build  <file.lg> [-o out] [-I dir]... (emit + ocamlfind/ocamlopt)

   `lg build` writes <out>.ml and compiles it with `ocamlfind ocamlopt
   -package clj-core,rrbvec -linkpkg`, producing a native binary; it falls
   back to ocamlc for a bytecode binary when ocamlopt is unavailable. *)

let usage = "usage: lg [check|emit|modes|build] <file.lg> [-o out] [-I dir]..."

exception Exit of int

let () =
  let roots = ref [] in
  let out = ref None in
  let cmd = ref None in
  let file = ref None in
  let backend = ref "ocaml" in
  let speclist =
    [ ("-I", Arg.String (fun d -> roots := !roots @ [ d ]), "<dir> add a module search root")
    ; ("-o", Arg.String (fun s -> out := Some s), "<file> output file")
    ; ("--backend", Arg.Symbol ([ "ocaml"; "oxcaml" ], (fun s -> backend := s)),
       "<ocaml|oxcaml> emit mode annotations for the OxCaml backend")
    ; ("--strict", Arg.Set Lgc.Infer.strict,
       " heterogeneous literals require an explicit ^any annotation") ]
  in
  Arg.parse speclist
    (fun a ->
      match !cmd with
      | None when List.mem a [ "check"; "emit"; "modes"; "lgi"; "build" ] -> cmd := Some a
      | None -> cmd := Some "emit"; file := Some a
      | Some _ -> (match !file with None -> file := Some a | Some _ -> raise (Exit 2)))
    usage;
  match !file with
  | None -> Arg.usage speclist usage
  | Some file ->
    (try
       if !backend = "oxcaml" then Lgc.Emit.oxcaml := true;
       let mods = Lgc.Compiler.compile_path ~roots:!roots file in
       (match !cmd with
        | Some "check" ->
          Printf.printf "ok (%d module%s)\n" (List.length mods)
            (if List.length mods = 1 then "" else "s")
        | Some "lgi" ->
          let entry = List.hd (List.rev mods) in
          Lgc.Compiler.write_lgi entry;
          Printf.printf "wrote %s
" (Lgc.Compiler.lgi_path entry.mpath)
        | Some "modes" ->
          let l, o, s = Lgc.Compiler.mode_stats mods in
          let total = l + o + s in
          Printf.printf "mode stats: %d total — local %d (%.0f%%), owned %d (%.0f%%), shared %d (%.0f%%)\n"
            total l (if total = 0 then 0. else 100. *. float l /. float total)
            o (if total = 0 then 0. else 100. *. float o /. float total)
            s (if total = 0 then 0. else 100. *. float s /. float total)
        | _ ->
          let ml = Lgc.Emit.emit_program mods in
          let out_ml =
            match !cmd, !out with
            | Some "emit", Some o -> o
            | Some "emit", None -> Filename.remove_extension file ^ ".ml"
            | _, Some o -> o ^ ".ml"
            | _, None -> Filename.remove_extension file ^ ".ml"
          in
          let oc = open_out out_ml in
          output_string oc ml;
          close_out oc;
          (match !cmd with
           | Some "build" ->
             let exe = match !out with Some o -> o | None -> Filename.remove_extension file in
             if !backend = "oxcaml" then
               Printf.eprintf "lg: oxcaml backend — building %s requires an OxCaml-capable ocamlfind (flambda2 toolchain); emitting annotated source anyway
%!" out_ml;
             let cmdline =
               Printf.sprintf "ocamlfind ocamlopt -package clj-core,rrbvec -linkpkg %s -o %s 2>/dev/null || ocamlfind ocamlc -package clj-core,rrbvec -linkpkg %s -o %s"
                 (Filename.quote out_ml) (Filename.quote exe)
                 (Filename.quote out_ml) (Filename.quote exe)
             in
             let code = Sys.command cmdline in
             if code <> 0 then (Printf.eprintf "lg: ocaml build failed (need clj_core + rrbvec installed)\n%!"; raise (Exit code))
           | _ -> Printf.printf "wrote %s\n" out_ml))
     with
     | Failure msg -> Printf.eprintf "lg: %s
%!" msg; exit 1
     | Lgc.Compiler.Compile_error (l, msg) ->
       Printf.eprintf "%s:%d:%d: %s\n" l.Lgc.Syntax.file l.Lgc.Syntax.line l.Lgc.Syntax.col msg;
       exit 1
     | Exit c -> exit c)
