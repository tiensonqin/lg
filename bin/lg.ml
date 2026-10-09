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
    ; ("--backend", Arg.Symbol ([ "ocaml"; "oxcaml"; "melange" ], (fun s -> backend := s)),
       "<ocaml|oxcaml|melange> emit mode annotations for OxCaml, or JS via melange")
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
       if !backend = "melange" then Lgc.Emit.melange := true;
       let target = if !backend = "melange" then Lgc.Reader.TJs else Lgc.Reader.TNative in
       let mods = Lgc.Compiler.compile_path ~roots:!roots ~target file in
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
           | Some "build" when !backend = "melange" ->
             let exe = match !out with Some o -> o | None -> Filename.remove_extension file in
             (* scratch melange.emit workspace next to <exe>: copy the
                emitted .ml, declare the stanza, dune build, copy the js out *)
             let ws =
               Filename.concat (Filename.get_temp_dir_name ())
                 ("lgmel-" ^ (Digest.to_hex (Digest.string (Filename.concat (Sys.getcwd ()) exe)))) in
             (try Unix.mkdir ws 0o755 with Unix.Unix_error (Unix.EEXIST, _, _) -> ());
             let oc = open_out (Filename.concat ws "dune-project") in
             output_string oc "(lang dune 3.23)
(using melange 1.0)
"; close_out oc;
             let modname = Filename.remove_extension (Filename.basename out_ml) in
             let oc = open_out (Filename.concat ws "dune") in
             output_string oc
               (Printf.sprintf "(melange.emit
 (target js)
 (alias mel)
 (modules %s)
 (libraries clj-core rrbvec)
 (preprocess (pps melange.ppx))
 (module_systems commonjs))
" modname);
             close_out oc;
             let rc = Sys.command (Printf.sprintf "cp %s %s && cd %s && dune build @mel"
                 (Filename.quote out_ml) (Filename.quote (Filename.concat ws (Filename.basename out_ml)))
                 (Filename.quote ws)) in
             if rc <> 0 then (Printf.eprintf "lg: melange build failed
%!"; raise (Exit rc));
             let js = Filename.concat ws (Filename.concat "_build/default/js" (modname ^ ".js")) in
             let dst = exe ^ ".js" in
             let rc = Sys.command (Printf.sprintf "rm -f %s && cp %s %s" (Filename.quote dst) (Filename.quote js) (Filename.quote dst)) in
             if rc <> 0 then (Printf.eprintf "lg: no js output at %s
%!" js; raise (Exit rc));
             (* CommonJS output requires the melange.js/clj-core runtime trees —
                link the emitted node_modules next to the output *)
             let nm = Filename.concat (Filename.dirname dst) "node_modules" in
             let nmsrc = Filename.concat ws "_build/default/js/node_modules" in
             if Sys.file_exists nmsrc && not (Sys.file_exists nm) then
               Unix.symlink ~to_dir:true nmsrc nm;
             Printf.printf "wrote %s (node %s to run)
" dst dst
           | Some "build" ->
             let exe = match !out with Some o -> o | None -> Filename.remove_extension file in
             if !backend = "oxcaml" then
               Printf.eprintf "lg: oxcaml backend — building %s requires an OxCaml-capable ocamlfind (flambda2 toolchain); emitting annotated source anyway
%!" out_ml;
             let pkgs =
               if List.exists (fun (m : Lgc.Ast.modl) -> m.uses_ctypes) mods then
                 "clj-core,rrbvec,unix,str,ctypes.foreign"
               else "clj-core,rrbvec,unix,str"
             in
             let extra = try Sys.getenv "LG_EXTRA_LINK" with Not_found -> "" in
             let cmdline =
               Printf.sprintf "ocamlfind ocamlopt -package %s -linkpkg %s %s -o %s 2>/dev/null || ocamlfind ocamlc -package %s -linkpkg %s %s -o %s"
                 pkgs (Filename.quote out_ml) extra (Filename.quote exe)
                 pkgs (Filename.quote out_ml) extra (Filename.quote exe)
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
