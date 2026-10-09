(* lg — the lg compiler driver.

   usage: lg check  <file.lg> [-I dir]...
          lg emit   <file.lg> [-o out.ml] [-I dir]...
          lg modes  <file.lg> [-I dir]...        (locality/ownership report)
          lg build  <file.lg> [-o out] [-I dir]... (emit + ocamlfind/ocamlopt)

   `lg build` writes <out>.ml and compiles it with `ocamlfind ocamlopt
   -package clj-core,rrbvec -linkpkg`, producing a native binary; it falls
   back to ocamlc for a bytecode binary when ocamlopt is unavailable. *)

let usage = "usage: lg [check|emit|modes|lgi|build|fmt|repl|lsp|deps|doc|init|version] <file.lg> [-o out] [-I dir]..."

exception Exit of int

let () =
  let roots = ref [] in
  let out = ref None in
  let cmd = ref None in
  let file = ref None in
  let backend = ref "ocaml" in
  let all_mods = ref false in
  let speclist =
    [ ("-I", Arg.String (fun d -> roots := !roots @ [ d ]), "<dir> add a module search root")
    ; ("-o", Arg.String (fun s -> out := Some s), "<file> output file")
    ; ("--backend", Arg.Symbol ([ "ocaml"; "oxcaml"; "melange"; "wasm" ], (fun s -> backend := s)),
       "<ocaml|oxcaml|melange> emit mode annotations for OxCaml, or JS via melange")
    ; ("--all", Arg.Set all_mods,
       " lg lgi: generate .lgi for every module in the require closure")
    ; ("--strict", Arg.Set Lgc.Infer.strict,
       " heterogeneous literals require an explicit ^any annotation") ]
  in
  Arg.parse speclist
    (fun a ->
      match !cmd with
      | None when List.mem a [ "check"; "emit"; "modes"; "lgi"; "build"; "fmt"; "repl"; "lsp"; "deps"; "doc"; "init"; "version"; "--version"; "-version" ] -> cmd := Some a
      | None -> cmd := Some "emit"; file := Some a
      | Some _ -> (match !file with None -> file := Some a | Some _ -> raise (Exit 2)))
    usage;
  (match !cmd with
   | Some "version" | Some "--version" | Some "-version" -> print_endline "lg 0.1.0"; exit 0
   | Some "deps" ->
     (match Lgc.Pkg.find_manifest (Sys.getcwd ()) with
      | None -> prerr_endline "no lg.edn found"; exit 1
      | Some (dir, mf) ->
        let _, deps = Lgc.Pkg.load_manifest mf in
        let roots = Lgc.Pkg.dep_roots dir deps in
        Lgc.Pkg.write_lock dir deps;
        List.iter (Printf.printf "resolved %s
") roots;
        Printf.printf "lg.lock written
"; exit 0)
   | Some "init" ->
     (match !file with
      | None -> prerr_endline "usage: lg init <name>"; exit 1
      | Some name ->
        let mkdir p = ignore (Sys.command (Printf.sprintf "mkdir -p %s" (Filename.quote p))) in
        mkdir (Filename.concat name "src");
        let oc = open_out (Filename.concat name "lg.edn") in
        Printf.fprintf oc "{:name \"%s\" :deps {}}\n" name; close_out oc;
        let oc = open_out (Filename.concat name "src/main.lg") in
        output_string oc "(ns main)\n\n(defn -main []\n  (println \"hello from lg\"))\n\n(-main)\n"; close_out oc;
        let oc = open_out (Filename.concat name ".gitignore") in
        output_string oc ".lg/
*.bin
"; close_out oc;
        Printf.printf "created %s (src/main.lg, lg.edn)
" name; exit 0)
   | Some "lsp" -> Lgc.Lsp.run (); exit 0
   | Some "repl" ->
     let session_txt = Buffer.create 512 in
     let compile_run src =
       let f = Filename.temp_file "lg_repl_eval" ".lg" in
       let oc = open_out f in output_string oc src; close_out oc;
       let bin = f ^ ".bin" and errf = f ^ ".err" in
       let rc =
         Sys.command
           (Printf.sprintf "%s build %s -o %s 2>%s" (Filename.quote Sys.argv.(0)) (Filename.quote f)
              (Filename.quote bin) (Filename.quote errf))
       in
       if rc = 0 then ignore (Sys.command (Filename.quote bin))
       else ignore (Sys.command ("cat " ^ Filename.quote errf))
     in
     Printf.printf "lg repl — :quit to exit\n%!";
     (try
        while true do
          Printf.printf "lg=> %!";
          let line = input_line stdin in
          if String.trim line = ":quit" then raise (Exit 0);
          (try
             let fs = Lgc.Reader.read_file ~file:"<repl>" line in
             List.iter
               (fun (f : Lgc.Syntax.form) ->
                 let is_def =
                   match f with
                   | Lgc.Syntax.List (_, Lgc.Syntax.Atom (_, Lgc.Syntax.Symbol hd) :: _) ->
                     List.mem hd [ "def"; "defn"; "defvariant"; "defmacro"; "defrecord"; "declare"; "ffi"; "extern-type"; "ns" ]
                   | _ -> false
                 in
                 if is_def then (
                   Buffer.add_string session_txt (Lgc.Fmt.flat f ^ "\n");
                   compile_run (Buffer.contents session_txt))
                 else compile_run (Buffer.contents session_txt ^ "(println " ^ Lgc.Fmt.flat f ^ ")\n"))
               fs
           with Lgc.Syntax.Read_error (l, m) -> prerr_string (Lgc.Err.render l "E201" m []))
        done
      with End_of_file | Exit _ -> ());
     exit 0
   | _ -> ());
  match !file with
  | None -> Arg.usage speclist usage
  | Some file ->
    (try
       if !backend = "oxcaml" then Lgc.Emit.oxcaml := true;
       if !backend = "melange" then Lgc.Emit.melange := true;
       let target = if !backend = "melange" then Lgc.Reader.TJs else Lgc.Reader.TNative in
       (match !cmd with
        | Some "fmt" ->
          let formatted = Lgc.Fmt.format_file ~target file in
          let ic = open_in file in
          let cur = really_input_string ic (in_channel_length ic) in
          close_in ic;
          if cur = formatted then Printf.printf "%s unchanged
" file
          else (let oc = open_out file in output_string oc formatted; close_out oc;
                Printf.printf "%s formatted
" file);
          exit 0
        | _ -> ());
       let roots = if !backend = "melange" then !roots else Lgc.Pkg.roots_with_manifest !roots file in
       let mods = Lgc.Compiler.compile_path ~roots ~target file in
       (match !cmd with
        | Some "doc" ->
          List.iter
            (fun (m : Lgc.Ast.modl) ->
              Printf.printf "# %s

" m.mname;
              List.iter
                (function
                  | Lgc.Ast.TDef d -> Printf.printf "- `%s` : `%s`
" d.tname (Lgc.Typ.string_of_lg_ty d.tsch.sty)
                  | Lgc.Ast.TExtern (_, n) -> Printf.printf "- `(extern-type %s)`
" n
                  | Lgc.Ast.TVariant (_, n, _, _) -> Printf.printf "- `(defvariant %s)`
" n
                  | _ -> ())
                m.tops)
            mods;
          exit 0
        | Some "check" ->
          Printf.printf "ok (%d module%s)\n" (List.length mods)
            (if List.length mods = 1 then "" else "s")
        | Some "lgi" ->
          let targets =
            if !all_mods then List.filter (fun (m : Lgc.Ast.modl) -> not m.iface_only) mods
            else [ List.hd (List.rev mods) ]
          in
          List.iter
            (fun (m : Lgc.Ast.modl) ->
              if m.iface_only then ()
              else (Lgc.Compiler.write_lgi m;
                    Printf.printf "wrote %s
" (Lgc.Compiler.lgi_path m.mpath)))
            targets
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
 (libraries clj-core rrbvec melange.js)
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
             (try Unix.unlink nm with Unix.Unix_error _ -> ());
             if Sys.file_exists nmsrc && not (Sys.file_exists nm) then
               Unix.symlink ~to_dir:true nmsrc nm;
             Printf.printf "wrote %s (node %s to run)
" dst dst
           | Some "build" when !backend = "wasm" ->
             let exe = match !out with Some o -> o | None -> Filename.remove_extension file in
             (* ocamlc bytecode -> wasm_of_ocaml -> <exe>.js + <exe>.assets/*.wasm *)
             let pkgs =
               if List.exists (fun (m : Lgc.Ast.modl) -> m.uses_ctypes) mods then
                 "clj-core,rrbvec,unix,str,ctypes.foreign"
               else "clj-core,rrbvec,unix,str"
             in
             let rc =
               Sys.command
                 (Printf.sprintf "ocamlfind ocamlc -package %s -linkpkg %s -o %s.byte && wasm_of_ocaml compile %s.byte -o %s.js"
                    pkgs (Filename.quote out_ml) (Filename.quote exe)
                    (Filename.quote exe) (Filename.quote exe))
             in
             if rc <> 0 then (Printf.eprintf "lg: wasm build failed (need wasm_of_ocaml + clj_core + rrbvec installed)\n%!"; raise (Exit rc));
             Printf.printf "wrote %s.js (+ %s.assets) — node %s.js to run\n" exe exe exe
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
             (* incremental compile: one OCaml unit per lg module under
                <exe-dir>/.lg-obj — a unit rebuilds only when its own
                emitted source or a dependency's unit hash changed, so
                untouched modules (and the Lg_rt runtime) link from
                cache *)
             let objdir = Filename.concat (Filename.dirname exe) ".lg-obj" in
             (try Unix.mkdir objdir 0o755 with Unix.Unix_error (Unix.EEXIST, _, _) -> ());
             let units = Lgc.Emit.emit_units mods in
             let opt = Sys.command "ocamlfind ocamlopt -version >/dev/null 2>&1" = 0 in
             let comp = if opt then "ocamlopt" else "ocamlc" in
             let obj_ext = if opt then ".cmx" else ".cmo" in
             let read_file p =
               try
                 let ic = open_in_bin p in
                 let n = in_channel_length ic in
                 let s = really_input_string ic n in
                 close_in ic; s
               with _ -> ""
             in
             let uhashes = Hashtbl.create 16 in
             List.iter
               (fun (fname, src, deps) ->
                 let uh =
                   Digest.to_hex
                     (Digest.string
                        (src ^ String.concat ""
                           (List.filter_map (Hashtbl.find_opt uhashes) deps)))
                 in
                 Hashtbl.replace uhashes fname uh;
                 let stamp = Filename.concat objdir (fname ^ ".stamp") in
                 let obj = Filename.concat objdir (fname ^ obj_ext) in
                 if String.trim (read_file stamp) <> uh || not (Sys.file_exists obj) then begin
                   let mlp = Filename.concat objdir (fname ^ ".ml") in
                   if read_file mlp <> src then begin
                     let oc = open_out mlp in
                     output_string oc src; close_out oc
                   end;
                   let rc =
                     Sys.command
                       (Printf.sprintf "cd %s && ocamlfind %s -package %s -c %s"
                          (Filename.quote objdir) comp pkgs
                          (Filename.quote (fname ^ ".ml")))
                   in
                   if rc <> 0 then (Printf.eprintf "lg: ocaml build failed (need clj_core + rrbvec installed)\n%!"; raise (Exit rc));
                   let oc = open_out stamp in
                   output_string oc (uh ^ "\n"); close_out oc
                 end)
               units;
             let objs =
               String.concat " "
                 (List.map
                    (fun (f, _, _) -> Filename.quote (Filename.concat objdir (f ^ obj_ext)))
                    units)
             in
             let cmdline =
               Printf.sprintf "ocamlfind %s -package %s -linkpkg %s %s -o %s"
                 comp pkgs objs extra (Filename.quote exe)
             in
             let code = Sys.command cmdline in
             if code <> 0 then (Printf.eprintf "lg: ocaml link failed\n%!"; raise (Exit code))
           | _ -> Printf.printf "wrote %s\n" out_ml))
     with
     | Failure msg -> Printf.eprintf "lg: %s
%!" msg; exit 1
     | Lgc.Compiler.Compile_error (l, msg) ->
       prerr_string (Lgc.Err.render l "E100" msg []);
       exit 1
     | Lgc.Err.E _ as e -> Lgc.Err.report e; exit 1
     | Exit c -> exit c)
