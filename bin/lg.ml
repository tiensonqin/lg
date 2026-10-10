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
  let byte = ref false in
  let lgi_check = ref false in
  let jobs = ref 4 in
  let doc_format = ref "html" in
  let doc_title = ref "lg API" in
  let doc_tut_dir = ref None in
  let files = ref [] in
  let speclist =
    [ ("-I", Arg.String (fun d -> roots := !roots @ [ d ]), "<dir> add a module search root")
    ; ("-o", Arg.String (fun s -> out := Some s), "<file> output file")
    ; ("--backend", Arg.Symbol ([ "ocaml"; "oxcaml"; "melange"; "wasm" ], (fun s -> backend := s)),
       "<ocaml|oxcaml|melange> emit mode annotations for OxCaml, or JS via melange")
    ; ("--all", Arg.Set all_mods,
       " lg lgi: generate .lgi for every module in the require closure")
    ; ("--byte", Arg.Set byte,
       " lg build --backend=ocaml: force an ocamlc bytecode build")
    ; ("--strict", Arg.Set Lgc.Infer.strict,
       " heterogeneous literals require an explicit ^any annotation")
    ; ("-j", Arg.Set_int jobs,
       "<n> lg build: parallel unit compiles per dependency level (default 4)")
    ; ("--check", Arg.Set lgi_check,
       " lg lgi --check: fail when a .lgi drifts from its .lg exports")
    ; ("--format", Arg.Symbol ([ "html"; "md" ], (fun s -> doc_format := s)),
       "<html|md> lg doc output format (default html -> <out>/index.html)")
    ; ("--title", Arg.String (fun s -> doc_title := s),
       "<name> lg doc: project title for the generated site")
    ; ("--tutorials", Arg.String (fun d -> doc_tut_dir := Some d),
       "<dir> lg doc: render <dir>/*.md as tutorial pages (sidebar + index)") ]
  in
  Arg.parse speclist
    (fun a ->
      match !cmd with
      | None when List.mem a [ "check"; "emit"; "modes"; "lgi"; "build"; "fmt"; "repl"; "lsp"; "deps"; "doc"; "init"; "version"; "--version"; "-version" ] -> cmd := Some a
      | None -> cmd := Some "emit"; file := Some a
      | Some "doc" -> files := !files @ [ a ]   (* lg doc takes many entry files *)
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
     (* one stable session file per repl: a fresh temp name per line would
        defeat .lg-obj (the unit name derives from the file name) — stable
        name + --byte keeps per-line latency to one unit compile + link *)
     let f = Filename.temp_file "lg_repl_eval" ".lg" in
     let compile_run src =
       let oc = open_out f in output_string oc src; close_out oc;
       let bin = f ^ ".bin" and errf = f ^ ".err" in
       let rc =
         Sys.command
           (Printf.sprintf "%s build --byte %s -o %s 2>%s" (Filename.quote Sys.argv.(0)) (Filename.quote f)
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
  match !files, !file with
  | _ :: _, _ when !cmd = Some "doc" ->
    (* lg doc: compile each entry file's require closure, dedup by mname *)
    let roots = Lgc.Pkg.roots_with_manifest !roots (List.hd !files) in
    let seen = Hashtbl.create 17 in
    let mods =
      List.concat_map
        (fun f -> Lgc.Compiler.compile_path ~roots ~target:Lgc.Reader.TNative f)
        (List.rev !files)
      |> List.filter
           (fun (m : Lgc.Ast.modl) ->
             if Hashtbl.mem seen m.mname then false
             else begin Hashtbl.add seen m.mname (); true end)
    in
    (match !doc_format with
     | "md" ->
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
               | Lgc.Ast.TVariant (_, n, _, _, _) -> Printf.printf "- `(defvariant %s)`
" n
               | _ -> ())
             m.tops)
         mods
     | _ ->
       let outdir = match !out with Some o -> o | None -> "docs/api" in
       let tutorials =
         match !doc_tut_dir with
         | None -> []
         | Some dir ->
           (if not (Sys.file_exists dir && Sys.is_directory dir) then
             (Printf.eprintf "doc: --tutorials: %s is not a directory\n" dir; exit 2));
           Sys.readdir dir |> Array.to_list
           |> List.filter (fun f -> Filename.check_suffix f ".md")
           |> List.sort compare
           |> List.map
             (fun f ->
               let slug = Filename.remove_extension f in
               let src = Lgc.Compiler.read_file_text (Filename.concat dir f) in
               let ttitle, body = Lgc.Doc.md_render ~slug src in
               (slug, ttitle, body))
       in
       Lgc.Doc.generate ~title:!doc_title ~out:outdir ~tutorials mods;
       Printf.printf "doc: %d module%s -> %s/index.html
" (List.length mods)
         (if List.length mods = 1 then "" else "s") outdir);
    exit 0
  | _, None -> Arg.usage speclist usage
  | _, Some file ->
    (try
       if !backend = "oxcaml" then Lgc.Emit.oxcaml := true;
       if !backend = "melange" then Lgc.Emit.melange := true;
       Lgc.Ocaml_sig.backend := !backend;
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
        | Some "check" ->
          Printf.printf "ok (%d module%s)\n" (List.length mods)
            (if List.length mods = 1 then "" else "s")
        | Some "lgi" ->
          let targets =
            if !all_mods then List.filter (fun (m : Lgc.Ast.modl) -> not m.iface_only) mods
            else [ List.hd (List.rev mods) ]
          in
          if !lgi_check then begin
            (* drift gate: an existing .lgi must agree with the module's
               exports — a listed def whose signature changed, or an entry
               naming a def that no longer exists, is drift (exit 1).
               Unlisted defs are private-by-omission, not drift. *)
            let bad = ref 0 in
            List.iter
              (fun (m : Lgc.Ast.modl) ->
                if m.iface_only then ()
                else begin
                  let p = Lgc.Compiler.lgi_path m.mpath in
                  if Sys.file_exists p then begin
                    let hand = Lgc.Compiler.parse_lgi p in
                    let hand = List.filter (function Lgc.Compiler.LMacro _ -> false | _ -> true) hand in
                    let gen = Lgc.Compiler.lgi_entries_of_module m in
                    let same_name e = Lgc.Compiler.lgi_entry_name e in
                    List.iter
                      (fun h ->
                        let hn = same_name h in
                        match List.find_opt (fun g -> same_name g = hn) gen with
                        | None ->
                          incr bad;
                          Printf.printf "%s: stale entry — %s is no longer defined\n  - %s\n" p hn
                            (Lgc.Compiler.lgi_entry_form h)
                        | Some g ->
                          let hf = Lgc.Compiler.lgi_form_canon (Lgc.Compiler.lgi_entry_form ~doc:false h)
                          and gf = Lgc.Compiler.lgi_form_canon (Lgc.Compiler.lgi_entry_form ~doc:false g) in
                          if hf <> gf then begin
                            incr bad;
                            Printf.printf "%s: signature drift — %s\n  - %s\n  + %s\n" p hn hf gf
                          end)
                      hand
                  end else Printf.printf "%s: no .lgi (all defs exported)\n" p
                end)
              targets;
            if !bad > 0 then (Printf.eprintf "lgi --check: %d drifted entr%s\n" !bad (if !bad = 1 then "y" else "ies"); exit 1)
            else Printf.printf "ok lgi --check\n"
          end
          else
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
             if !backend = "oxcaml" then begin
               (* the build must run inside an OxCaml opam switch: probe
                  ocamlopt's flambda2 flag rather than guessing *)
               let ox =
                 Sys.command "ocamlfind ocamlopt -config 2>/dev/null | grep -q 'flambda2: true'" = 0
               in
               if not ox then
                 Printf.eprintf "lg: warning: ocamlfind is not an OxCaml toolchain — `local_`/`stack_` annotations will not compile (run inside `eval $(opam env --switch=oxcaml)`)\n%!"
             end;
             let pkgs =
               let base =
                 if List.exists (fun (m : Lgc.Ast.modl) -> m.uses_ctypes) mods then
                   "clj-core,rrbvec,unix,str,ctypes.foreign"
                 else "clj-core,rrbvec,unix,str"
               in
               (* [ocaml.pkg/name] requires append their ocamlfind
                  packages to the per-unit compile (-I dirs) and the link *)
               match !(Lgc.Ocaml_sig.packages) with
               | [] -> base
               | ps -> base ^ "," ^ String.concat "," (List.sort_uniq String.compare ps)
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
             let comp = if !byte || not opt then "ocamlc" else "ocamlopt" in
             let obj_ext = if !byte || not opt then ".cmo" else ".cmx" in
             (* toolchain version participates in staleness: a .cmi/.cmx
                built by OCaml X.Y is unreadable by OCaml X.Z, so the stamp
                binds both source+dep content and the active compiler *)
             let ocaml_ver =
               (* direct `ocamlc/ocamlopt -version` — ocamlfind adds ~8ms
                  on the warm path for no benefit *)
               let ic = Unix.open_process_in (comp ^ " -version 2>/dev/null") in
               let v = try input_line ic with End_of_file -> "unknown" in
               close_in ic; String.trim v
             in
             let read_file p =
               try
                 let ic = open_in_bin p in
                 let n = in_channel_length ic in
                 let s = really_input_string ic n in
                 close_in ic; s
               with _ -> ""
             in
             let uhashes = Hashtbl.create 16 in
             (* global content-addressed object cache under ~/.lg/cache:
                key = hash(emitted src + dep unit hashes) + toolchain +
                compiler mode. A hit copies .cmi/.cmo|.cmx/.o/.ml into
                .lg-obj and the unit counts as fresh — lg_rt and
                untouched units never recompile, so a cold build is
                emit + link only. *)
             let cache_root =
               match Sys.getenv_opt "HOME" with
               | Some h -> Filename.concat h ".lg/cache"
               | None -> Filename.concat (Filename.get_temp_dir_name ()) "lg-cache"
             in
             ignore (Sys.command ("mkdir -p " ^ Filename.quote cache_root));
             let cp_file a b =
               let ic = open_in_bin a and oc = open_out_bin b in
               (try
                  while true do output_char oc (input_char ic) done
                with End_of_file -> ());
               close_in ic; close_out oc
             in
             let artifact_exts =
               (* .o only exists under ocamlopt; ocamlc emits no .o *)
               [ ".cmi"; obj_ext; ".ml" ]
               @ (if obj_ext = ".cmx" then [ ".o" ] else [])
             in
             let cache_restore fname key =
               let d = Filename.concat cache_root key in
               if Sys.file_exists d
                  && List.for_all
                       (fun e -> Sys.file_exists (Filename.concat d (fname ^ e)))
                       artifact_exts
               then begin
                 List.iter
                   (fun e ->
                     let p = Filename.concat d (fname ^ e) in
                     if Sys.file_exists p then
                       cp_file p (Filename.concat objdir (fname ^ e)))
                   artifact_exts;
                 true
               end else false
             in
             let cache_store fname key =
               let d = Filename.concat cache_root key in
               let tmp = d ^ ".tmp." ^ string_of_int (Unix.getpid ()) in
               if not (Sys.file_exists d) then begin
                 (try Unix.mkdir tmp 0o755 with Unix.Unix_error _ -> ());
                 List.iter
                   (fun e ->
                     let p = Filename.concat objdir (fname ^ e) in
                     if Sys.file_exists p then
                       cp_file p (Filename.concat tmp (fname ^ e)))
                   artifact_exts;
                 (try Unix.rename tmp d
                  with Unix.Unix_error _ ->
                    ignore (Sys.command ("rm -rf " ^ Filename.quote tmp)))
               end
             in
             (* the stamp is per (unit, toolchain): ocamlc and ocamlopt
                produce different artifacts from the same source, so a
                shared stamp would let a stale .cmo/.cmx pass as fresh
                after the other mode rebuilt the unit *)
             let write_stamp fname uh =
               let stamp = Filename.concat objdir (fname ^ "." ^ comp ^ ".stamp") in
               let oc = open_out stamp in
               output_string oc (uh ^ " " ^ ocaml_ver ^ "\n"); close_out oc
             in
             let stale = ref [] in
             List.iter
               (fun (fname, src, deps) ->
                 let uh =
                   Digest.to_hex
                     (Digest.string
                        (src ^ String.concat ""
                           (List.filter_map (Hashtbl.find_opt uhashes) deps)))
                 in
                 Hashtbl.replace uhashes fname uh;
                 let stamp = Filename.concat objdir (fname ^ "." ^ comp ^ ".stamp") in
                 let obj = Filename.concat objdir (fname ^ obj_ext) in
                 if String.trim (read_file stamp) <> (uh ^ " " ^ ocaml_ver) || not (Sys.file_exists obj) then begin
                   let key = uh ^ "-" ^ ocaml_ver ^ "-" ^ comp in
                   if cache_restore fname key then write_stamp fname uh
                   else begin
                     let mlp = Filename.concat objdir (fname ^ ".ml") in
                     if read_file mlp <> src then begin
                       let oc = open_out mlp in
                       output_string oc src; close_out oc
                     end;
                     stale := (fname, uh, key) :: !stale
                   end
                 end)
               units;
             (* parallel unit compilation in dependency levels: a unit needs
                its lg deps' .cmi, so level(u) = 1 + max level of its stale
                deps; fresh units count as done. Children fork per level in
                batches of -j. *)
             let stale_set =
               List.fold_left (fun s (f, _, _) -> f :: s) [] !stale
             in
             let dep_of =
               let t = Hashtbl.create 16 in
               List.iter (fun (f, _, ds) -> Hashtbl.replace t f ds) units;
               fun f -> try Hashtbl.find t f with Not_found -> []
             in
             let levels = Hashtbl.create 16 in
             let rec level f =
               match Hashtbl.find_opt levels f with
               | Some l -> l
               | None ->
                 let l =
                   1 + List.fold_left
                         (fun m d -> if List.mem d stale_set then max m (level d) else m)
                         (-1) (dep_of f)
                 in
                 Hashtbl.replace levels f l; l
             in
             let max_lvl =
               List.fold_left (fun m (f, _, _) -> max m (level f)) (-1) !stale
             in
             let compile fname key =
               let rc =
                 Sys.command
                   (Printf.sprintf "cd %s && ocamlfind %s -package %s -c %s"
                      (Filename.quote objdir) comp pkgs
                      (Filename.quote (fname ^ ".ml")))
               in
               if rc = 0 then cache_store fname key;
               rc
             in
             for lvl = 0 to max_lvl do
               let fns =
                 List.filter_map
                   (fun (f, _, k) -> if level f = lvl then Some (f, k) else None)
                   !stale
               in
               let rec chunks n l =
                 match l with
                 | [] -> []
                 | _ ->
                   let rec take k acc = function
                     | [] -> (List.rev acc, [])
                     | x :: xs -> if k = 0 then (List.rev acc, x :: xs) else take (k - 1) (x :: acc) xs
                   in
                   let g, rest = take (max 1 !jobs) [] l in
                   g :: chunks n rest
               in
               List.iter
                 (fun grp ->
                   let pids =
                     List.map
                       (fun (f, k) ->
                         match Unix.fork () with
                         | 0 -> exit (compile f k)
                         | pid -> pid)
                       grp
                   in
                   List.iter
                     (fun pid ->
                       match Unix.waitpid [] pid with
                       | _, Unix.WEXITED 0 -> ()
                       | _, Unix.WEXITED rc ->
                         Printf.eprintf "lg: ocaml build failed (need clj_core + rrbvec installed)\n%!";
                         raise (Exit rc)
                       | _ ->
                         Printf.eprintf "lg: ocaml build failed (compiler killed)\n%!";
                         raise (Exit 2))
                     pids)
                 (chunks (max 1 !jobs) fns)
             done;
             List.iter
               (fun (fname, uh, _) -> write_stamp fname uh)
               !stale;
             let objs =
               String.concat " "
                 (List.map
                    (fun (f, _, _) -> Filename.quote (Filename.concat objdir (f ^ obj_ext)))
                    units)
             in
             (* the link itself is content-addressed too: skip it when the
                exe is fresh (warm path ~25ms total), and cache the linked
                binary globally so a cold build with all units restored is
                just a file copy *)
             let link_key =
               Digest.to_hex
                 (Digest.string
                    (String.concat ""
                       (List.map (fun (f, _, _) -> Hashtbl.find uhashes f) units)
                     ^ comp ^ pkgs ^ extra ^ ocaml_ver))
             in
             let link_stamp = Filename.concat objdir (".link." ^ comp ^ ".stamp") in
             let linked =
               String.trim (read_file link_stamp) = link_key && Sys.file_exists exe
             in
             let code =
               if linked then 0
               else
                 let d = Filename.concat cache_root ("link-" ^ link_key) in
                 let cached_exe = Filename.concat d "exe" in
                 if Sys.file_exists cached_exe then begin
                   cp_file cached_exe exe;
                   (try Unix.chmod exe 0o755 with Unix.Unix_error _ -> ());
                   0
                 end else begin
                   let cmdline =
                     Printf.sprintf "ocamlfind %s -package %s -linkpkg %s %s -o %s"
                       comp pkgs objs extra (Filename.quote exe)
                   in
                   let rc = Sys.command cmdline in
                   if rc = 0 && not (Sys.file_exists d) then begin
                     let tmp = d ^ ".tmp." ^ string_of_int (Unix.getpid ()) in
                     (try Unix.mkdir tmp 0o755 with Unix.Unix_error _ -> ());
                     cp_file exe (Filename.concat tmp "exe");
                     (try Unix.rename tmp d
                      with Unix.Unix_error _ ->
                        ignore (Sys.command ("rm -rf " ^ Filename.quote tmp)))
                   end;
                   rc
                 end
             in
             (if code = 0 then begin
                let oc = open_out link_stamp in
                output_string oc (link_key ^ "\n"); close_out oc
              end);
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
