(* Module loading + compilation driver.

   Module resolution: `foo.bar` -> <root>/foo/bar.lg, then <root>/foo_bar.lg,
   then <root>/foo.bar.lg. The entry file's basename is its namespace unless
   it declares `(ns ...)`. Requires are scanned from the ns form before the
   module is inferred so dependencies typecheck first. *)

open Syntax

exception Compile_error of loc * string

let read_file_text path =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  s

let scan_ns (forms : form list) : string option * string list =
  let reqs = ref [] in
  let ns = ref None in
  List.iter
    (fun f ->
      match f with
      | List (l, Atom (_, Symbol "ns") :: Atom (_, Symbol n) :: clauses) ->
        ns := Some n;
        List.iter
          (fun c ->
            match c with
            | List (_, Atom (_, Keyword "require") :: specs) ->
              List.iter
                (fun spec ->
                  match spec with
                  | Vector (_, [| Atom (_, Symbol rn) |]) -> reqs := rn :: !reqs
                  | Vector (_, [| Atom (_, Symbol rn); Atom (_, Keyword "as"); Atom (_, Symbol _) |]) -> reqs := rn :: !reqs
                  | _ -> raise (Compile_error (l, "unsupported :require spec")))
                specs
            | _ -> ())
          clauses
      | _ -> ())
    forms;
  (!ns, List.rev !reqs)

let ns_to_paths ns =
  let a = String.map (fun c -> if c = '.' then '/' else c) ns in
  let b = String.map (fun c -> if c = '.' then '_' else c) ns in
  [ a; b; ns ]

let find_module_file ~roots ns =
  let cands =
    List.concat_map
      (fun r -> List.map (fun base -> Filename.concat r (base ^ ".lg")) (ns_to_paths ns))
      roots
  in
  List.find_opt Sys.file_exists cands

let compile_path ~(roots : string list) (path : string) : Ast.modl list =
  let globals : Infer.globals = Hashtbl.create 16 in
  let visited : (string, unit) Hashtbl.t = Hashtbl.create 16 in
  let order : Ast.modl list ref = ref [] in
  let rec load file =
    let file = if Filename.is_relative file then Filename.concat (Sys.getcwd ()) file else file in
    if not (Hashtbl.mem visited file) then begin
      Hashtbl.add visited file ();
      let src =
        try read_file_text file
        with Sys_error m -> raise (Compile_error (no_loc, m))
      in
      let forms =
        try Reader.read_file ~file src
        with Read_error (l, msg) -> raise (Compile_error (l, msg))
      in
      let ns0, reqs = scan_ns forms in
      let dir = Filename.dirname file in
      let roots' = dir :: roots in
      List.iter
        (fun rn ->
          match find_module_file ~roots:roots' rn with
          | Some f -> load f
          | None -> raise (Compile_error (no_loc, "cannot find module " ^ rn)))
        reqs;
      let mname =
        match ns0 with
        | Some n -> n
        | None -> Filename.remove_extension (Filename.basename file)
      in
      let m =
        try Infer.infer_program forms mname file globals
        with Typ.Type_error (l, msg) -> raise (Compile_error (l, msg))
      in
      Modes.analyze_module m;
      order := m :: !order
    end
  in
  load path;
  List.rev !order

let mode_stats mods =
  let l = ref 0 and o = ref 0 and s = ref 0 in
  List.iter
    (fun m ->
      let l', o', s' = Modes.count_modes m in
      l := !l + l'; o := !o + o'; s := !s + s')
    mods;
  (!l, !o, !s)
