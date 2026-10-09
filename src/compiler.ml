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

(* ---------- .lgi interface files ----------

   Format: one form per exported def —

     (def name TYPE :escapes [bool ...])

   TYPE is the same shape as `^` annotations ((fn [t t] -> r), (vec t),
   (map k v), 'a type vars, named types). Hand-written entries win over
   generated output. A module that has an .lgi only exports the defs
   listed in it. *)

let lgi_of_module (m : Ast.modl) : string =
  let b = Buffer.create 256 in
  Buffer.add_string b
    (Printf.sprintf ";; %s.lgi — interface; defs not listed are private\n" m.mname);
  List.iter
    (fun (d : Ast.topdef) ->
      let esc =
        match Hashtbl.find_opt Modes.global_escapes (m.ocaml_name ^ "." ^ d.tname) with
        | Some l -> " :escapes [" ^ String.concat " " (List.map string_of_bool l) ^ "]"
        | None -> ""
      in
      Buffer.add_string b
        (Printf.sprintf "(def %s %s%s)\n" d.tname (Typ.string_of_lg_ty d.tsch.sty) esc))
    m.defs;
  Buffer.contents b

let lgi_path file = Filename.remove_extension file ^ ".lgi"

let write_lgi (m : Ast.modl) : unit =
  let p = lgi_path m.mpath in
  let oc = open_out p in
  output_string oc (lgi_of_module m);
  close_out oc

let parse_lgi path : (string * Typ.scheme * bool list) list =
  let forms =
    try Reader.read_file ~file:path (read_file_text path)
    with Read_error (l, msg) -> raise (Compile_error (l, msg))
  in
  List.filter_map
    (fun f ->
      match f with
      | Syntax.List (_, Syntax.Atom (_, Syntax.Symbol "def") :: Syntax.Atom (_, Syntax.Symbol n) :: tyf :: rest) ->
        let t =
          try Infer.ty_of_form tyf
          with Typ.Type_error (l, msg) -> raise (Compile_error (l, "lgi: " ^ msg))
        in
        let esc =
          let rec go = function
            | Syntax.Atom (_, Syntax.Keyword "escapes") :: Syntax.Vector (_, bs) :: _ ->
              List.map
                (function Syntax.Atom (_, Syntax.Bool x) -> x | _ -> false)
                (Array.to_list bs)
            | _ :: _ :: tl -> go tl
            | _ -> []
          in
          go rest
        in
        Some (n, Typ.generalize [] t, esc)
      | _ -> None)
    forms

let apply_lgi ~(globals : Infer.globals) ~(m : Ast.modl)
    (entries : (string * Typ.scheme * bool list) list) : unit =
  match Hashtbl.find_opt globals m.mname with
  | None -> ()
  | Some tbl ->
    let listed = List.map (fun (n, _, _) -> n) entries in
    Hashtbl.iter
      (fun n (g : Infer.gbind) -> if not (List.mem n listed) then g.gexp <- false)
      tbl;
    List.iter
      (fun (n, sch, esc) ->
        match Hashtbl.find_opt tbl n with
        | Some (g : Infer.gbind) ->
          g.gsch <- sch;
          g.gexp <- true;
          Hashtbl.replace Modes.global_escapes (m.ocaml_name ^ "." ^ n) esc
        | None ->
          Hashtbl.replace tbl n { Infer.gsch = sch; gvar = false; gexp = true })
      entries

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
      List.iter (fun d -> Modes.record_escapes m.ocaml_name d) m.defs;
      (* an .lgi next to the .lg overrides the module's interface:
         narrows schemes, supplies mode signatures, and gates exports *)
      let lf = lgi_path file in
      (if Sys.file_exists lf then apply_lgi ~globals ~m (parse_lgi lf));
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
