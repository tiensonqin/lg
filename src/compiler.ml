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
      | List (l, Atom (_, Keyword "require") :: specs) ->
        (* bare top-level (:require [ns :as a]) — same spec surface as the
           ns clause; only [ns ...] vector specs contribute dependencies *)
        List.iter
          (fun spec ->
            match spec with
            | Vector (_, els) when Array.length els >= 1 ->
              (match els.(0) with
               | Atom (_, Symbol rn) ->
                 (* ocaml.* specs name OCaml libraries, not lg modules —
                    no dependency edge *)
                 if String.length rn < 6 || String.sub rn 0 6 <> "ocaml." then
                   reqs := rn :: !reqs
               | _ -> raise (Compile_error (l, "unsupported :require spec")))
            | _ -> raise (Compile_error (l, "unsupported :require spec")))
          specs
      | List (l, Atom (_, Symbol "ns") :: Atom (_, Symbol n) :: clauses) ->
        ns := Some n;
        List.iter
          (fun c ->
            match c with
            | List (_, Atom (_, Keyword "require") :: specs) ->
              List.iter
                (fun spec ->
                  match spec with
                  | Vector (_, els) when Array.length els >= 1 ->
                    (match els.(0) with
                     | Atom (_, Symbol rn) ->
                       (* ocaml.* specs name OCaml libraries, not lg
                          modules — no dependency edge *)
                       if String.length rn < 6 || String.sub rn 0 6 <> "ocaml." then
                         reqs := rn :: !reqs
                     | _ -> raise (Compile_error (l, "unsupported :require spec")))
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
      (fun r -> List.concat_map (fun base -> [ Filename.concat r (base ^ ".lg"); Filename.concat r (base ^ ".cljc") ]) (ns_to_paths ns))
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

(* a parsed .lgi entry — one per form *)
type lgi_entry =
  | LDef of string * Typ.scheme * bool list * bool * string option (* name, sch, escapes, implicit, docstring *)
  | LMacro of string * Typ.scheme * string option    (* doc-only macro entry — never a value export *)
  | LExtern of string
  | LVariant of string * Typ.ty list * (string * (string * Typ.ty) list) list
  | LPrivate of string

(* 'aNN tyvars carry internal ids; drift checks compare alpha-normalized forms *)
let lgi_form_canon s =
  let tbl = Hashtbl.create 8 in
  let next = ref 0 in
  let n = String.length s in
  let is_id c = (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9') || c = '_' || c = '?' || c = '-' in
  let b = Buffer.create n in
  let rec scan i =
    if i < n then begin
      if s.[i] = '\'' && i + 1 < n && is_id s.[i + 1] then begin
        let j = ref (i + 1) in
        while !j < n && is_id s.[!j] do incr j done;
        let tok = String.sub s i (!j - i) in
        let k = String.length tok in
        if k > 2 && tok.[k - 1] >= '0' && tok.[k - 1] <= '9' then begin
          let nm =
            match Hashtbl.find_opt tbl tok with
            | Some v -> v
            | None ->
              let v = "'" ^ String.make 1 (Char.chr (Char.code 'a' + !next)) in
              incr next; Hashtbl.replace tbl tok v; v
          in
          Buffer.add_string b nm
        end else Buffer.add_string b tok;
        scan !j
      end else begin
        Buffer.add_char b s.[i];
        scan (i + 1)
      end
    end
  in
  scan 0;
  Buffer.contents b

let lgi_entry_name = function
  | LDef (n, _, _, _, _) | LMacro (n, _, _) | LExtern n | LPrivate n -> n
  | LVariant (n, _, _) -> n

(* like string_of_lg_ty, but the variant's parameter vars print as the
   declared parameter names (a, b, ...) so generated defvariant entries
   round-trip through parse_lgi with their fields linked to the head *)
let lgi_ty_str (ptys : Typ.ty list) : Typ.ty -> string =
  let m = Hashtbl.create 7 in
  List.iteri
    (fun i tv ->
      match Typ.repr tv with
      | Typ.TVar v -> Hashtbl.replace m v.id (String.make 1 (Char.chr (Char.code 'a' + i)))
      | _ -> ())
    ptys;
  let rec go t =
    match Typ.repr t with
    | Typ.TVar v ->
      (match Hashtbl.find_opt m v.id with Some n -> n | None -> Typ.string_of_lg_ty t)
    | Typ.TList t -> "(list " ^ go t ^ ")"
    | Typ.TVec t -> "(vec " ^ go t ^ ")"
    | Typ.TSeq t -> "(seq " ^ go t ^ ")"
    | Typ.TMap (k, v) -> "(map " ^ go k ^ " " ^ go v ^ ")"
    | Typ.TSet t -> "(set " ^ go t ^ ")"
    | Typ.TAtom t -> "(atom " ^ go t ^ ")"
    | Typ.TOption t -> "(option " ^ go t ^ ")"
    | Typ.TImplicit t -> "(implicit " ^ go t ^ ")"
    | Typ.TTuple ts -> "(tuple " ^ String.concat " " (List.map go ts) ^ ")"
    | Typ.TFun (ts, r) ->
      "(fn [" ^ String.concat " " (List.map go ts) ^ "] " ^ go r ^ ")"
    | Typ.TCon (n, ts) ->
      if ts = [] then n else "(" ^ n ^ " " ^ String.concat " " (List.map go ts) ^ ")"
    | _ -> Typ.string_of_lg_ty t
  in
  go

let lgi_entry_form ?(doc = true) (e : lgi_entry) : string =
  match e with
  | LDef (n, sch, esc, imp, d) ->
    let kw = if imp then "implicit" else "def" in
    let es = if esc = [] then "" else " :escapes [" ^ String.concat " " (List.map string_of_bool esc) ^ "]" in
    let ds = match doc, d with true, Some d -> " " ^ Printf.sprintf "%S" d | _ -> "" in
    Printf.sprintf "(%s %s %s%s%s)" kw n (Typ.string_of_lg_ty sch.sty) es ds
  | LMacro (n, sch, d) ->
    let ds = match doc, d with true, Some d -> " " ^ Printf.sprintf "%S" d | _ -> "" in
    Printf.sprintf "(macro %s %s%s)" n (Typ.string_of_lg_ty sch.sty) ds
  | LExtern n -> Printf.sprintf "(extern-type %s)" n
  | LVariant (n, ptys, cs) ->
    let tys = lgi_ty_str ptys in
    let pnames = List.map tys ptys in
    let head = if pnames = [] then n else "(" ^ String.concat " " (n :: pnames) ^ ")" in
    Printf.sprintf "(defvariant %s%s)" head
      (String.concat ""
         (List.map
            (fun (c2, flds) ->
              if flds = [] then " " ^ c2
              else " (" ^ c2 ^ String.concat "" (List.map (fun (fnm, t) -> " [" ^ fnm ^ " " ^ tys t ^ "]") flds) ^ ")")
            cs))
  | LPrivate n -> Printf.sprintf "(private %s)" n

let lgi_entries_of_module (m : Ast.modl) : lgi_entry list =
  List.filter_map
    (function
      | Ast.TDef (d : Ast.topdef) ->
        let esc =
          match Hashtbl.find_opt Modes.global_escapes (m.ocaml_name ^ "." ^ d.tname) with
          | Some l -> l
          | None -> []
        in
        Some (LDef (d.tname, d.tsch, esc, d.timplicit <> None, d.tdoc))
      | Ast.TExtern (_, n) -> Some (LExtern n)
      | Ast.TVariant (_, n, ps, cs, _) -> Some (LVariant (n, ps, cs))
      | Ast.TEffect _ -> None
      | Ast.TFfi (_, n, args, ret, _, _) ->
        Some (LDef (n, Typ.generalize [] (Typ.TFun (args, ret)), [], false, None)))
    m.tops

let lgi_of_module (m : Ast.modl) : string =
  let b = Buffer.create 256 in
  Buffer.add_string b
    (Printf.sprintf ";; %s.lgi — interface; defs not listed are private\n" m.mname);
  List.iter (fun e -> Buffer.add_string b (lgi_entry_form e ^ "\n")) (lgi_entries_of_module m);
  Buffer.contents b

let lgi_path file = Filename.remove_extension file ^ ".lgi"

let parse_lgi path : lgi_entry list =
  let forms =
    try Reader.read_file ~file:path (read_file_text path)
    with Read_error (l, msg) -> Err.err l "E201" msg []
  in
  let ty_of tf =
    try Infer.ty_of_form tf
    with Typ.Type_error (l, msg) -> raise (Compile_error (l, "lgi: " ^ msg))
  in
  List.filter_map
    (fun f ->
      match f with
      | Syntax.List (_, Syntax.Atom (_, Syntax.Symbol "macro") :: Syntax.Atom (_, Syntax.Symbol n) :: tyf :: rest) ->
        let doc =
          List.find_map
            (function Syntax.Atom (_, Syntax.Str d) -> Some d | _ -> None)
            rest
        in
        Some (LMacro (n, Typ.generalize [] (ty_of tyf), doc))
      | Syntax.List (_, Syntax.Atom (_, Syntax.Symbol kw) :: Syntax.Atom (_, Syntax.Symbol n) :: tyf :: rest)
        when kw = "def" || kw = "implicit" || kw = "ffi" ->
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
        let doc =
          List.find_map
            (function Syntax.Atom (_, Syntax.Str d) -> Some d | _ -> None)
            rest
        in
        Some (LDef (n, Typ.generalize [] (ty_of tyf), esc, kw = "implicit", doc))
      | Syntax.List (_, Syntax.Atom (_, Syntax.Symbol "extern-type") :: [ Syntax.Atom (_, Syntax.Symbol n) ]) ->
        Some (LExtern n)
      | Syntax.List (_, Syntax.Atom (_, Syntax.Symbol "private") :: [ Syntax.Atom (_, Syntax.Symbol n) ]) ->
        Some (LPrivate n)
      | Syntax.List (l, Syntax.Atom (_, Syntax.Symbol "defvariant") :: namef :: ctors) ->
        let vname, params =
          match namef with
          | Syntax.Atom (_, Syntax.Symbol n) -> (n, [])
          | Syntax.List (_, Syntax.Atom (_, Syntax.Symbol n) :: ps) ->
            (n, List.map (function Syntax.Atom (_, Syntax.Symbol p) -> p | _ -> raise (Compile_error (l, "lgi: variant params must be symbols"))) ps)
          | _ -> raise (Compile_error (l, "lgi: defvariant expects a name or (name params...)"))
        in
        let tbl = Hashtbl.create 7 in
        List.iter (fun p -> Hashtbl.replace tbl p (Typ.fresh_var ())) params;
        let ptys = List.map (Hashtbl.find tbl) params in
        let field_of = function
          | Syntax.Vector (_, [| Syntax.Atom (_, Syntax.Symbol fnm); tf |]) ->
            (fnm, (try Infer.ty_of_form ~tbl tf with Typ.Type_error (l2, msg) -> raise (Compile_error (l2, "lgi: " ^ msg))))
          | _ -> raise (Compile_error (l, "lgi: variant fields must be [name type] vectors"))
        in
        let parsed =
          List.map
            (function
              | Syntax.Atom (_, Syntax.Symbol c) -> (c, [])
              | Syntax.List (_, Syntax.Atom (_, Syntax.Symbol c) :: flds) -> (c, List.map field_of flds)
              | _ -> raise (Compile_error (l, "lgi: malformed variant ctor")))
            ctors
        in
        Some (LVariant (vname, ptys, parsed))
      | _ -> None)
    forms

(* merge with an existing .lgi: entries the user wrote (or edited) win
   over freshly generated ones with the same name, and `(private n)`
   entries survive — regeneration never re-exports what was made private *)
let write_lgi (m : Ast.modl) : unit =
  let p = lgi_path m.mpath in
  let hand : lgi_entry list =
    if Sys.file_exists p then parse_lgi p else []
  in
  let gen = lgi_entries_of_module m in
  let merged =
    List.map
      (fun g ->
        match List.find_opt (fun h -> lgi_entry_name h = lgi_entry_name g) hand with
        | Some h -> h
        | None -> g)
      gen
    @ List.filter (fun h -> not (List.mem (lgi_entry_name h) (List.map lgi_entry_name gen))) hand
  in
  let b = Buffer.create 256 in
  Buffer.add_string b
    (Printf.sprintf ";; %s.lgi — interface; defs not listed are private\n" m.mname);
  Buffer.add_string b ";; hand-written entries win over generated output; (private n) hides a def\n";
  List.iter (fun e -> Buffer.add_string b (lgi_entry_form e ^ "\n")) merged;
  let oc = open_out p in
  output_string oc (Buffer.contents b);
  close_out oc

let find_lgi ~roots ns =
  let cands =
    List.concat_map
      (fun r -> List.map (fun base -> Filename.concat r (base ^ ".lgi")) (ns_to_paths ns))
      roots
  in
  List.find_opt Sys.file_exists cands

let apply_lgi ~(globals : Infer.globals) ~(m : Ast.modl)
    (entries : lgi_entry list) : unit =
  match Hashtbl.find_opt globals m.mname with
  | None -> ()
  | Some tbl ->
    let listed =
      List.concat_map
        (function
          | LDef (n, _, _, _, _) -> [ n ]
          | LVariant (_, _, cs) -> List.map fst cs
          | LExtern _ | LPrivate _ | LMacro _ -> [])
        entries
    in
    Hashtbl.iter
      (fun n (g : Infer.gbind) -> if not (List.mem n listed) then g.gexp <- false)
      tbl;
    List.iter
      (fun e ->
        match e with
        | LDef (n, sch, esc, imp, _) ->
          (match Hashtbl.find_opt tbl n with
           | Some (g : Infer.gbind) ->
             g.gsch <- sch;
             g.gexp <- true;
             Hashtbl.replace Modes.global_escapes (m.ocaml_name ^ "." ^ n) esc
           | None ->
             Hashtbl.replace tbl n { Infer.gsch = sch; gvar = false; gexp = true });
          if imp then
            let cur = match Hashtbl.find_opt Infer.module_implicits m.mname with Some l -> l | None -> [] in
            Hashtbl.replace Infer.module_implicits m.mname (cur @ [ (n, sch.sty) ])
        | LVariant (vname, ptys, cs) ->
          let ret = Typ.TCon (vname, ptys) in
          List.iter
            (fun (c, flds) ->
              let ftys = List.map snd flds in
              let cty = (match ftys with [] -> ret | _ -> Typ.TFun (ftys, ret)) in
              let sch = Typ.generalize [] cty in
              (* the .lgi interface is authoritative: listed ctors become
                 the exported/visible set for this module's variant *)
              Hashtbl.replace tbl c { Infer.gsch = sch; gvar = false; gexp = true };
              Infer.register_variant_mod m.ocaml_name c sch (List.length ftys))
            cs;
          Hashtbl.replace Infer.all_vtypes vname (List.map fst cs)
        | LExtern _ | LPrivate _ | LMacro _ -> ())
      entries

let compile_path ~(roots : string list) ?(target = Reader.TNative) (path : string) : Ast.modl list =
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
        try Reader.read_file ~file ~target src
        with Read_error (l, msg) -> Err.err l "E201" msg []
      in
      let ns0, reqs = scan_ns forms in
      let dir = Filename.dirname file in
      let roots' = dir :: roots in
      List.iter
        (fun rn ->
          if not (List.mem rn Infer.builtin_namespaces) then
          match find_module_file ~roots:roots' rn with
          | Some f -> load f
          | None ->
            (* interface-only dependency: an .lgi satisfies a require for
               check/modes (interface-first workflow); emit still needs
               the .lg *)
            (match find_lgi ~roots:roots' rn with
             | Some lf -> load_lgi rn lf
             | None -> raise (Compile_error (no_loc, "cannot find module " ^ rn))))
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
      List.iter (function Ast.TDef d -> Modes.record_escapes m.ocaml_name d | _ -> ()) m.tops;
      (* an .lgi next to the .lg overrides the module's interface:
         narrows schemes, supplies mode signatures, and gates exports *)
      let lf = lgi_path file in
      (if Sys.file_exists lf then apply_lgi ~globals ~m (parse_lgi lf));
      order := m :: !order
    end
  and load_lgi rn lf =
    (* an .lgi standing in for a module: register its entries as the
       module's globals and mark it interface-only *)
    if not (Hashtbl.mem visited lf) then begin
      Hashtbl.add visited lf ();
      let entries = parse_lgi lf in
      let tbl =
        match Hashtbl.find_opt globals rn with
        | Some t -> t
        | None -> let t = Hashtbl.create 16 in Hashtbl.replace globals rn t; t
      in
      let ocaml_m = Infer.ocaml_mod_of_ns rn in
      List.iter
        (fun e ->
          match e with
          | LDef (n, sch, esc, imp, _) ->
            Hashtbl.replace tbl n { Infer.gsch = sch; gvar = false; gexp = true };
            if esc <> [] then
              Hashtbl.replace Modes.global_escapes (ocaml_m ^ "." ^ n) esc;
            if imp then
              Hashtbl.replace Infer.module_implicits rn [ (n, sch.sty) ]
          | LVariant (vname, ptys, cs) ->
            let ret = Typ.TCon (vname, ptys) in
            List.iter
              (fun (c, flds) ->
                let ftys = List.map snd flds in
                let cty = (match ftys with [] -> ret | _ -> Typ.TFun (ftys, ret)) in
                let sch = Typ.generalize [] cty in
                Hashtbl.replace tbl c { Infer.gsch = sch; gvar = false; gexp = true };
                Infer.register_variant_mod ocaml_m c sch (List.length ftys))
              cs;
            Hashtbl.replace Infer.all_vtypes vname (List.map fst cs)
          | LExtern _ | LPrivate _ | LMacro _ -> ())
        entries;
      order :=
        { Ast.mname = rn; ocaml_name = Infer.ocaml_mod_of_ns rn; mpath = lf;
          requires = []; tops = []; effects = []; iface_only = true;
          uses_ctypes = false }
        :: !order
    end
  in
  load path;
  (* two modules must not collapse into one emitted name: a repeated ns
     name (same name from different files) silently merges globals, and
     distinct ns names that munge to the same OCaml module (foo-bar vs
     foo_bar) emit a duplicate `module M = struct` — catch both early *)
  let seen_ns = Hashtbl.create 16 and seen_mod = Hashtbl.create 16 in
  List.iter
    (fun (m : Ast.modl) ->
      (match Hashtbl.find_opt seen_ns m.mname with
       | Some (m2 : Ast.modl) when m2.mpath <> m.mpath ->
         raise (Compile_error (no_loc, "duplicate namespace " ^ m.mname ^ " in " ^ m.mpath ^ " and " ^ m2.mpath))
       | _ -> ());
      (match Hashtbl.find_opt seen_mod m.ocaml_name with
       | Some (m2 : Ast.modl) when m2.mname <> m.mname ->
         raise (Compile_error (no_loc, "namespaces " ^ m2.mname ^ " and " ^ m.mname ^ " both compile to OCaml module " ^ m.ocaml_name))
       | _ -> ());
      Hashtbl.replace seen_ns m.mname m;
      Hashtbl.replace seen_mod m.ocaml_name m)
    !order;
  List.rev !order

let mode_stats mods =
  let l = ref 0 and o = ref 0 and s = ref 0 in
  List.iter
    (fun m ->
      let l', o', s' = Modes.count_modes m in
      l := !l + l'; o := !o + o'; s := !s + s')
    mods;
  (!l, !o, !s)
