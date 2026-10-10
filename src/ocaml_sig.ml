(* Direct interop with installed OCaml libraries.

   `(:require [ocaml.Mod :as m])` aliases an OCaml module; `m/f` then
   resolves `f`'s type from the module's .cmi via compiler-libs — real
   signatures, not user annotations. `(:require [ocaml.pkg/name])`
   declares an ocamlfind package: its include dirs (via `ocamlfind
   query -r -format %d`) are searched for cmis and the package is added
   to the link line (-package/-linkpkg).

   Labeled/optional OCaml parameters are written as trailing
   keyword/value pairs: `(m/f x :lbl v)` emits `Mod.f ~lbl:v x`.
   Type constructors the cmi signature uses but lg cannot express
   (abstract types, GADTs, objects) are E102 compile errors — no
   silent `any`. *)

open Typ

type ocaml_lbl = Osig_shim.ocaml_lbl = ONo | OLbl of string | OOpt of string

(* alias -> OCaml module path ("String", "Eio.Fiber", "Unix") *)
let aliases : (string, string) Hashtbl.t = Hashtbl.create 17

(* ocamlfind package declarations from ocaml.pkg/* specs *)
let packages : string list ref = ref []

(* directories searched for cmi files: stdlib + ocaml.pkg query dirs *)
let cmi_dirs : string list ref = ref []

(* emit backend selected on the lg command line; ocaml.* requires are
   native-only ("ocaml"/"oxcaml"), set by bin/lg.ml *)
let backend = ref "ocaml"

(* modpath -> real compilation unit name: "Eio.Fiber" -> "Eio__Fiber",
   from the basename of the cmi file we actually resolved *)
let unit_paths : (string, string) Hashtbl.t = Hashtbl.create 17

exception Unknown_package of string

let run_lines_st cmd =
  let ic = Unix.open_process_in cmd in
  let rec go acc =
    match input_line ic with
    | s -> go (s :: acc)
    | exception End_of_file -> List.rev acc
  in
  let lines = go [] in
  (lines, Unix.close_process_in ic)

let run_lines cmd = fst (run_lines_st cmd)

let init () =
  if !cmi_dirs = [] then
    let stdlib =
      match run_lines "ocamlc -where" with
      | d :: _ -> String.trim d
      | [] -> "/usr/lib/ocaml"
    in
    cmi_dirs := [ stdlib ]

let add_package pkg =
  init ();
  if not (List.mem pkg !packages) then begin
    (match run_lines_st (Printf.sprintf "ocamlfind query %s 2>/dev/null" pkg) with
     | [], _ -> raise (Unknown_package pkg)
     | _ -> ());
    packages := pkg :: !packages;
    (* recursive include dirs so wrapped/sub libraries resolve *)
    let ds =
      run_lines
        (Printf.sprintf "ocamlfind query -r -format '%%d' %s 2>/dev/null" pkg)
    in
    cmi_dirs := !cmi_dirs @ List.map String.trim ds
  end

(* candidate cmi file names for a module path. Covers stdlib wrap
   (String -> stdlib__String.cmi), dune-style package wrap
   (Eio.Fiber -> eio__Fiber.cmi), package dirs (unix -> unix/unix.cmi)
   and literal unit names (Eio__Fiber.cmi from an Mty_alias path) *)
let cmi_candidates modpath =
  let segs = String.split_on_char '.' modpath in
  let last = List.hd (List.rev segs) in
  let flat =
    String.lowercase_ascii (String.map (fun c -> if c = '.' then '_' else c) modpath)
  in
  let wrap =
    match segs with
    | [ n ] -> [ "stdlib__" ^ n ^ ".cmi" ]
    | pkg :: rest ->
      [ String.lowercase_ascii pkg ^ "__" ^ String.concat "__" rest ^ ".cmi" ]
    | [] -> []
  in
  let subdir =
    match segs with
    | [ n ] ->
      (* findlib convention: <libdir>/<pkg>/<pkg>.cmi *)
      [ String.lowercase_ascii n ^ "/" ^ String.lowercase_ascii n ^ ".cmi" ]
    | _ -> []
  in
  [ modpath ^ ".cmi";
    String.lowercase_ascii last ^ ".cmi";
    flat ^ ".cmi";
    String.map (fun c -> if c = '.' then '/' else c) (String.lowercase_ascii modpath)
    ^ ".cmi" ]
  @ wrap @ subdir

(* find the longest prefix of modpath that resolves to a cmi. Returns
   (cmi path, number of leading segments consumed); remaining segments
   are nested modules inside that unit *)
let find_cmi modpath =
  init ();
  let segs = String.split_on_char '.' modpath in
  let nsegs = List.length segs in
  let find_in dirs prefix =
    List.find_map
      (fun d ->
        List.find_map
          (fun c ->
            let p = Filename.concat d c in
            if Sys.file_exists p then Some p else None)
          (cmi_candidates prefix))
      dirs
  in
  let prefix k = String.concat "." (List.filteri (fun i _ -> i < k) segs) in
  let rec try_prefix dirs k =
    if k = 0 then None
    else
      match find_in dirs (prefix k) with
      | Some p -> Some (p, k)
      | None -> try_prefix dirs (k - 1)
  in
  match try_prefix !cmi_dirs nsegs with
  | Some r -> Some r
  | None ->
    (* findlib fallback: treat the first segment as a package name; a
       package resolved this way is also added to the link line *)
    let pkg = String.lowercase_ascii (List.hd segs) in
    (match run_lines (Printf.sprintf "ocamlfind query %s 2>/dev/null" pkg) with
     | _ :: _ ->
       add_package pkg;
       try_prefix !cmi_dirs nsegs
     | [] -> None)

let sig_cache : (string, Types.signature_item list * string * string list) Hashtbl.t =
  Hashtbl.create 17

(* modpath -> (signature items of the resolved cmi, unit name, remaining
   nested-module segments) *)
let signature_of modpath =
  match Hashtbl.find_opt sig_cache modpath with
  | Some s -> Some s
  | None ->
    (match find_cmi modpath with
     | None -> None
     | Some (file, k) ->
       let cmi =
         try Cmi_format.read_cmi file
         with Cmi_format.Error _ ->
           (* .cmi layout/magic is toolchain-bound: a cmi written by a
              different OCaml family (e.g. OxCaml vs upstream) cannot be
              read — report which side produced the file *)
           failwith
             (Printf.sprintf
                "ocaml.%s: %s was compiled by a different OCaml toolchain (lg reads OCaml %s interfaces)"
                modpath file Sys.ocaml_version)
       in
       let unit =
         String.capitalize_ascii
           (Filename.chop_extension (Filename.basename file))
       in
       let segs = String.split_on_char '.' modpath in
       let rest = List.filteri (fun i _ -> i >= k) segs in
       let r = (Osig_shim.cmi_signature cmi, unit, rest) in
       Hashtbl.replace unit_paths modpath (String.concat "." (unit :: rest));
       Hashtbl.replace sig_cache modpath r;
       Some r)

(* Types.type_expr -> (param tys, labels, ret ty) + lg conversion *)
exception Unsupported of string

(* one var table per signature query: occurrences of the same 'a share a
   fresh flexible lg var so ('a -> 'a) instantiates correctly *)
let var_tbl : (int, tvar) Hashtbl.t = Hashtbl.create 7

(* emit-visible path ("Str", "Eio.Fiber") of the signature being read;
   Pident type names inside a cmi are bare ("regexp") — qualify them
   with the owning unit so opaque TCon names unify and emit correctly *)
let cur_unit_path = ref ""

(* dune-wrapped libraries spell one type two ways: `Eio__core__.Switch.t`
   (module inside the hidden `Eio__core__` unit) and `Eio__core__Switch.t`
   (the flat wrapped unit). Fold every `X__.Y` boundary into `X__Y` so
   both spellings unify to the flat unit. *)
let flat_path n =
  let segs = String.split_on_char '.' n in
  let rec go acc = function
    | s1 :: s2 :: tl
      when String.length s1 >= 2
           && String.sub s1 (String.length s1 - 2) 2 = "__" ->
      go acc ((s1 ^ s2) :: tl)
    | s :: tl -> go (s :: acc) tl
    | [] -> List.rev acc
  in
  String.concat "." (go [] segs)

let qualify_tcon n =
  if String.contains n '.' || !cur_unit_path = "" then flat_path n
  else flat_path (!cur_unit_path ^ "." ^ n)

(* relative dotted names inside a cmi bind against the enclosing unit's
   parent scope first: `Net.t` inside `Eio.Stdenv`'s signature means
   `Eio.Net.t` (a sibling submodule), not a top-level `Net` unit.
   Paths already starting `X__` are absolute wrapped-unit spellings. *)
let qualify_rel_tcon n =
  let abs = match String.index_opt n '.' with
    | Some i -> i >= 2 && String.sub n (i - 2) 2 = "__"
    | None -> false
  in
  match String.rindex_opt !cur_unit_path '.' with
  | Some i when String.contains n '.' && not abs ->
    flat_path (String.sub !cur_unit_path 0 i ^ "." ^ n)
  | _ -> qualify_tcon n

(* descend nested-module segments of a modpath through Sig_module decls
   (Mty_signature), following Mty_alias through the aliased unit's cmi.
   Naming tracks the actual unit read ("Eio__core__.Switch") rather than
   the requested alias path ("Eio.Switch") so opaque TCon names match
   the canonical paths other cmis use for the same type.
   Returns (items, emit-visible naming path). *)
let rec walk_submodules items (unit, acc) = function
  | [] -> Some (items, String.concat "." (unit :: List.rev acc))
  | seg :: tl ->
    (match
       List.find_map
         (fun it ->
           match it with
           | Types.Sig_module (id, _, md, _, _) when Ident.name id = seg ->
             (match md.Types.md_type with
              | Types.Mty_signature s -> Some (`Nested s)
              | Types.Mty_alias p ->
                (match find_cmi (Path.name p) with
                 | Some (f, k) ->
                   let cmi = Cmi_format.read_cmi f in
                   let un =
                     String.capitalize_ascii
                       (Filename.chop_extension (Filename.basename f))
                   in
                   (* the alias's own remaining segments are nested
                      modules inside the aliased unit's signature *)
                   let asegs = String.split_on_char '.' (Path.name p) in
                   let arest = List.filteri (fun i _ -> i >= k) asegs in
                   Some (`Alias (Osig_shim.cmi_signature cmi, un, arest))
                 | None -> Some `Missing)
              | _ -> Some `Missing)
           | _ -> None)
         items
     with
     | Some (`Nested inner) -> walk_submodules inner (unit, seg :: acc) tl
     | Some (`Alias (inner, un, arest)) ->
       walk_submodules inner (un, []) (arest @ tl)
     | _ -> None)

(* a Tconstr path "P.t" may hide a transparent manifest alias — ox cmis
   spell String.t as Stdlib__String.t where upstream cmis spell the
   primitive `string`, and user libraries do the same with `type t =
   inner`. Read the type's declaration in P's own cmi and expand the
   manifest when it is transparent. Depth-bound keeps alias cycles
   finite; the declaration's type_params instantiate against the
   Tconstr's args via subst. *)
let manifest_decl path =
  match String.rindex_opt path '.' with
  | None -> None
  | Some i ->
    let modpath = String.sub path 0 i in
    let tname = String.sub path (i + 1) (String.length path - i - 1) in
    (match signature_of modpath with
     | None -> None
     | Some (items, unit, rest) ->
       (match walk_submodules items (unit, []) rest with
        | None -> None
        | Some (items, naming) ->
          Option.map
            (fun td -> (td, naming))
            (List.find_map
               (fun it ->
                 (match it with
                  | Types.Sig_type (id, td, _, _)
                    when Ident.name id = tname -> Some td
                  | _ -> None))
               items)))

let rec ty_of_te ?(depth = 0) ?(subst = []) ?(nested = false) te : ty =
  match Types.get_desc te with
  (* An OCaml arrow chain `a -> b -> r` is the same function as lg's
     (fn [a b] r) — curried application at the OCaml backend is
     syntactically identical — so flatten consecutive arrows into one
     multi-param TFun. This is what lets an lg (fn [k v acc] ...) feed
     an OCaml ('a -> 'b -> 'acc -> 'acc) parameter (Hashtbl.fold etc.);
     without flattening only 1-ary fns were passable to foreign HOFs. *)
  | Types.Tarrow (_, a, r, _) ->
    let rec flat acc t =
      match Types.get_desc t with
      | Types.Tarrow (_, x, y, _) ->
        flat (ty_of_te ~depth ~subst x :: acc) y
      | Types.Tlink u | Types.Tsubst (u, _) -> flat acc u
      | _ -> (List.rev acc, ty_of_te ~depth ~subst t)
    in
    let args, ret = flat [ ty_of_te ~depth ~subst a ] r in
    TFun (args, ret)
  | Types.Ttuple ts ->
    TTuple (List.map (fun (_, t) -> ty_of_te ~depth ~subst t) ts)
  | Types.Tlink t | Types.Tsubst (t, _) -> ty_of_te ~depth ~subst ~nested t
  | Types.Tvar _ ->
    let id = Types.get_id te in
    (match List.assoc_opt id subst with
     | Some t -> t
     | None ->
       (match Hashtbl.find_opt var_tbl id with
        | Some v -> TVar v
        | None ->
          let v = Typ.fresh_var () in
          (match v with
           | TVar tv -> Hashtbl.replace var_tbl id tv
           | _ -> ());
          v))
  | Types.Tpoly (t, _) -> ty_of_te ~depth ~subst t
  | Types.Tconstr (p, args, _) ->
    let n = Path.name p in
    let base =
      match List.rev (String.split_on_char '.' n) with
      | b :: _ -> b
      | [] -> n
    in
    (* primitive paths only: a user-defined `M.list` must not map to the
       lg list builtin — the base-name match binds only when the path is
       literally `list` or `Stdlib.list`, i.e. the primitive itself *)
    let builtin = if n = base || n = "Stdlib." ^ base then base else "" in
    (match builtin, args with
     | "int", [] -> TInt
     | "float", [] -> TFloat
     | "bool", [] -> TBool
     | "string", [] -> TString
     | "char", [] -> TChar
     | "unit", [] -> TUnit
     | "bytes", [] -> TCon ("Stdlib.bytes", [])
       (* opaque handle — lg strings are immutable; convert via
          Bytes.to_string / Bytes.of_string *)
     | "exn", [] -> TCon ("exn", []) (* opaque exception handle — canonical spelling *)
     | "list", [ a ] -> TList (ty_of_te ~depth ~subst ~nested:true a)
     | "option", [ a ] -> TOption (ty_of_te ~depth ~subst ~nested:true a)
     | "array", [ a ] ->
       (* OCaml arrays are not lg lists — mapping `int array` to
          (list int) let a list literal emit where ocamlopt demands an
          [| |] array. Opaque handle; convert via Array.of_list /
          Array.to_list. *)
       TCon ("Stdlib.array", [ ty_of_te ~depth ~subst ~nested:true a ])
     | "result", [ o; e ] ->
       (* (`ok`,`err`) result is NOT lg's option: collapsing it to
          TOption let an `option` value flow into `Result.map` and
          emitted OCaml that cannot typecheck. Keep it a 2-param
          opaque handle — conversion happens at the boundary through
          `Option.to_result`/`Result.to_option`. *)
       TCon ("Stdlib.result",
             [ ty_of_te ~depth ~subst ~nested:true o
             ; ty_of_te ~depth ~subst ~nested:true e ])
     | "ref", [ a ] ->
       (* `Stdlib.ref` is a mutable record, not a clj Atom — same lie
          class as array/result. *)
       TCon ("Stdlib.ref", [ ty_of_te ~depth ~subst ~nested:true a ])
     (* expand a transparent manifest alias (Stdlib__String.t = string);
        on failure fall through to an opaque handle *)
     | _ when depth < 8 ->
       let q = qualify_tcon n and qr = qualify_rel_tcon n in
       let qn, decl =
         if qr <> q then
           match manifest_decl qr with
           | Some _ as d -> (qr, d)
           | None -> (q, manifest_decl q)
         else (q, manifest_decl q)
       in
       (match decl with
        | Some ({ Types.type_manifest = Some m; type_params = ps; _ },
                naming) ->
          (try
             let subst' =
               try
                 List.map2
                   (fun pe a ->
                     (Types.get_id pe, ty_of_te ~depth ~subst ~nested:true a))
                   ps args
               with Invalid_argument _ -> subst
             in
             (* names inside the manifest bind against ITS unit, not
                the signature currently being read *)
             let saved = !cur_unit_path in
             cur_unit_path := naming;
             let r =
               try ty_of_te ~depth:(depth + 1) ~subst:subst' m
               with e -> cur_unit_path := saved; raise e
             in
             cur_unit_path := saved;
             r
           with Unsupported _ ->
             (* an inexpressible manifest is no better than the handle —
                keep the opaque TCon *)
             TCon (qn, List.map (ty_of_te ~depth ~subst ~nested:true) args))
        (* abstract type — name it by the resolved unit so alias
           spellings (Eio.Std.Switch.t) unify with the canonical unit
           spelling (Eio__core__Switch.t) *)
        | Some (_, naming) ->
          (match String.rindex_opt qn '.' with
           | Some i ->
             let tname =
               String.sub qn (i + 1) (String.length qn - i - 1)
             in
             TCon (naming ^ "." ^ tname,
                   List.map (ty_of_te ~depth ~subst ~nested:true) args)
           | None ->
             TCon (qn, List.map (ty_of_te ~depth ~subst ~nested:true) args))
        | _ -> TCon (qn, List.map (ty_of_te ~depth ~subst ~nested:true) args))
     (* abstract/unknown type constructors become opaque handles: they can
        be held and passed back to the library that produced them, never
        constructed from lg directly *)
     | _ ->
       TCon (qualify_tcon n,
             List.map (ty_of_te ~depth ~subst ~nested:true) args))
  (* Row types, objects, univars, first-class modules and empty rows have
     no lg surface. They appear inside library signatures wrapped in a
     constraining constructor — e.g. eio's `[> 'tag ty] r` resources —
     so a fresh variable keeps the enclosing Tconstr shape checkable
     while the row tag itself is left for the OCaml backend to check.
     At the TOP level of a signature (a bare `< .. >` parameter such as
     `Oo.id`) they become opaque handles named by kind — an object or
     package value can flow through a call (`Eio_main.run`'s env) but
     never be constructed or confused with an lg type. *)
  | Types.Tvariant _ | Types.Tobject _ | Types.Tunivar _
  | Types.Tpackage _ | Types.Tfield _ | Types.Tnil ->
    if nested then Typ.fresh_var ()
    else
      let k =
        match Types.get_desc te with
        | Types.Tvariant _ -> "variant" | Types.Tobject _ -> "object"
        | Types.Tunivar _ -> "univar" | Types.Tpackage _ -> "package"
        | _ -> "row"
      in
      TCon ("OCaml." ^ k, [])
  | _ -> raise (Unsupported "type form")

(* decompose a value's type into positional/labeled params + result *)
let decompose te : (ty list) * ocaml_lbl list * ty =
  (* `?x:T` stores the arg as `T option` in the cmi (both toolchains);
     callers see the value type — the lg surface treats `?x` like `~x`,
     omittable and supplied by value (`~x:v` at emit) *)
  let rec strip t =
    match Types.get_desc t with
    | Types.Tlink u | Types.Tsubst (u, _) | Types.Tpoly (u, _) -> strip u
    | Types.Tconstr (p, [ inner ], _)
      when Path.name p = "option" || Path.name p = "Stdlib.option" ->
      inner
    | _ -> t
  in
  let rec go ps ls t =
    match Osig_shim.split_arrow t with
    | Some (OOpt _ as l, a, r) -> go (ps @ [ ty_of_te (strip a) ]) (ls @ [ l ]) r
    | Some (l, a, r) -> go (ps @ [ ty_of_te a ]) (ls @ [ l ]) r
    | None ->
      (match Types.get_desc t with
       | Types.Tlink u | Types.Tsubst (u, _) -> go ps ls u
       | _ -> (ps, ls, ty_of_te t))
  in
  go [] [] te

(* look up `name` in modpath's signature: either a value or a variant
   constructor. Returns (param tys, labels, result ty, is_ctor). *)
let lookup modpath name : (ty list * ocaml_lbl list * ty * bool) option =
  Hashtbl.reset var_tbl;
  match signature_of modpath with
  | None -> None
  | Some (items, unit, rest) ->
    (match walk_submodules items (unit, []) rest with
     | None -> None
     | Some (items, naming) ->
    cur_unit_path := flat_path naming;
    let rec find = function
      | [] -> None
      | Types.Sig_value (id, vd, _) :: tl ->
        if Ident.name id = name then begin
          let ps, ls, r = decompose vd.Types.val_type in
          Some (ps, ls, r, false)
        end else find tl
      | Types.Sig_type (tid, td, _, _) :: tl ->
        (match Osig_shim.variant_ctors td with
         | Some cds ->
           (match
              List.find_opt
                (fun cd -> Ident.name cd.Types.cd_id = name)
                cds
            with
            | Some cd ->
              (match Osig_shim.cstr_tuple cd with
               | Some ts ->
                 let rt =
                   let emod = flat_path naming in
                   match td.Types.type_manifest with
                   | Some m ->
                     (try ty_of_te m
                      with Unsupported _ -> TCon (emod ^ "." ^ Ident.name tid, []))
                   | None -> TCon (emod ^ "." ^ Ident.name tid, [])
                 in
                 Some (List.map ty_of_te ts, List.map (fun _ -> ONo) ts, rt, true)
               | None -> find tl)
            | None -> find tl)
         | None -> find tl)
      | _ :: tl -> find tl
    in
    find items)

(* record labels are projections, not Sig_value functions — `(x/lbl r)`
   resolves here and emits `r.lbl`. Returns (record_ty, field_ty). *)
let lookup_label modpath name : (ty * ty) option =
  Hashtbl.reset var_tbl;
  match signature_of modpath with
  | None -> None
  | Some (items, unit, rest) ->
    (match walk_submodules items (unit, []) rest with
     | None -> None
     | Some (items, naming) ->
       cur_unit_path := flat_path naming;
       let rec find = function
         | [] -> None
         | Types.Sig_type (tid, td, _, _) :: tl ->
           (match Osig_shim.record_lbls td with
            | Some lds ->
              (match
                  List.find_opt
                    (fun ld -> Ident.name ld.Types.ld_id = name)
                    lds
                with
               | Some ld ->
                 let emod = flat_path naming in
                 let rty =
                   TCon
                     ( emod ^ "." ^ Ident.name tid
                     , List.map ty_of_te td.Types.type_params )
                 in
                 (try Some (rty, ty_of_te ~depth:1 ld.Types.ld_type)
                  with Unsupported _ -> find tl)
               | None -> find tl)
            | None -> find tl)
         | _ :: tl -> find tl
       in
       find items)
