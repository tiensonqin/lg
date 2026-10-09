(* Analyzer + Hindley-Milner inference: forms -> typed AST.

   Resolution order for a bare symbol: locals, then current-module defs, then
   builtins. A qualified symbol ns/name resolves through :require aliases or
   as a fully-qualified namespace reference. *)

open Syntax
open Typ
open Ast

(* ---------- environment ---------- *)

type vkind =
  | KLocal of Ast.binder
  | KGlobal of string * string  (* emitted ocaml module path, emitted name *)
  | KBuiltin

type vbind = { vscheme : scheme; vkind : vkind; vvariadic : bool }

type env = (string * vbind) list

(* ns -> (name -> gbind); gexp=false marks a def hidden by an .lgi *)
type gbind = { mutable gsch : scheme; gvar : bool; mutable gexp : bool }
type globals = (string, (string, gbind) Hashtbl.t) Hashtbl.t

type ctx = {
  modl : modl;
  globals : globals;
  mutable env : env;
  mutable implicits : (ty * (unit -> expr)) list;  (* implicit dicts, innermost first *)
  mimplicits : (string * ty) list ref;           (* exported implicit defs of this module *)
  externs : (string, unit) Hashtbl.t;            (* (extern-type n) declared in this module *)

}

(* ns -> (name * dict type) entries exported via (:implicits true) *)
let module_implicits : (string, (string * ty) list) Hashtbl.t = Hashtbl.create 16

(* --strict: heterogeneous literals must carry an explicit ^any-family
   annotation. [strict_ok] is set while descending into a meta form whose
   declared type is dyn-flavoured (any / vec any / map any _ / set any). *)
let strict = ref false
let strict_ok = ref false

let strict_decl t =
  match repr t with
  | TAny | TVec TAny | TSet TAny | TList TAny -> true
  | TMap (TAny, _) | TMap (_, TAny) -> true
  | _ -> false

let lookup env n = List.assoc_opt n env

(* ---------- name mangling ---------- *)

let munge name =
  let b = Buffer.create (String.length name) in
  String.iter
    (fun c ->
      match c with
      | '-' -> Buffer.add_string b "_"
      | '?' -> Buffer.add_string b "_p"
      | '!' -> Buffer.add_string b "_bang"
      | '*' -> Buffer.add_string b "_x"
      | '+' -> Buffer.add_string b "_plus"
      | '<' -> Buffer.add_string b "_lt"
      | '>' -> Buffer.add_string b "_gt"
      | '=' -> Buffer.add_string b "_eq"
      | '/' -> Buffer.add_string b "_ns_"
      | '.' -> Buffer.add_string b "_dot_"
      | c -> Buffer.add_char b c)
    name;
  (* OCaml value identifiers can't start with a capital (ctor/module
     namespace) — lowercase a leading capital *)
  let s = Buffer.contents b in
  if String.length s > 0 && s.[0] >= 'A' && s.[0] <= 'Z' then (
    let bs = Bytes.of_string s in
    Bytes.set bs 0 (Char.lowercase_ascii s.[0]);
    Bytes.to_string bs)
  else s

let ocaml_mod_of_ns ns =
  String.split_on_char '.' ns
  |> List.map (fun seg ->
         let seg = String.map (fun c -> if c = '-' then '_' else c) seg in
         if String.length seg = 0 then "M"
         else if seg.[0] >= 'a' && seg.[0] <= 'z' then String.capitalize_ascii seg
         else if seg.[0] >= 'A' && seg.[0] <= 'Z' then seg
         else "M" ^ seg)
  |> String.concat "_"

(* ---------- type-expression parsing (for ^T metadata) ---------- *)

let primitive_type_names =
  [ "int"; "float"; "bool"; "char"; "string"; "keyword"; "symbol"; "unit"; "nil"; "any" ]

let ty_of_form f : ty =
  let tbl = Hashtbl.create 7 in
  let rec go = function
    | Atom (_, Symbol s) ->
      (match s with
       | "int" -> TInt | "float" -> TFloat | "bool" -> TBool | "char" -> TChar
       | "string" -> TString | "keyword" -> TKeyword | "symbol" -> TSymbol
       | "unit" -> TUnit | "any" -> TAny | "nil" -> TUnit
       | v when String.length v = 1 || v.[0] = '\'' ->
         (* type variable; same name maps to the same var within one
            annotation. Flexible (not rigid): it unifies with what the
            body actually is, then generalize() makes it polymorphic —
            this is what lets `(fn [a (implicit (fn [a] string))] string)`
            dispatch on the call-site type. *)
         (match Hashtbl.find_opt tbl v with
          | Some t -> t
          | None -> let t = fresh_var () in Hashtbl.replace tbl v t; t)
       | v -> TCon (v, []))
    | List (_, [ Atom (_, Symbol "vec"); t ]) -> TVec (go t)
    | List (_, [ Atom (_, Symbol "list"); t ]) -> TList (go t)
    | List (_, [ Atom (_, Symbol "set"); t ]) -> TSet (go t)
    | List (_, [ Atom (_, Symbol "atom"); t ]) -> TAtom (go t)
    | List (_, [ Atom (_, Symbol "option"); t ]) -> TOption (go t)
    | List (_, [ Atom (_, Symbol "implicit"); t ]) -> TImplicit (go t)
    | List (_, [ Atom (_, Symbol "map"); k; v ]) -> TMap (go k, go v)
    | List (_, Atom (_, Symbol "tuple") :: ts) -> TTuple (List.map go ts)
    | List (_, Atom (_, Symbol "fn") :: Vector (_, args) :: rest) ->
      let ret =
        match rest with
        | [ r ] -> go r
        | [ Atom (_, Symbol "->"); r ] -> go r
        | _ -> raise (Type_error (atom_loc f, "malformed (fn [...] ret) type"))
      in
      TFun (List.map go (Array.to_list args), ret)
    | bad -> raise (Type_error (atom_loc bad, "unsupported type expression"))
  in
  go f

(* scan a form's metadata for `^:implicit` / `^{:implicit T}`:
   None = not implicit, Some None = implicit (key = inferred type),
   Some (Some t) = implicit (key = declared T) *)
let rec implicit_ann f : ty option option =
  match f with
  | Meta (_, m, inner) ->
    (match implicit_ann inner with
     | Some _ as r -> r
     | None ->
       (match m with
        | Atom (_, Keyword "implicit") | Atom (_, Symbol "implicit") -> Some None
        | Map (_, kvs) ->
          (match
             List.find_map
               (fun (k, v) ->
                 match k with
                 | Atom (_, Keyword "implicit") | Atom (_, Symbol "implicit") -> Some v
                 | _ -> None)
               kvs
           with
           | Some (Atom (_, Bool true)) | None -> Some None
           | Some tf -> Some (try Some (ty_of_form tf) with Type_error _ -> None))
        | _ -> None))
  | _ -> None

(* Split metadata attached to a form.
   Returns (mode_hint, type_annotation option, inner form). *)
let rec split_meta = function
  | Meta (_, m, f) ->
    let mh, ta, inner = split_meta f in
    let mh' =
      match m with
      | Atom (_, Keyword "local") -> Some Local
      | Atom (_, Keyword "owned") -> Some Owned
      | Atom (_, Keyword "shared") -> Some Shared
      | _ -> mh
    in
    let ta' =
      match ta with
      | Some _ -> ta
      | None ->
        (match m with
         | Atom (_, Keyword k) when List.mem k primitive_type_names ->
           (try Some (ty_of_form (Atom (no_loc, Symbol k))) with Type_error _ -> None)
         | Atom (_, Symbol _) -> (try Some (ty_of_form m) with Type_error _ -> None)
         | List _ -> (try Some (ty_of_form m) with Type_error _ -> None)
         | Map (_, kvs) ->
           (match
              List.find_map (fun (k, v) -> match k with Atom (_, Keyword "sig") -> Some v | _ -> None) kvs
            with
            | Some sigf -> (try Some (ty_of_form sigf) with Type_error _ -> None)
            | None -> None)
         | _ -> None)
    in
    (mh', ta', inner)
  | f -> (None, None, f)

(* ---------- builtins ---------- *)

let scheme_of_ty sty = { svars = free_tvars sty []; sty }
let fn_t args ret = TFun (args, ret)

(* Table of builtin names -> thunk producing a fresh type each call.
   Builtins whose inference needs argument types (numeric ops, map, get, ...)
   are also listed here so bare-symbol resolution succeeds; their real typing
   happens in the special handlers in infer_app. *)
let builtin_table : (string, unit -> ty) Hashtbl.t = Hashtbl.create 131

let reg n t = Hashtbl.replace builtin_table n t

let () =
  let v () = fresh_var () in
  let f args ret = fn_t args ret in
  (* numeric family: '+' etc. typed per call by infer_numeric *)
  List.iter
    (fun n -> reg n (fun () -> let a = v () in f [ a; a ] a))
    [ "+"; "-"; "*"; "/"; "+."; "-."; "*."; "/."; "<"; "<="; ">"; ">=" ];
  reg "inc" (fun () -> f [ TInt ] TInt);
  reg "dec" (fun () -> f [ TInt ] TInt);
  reg "mod" (fun () -> f [ TInt; TInt ] TInt);
  reg "abs" (fun () -> f [ TInt ] TInt);
  reg "float" (fun () -> f [ v () ] TFloat);
  reg "int" (fun () -> f [ v () ] TInt);
  reg "=" (fun () -> let a = v () in f [ a; a ] TBool);
  reg "not=" (fun () -> let a = v () in f [ a; a ] TBool);
  reg "not" (fun () -> f [ TBool ] TBool);
  reg "identity" (fun () -> let a = v () in f [ a ] a);
  reg "constantly" (fun () -> let a = v () and b = v () in f [ a ] (f [ b ] a));
  (* lists *)
  reg "list" (fun () -> let a = v () in f [ a ] (TList a));
  reg "cons" (fun () -> let a = v () in f [ a; TList a ] (TList a));
  reg "concat" (fun () -> let a = v () in f [ TList a; TList a ] (TList a));
  reg "empty?" (fun () -> f [ v () ] TBool);
  reg "count" (fun () -> f [ v () ] TInt);
  (* collections resolved by arg type at special-handler level *)
  List.iter
    (fun n -> reg n (fun () -> let a = v () in f [ a ] a))
    [ "first"; "next"; "rest"; "seq"; "get"; "nth"; "conj"; "range"; "apply" ];
  reg "keys" (fun () -> let k = v () and x = v () in f [ TMap (k, x) ] (TList k));
  reg "vals" (fun () -> let k = v () and x = v () in f [ TMap (k, x) ] (TList x));
  reg "assoc" (fun () -> let c = v () and k = v () and x = v () in f [ c; k; x ] c);
  reg "dissoc" (fun () -> let k = v () and x = v () in f [ TMap (k, x); k ] (TMap (k, x)));
  reg "contains?" (fun () -> f [ v (); v () ] TBool);
  reg "map?" (fun () -> f [ v () ] TBool);
  reg "merge" (fun () -> let k = v () and x = v () in f [ TMap (k, x); TMap (k, x) ] (TMap (k, x)));
  reg "vec" (fun () -> let a = v () in f [ TList a ] (TVec a));
  reg "peek" (fun () -> let a = v () in f [ TVec a ] (TOption a));
  reg "pop" (fun () -> let a = v () in f [ TVec a ] (TVec a));
  reg "set" (fun () -> let a = v () in f [ TList a ] (TSet a));
  reg "disj" (fun () -> let a = v () in f [ TSet a; a ] (TSet a));
  reg "union" (fun () -> let a = v () in f [ TSet a; TSet a ] (TSet a));
  reg "atom" (fun () -> let a = v () in f [ a ] (TAtom a));
  reg "deref" (fun () -> let a = v () in f [ TAtom a ] a);
  reg "reset!" (fun () -> let a = v () in f [ TAtom a; a ] a);
  reg "swap!" (fun () -> let a = v () in f [ TAtom a; f [ a ] a ] a);
  reg "str" (fun () -> f [ v () ] TString);
  reg "name" (fun () -> f [ v () ] TString);
  reg "keyword" (fun () -> f [ TString ] TKeyword);
  reg "symbol" (fun () -> f [ TString ] TSymbol);
  reg "println" (fun () -> f [ v () ] TUnit);
  reg "print" (fun () -> f [ v () ] TUnit);
  reg "pr-str" (fun () -> f [ v () ] TString);
  reg "map" (fun () -> f [ v (); v () ] (v ()));
  reg "filter" (fun () -> f [ v (); v () ] (v ()));
  reg "reduce" (fun () -> f [ v (); v (); v () ] (v ()));
  reg "mapv" (fun () -> f [ v (); v () ] (TVec (v ())));
  reg "filterv" (fun () -> f [ v (); v () ] (TVec (v ())));
  reg "into" (fun () -> let a = v () in f [ TVec a; v () ] (TVec a));
  reg "take" (fun () -> let c = v () in f [ TInt; c ] c);
  reg "drop" (fun () -> let c = v () in f [ TInt; c ] c);
  reg "some?" (fun () -> let a = v () in f [ TOption a ] TBool);
  reg "none?" (fun () -> let a = v () in f [ TOption a ] TBool);
  reg "select-keys" (fun () -> let k = v () and x = v () in f [ TMap (k, x); v () ] (TMap (k, x)));
  reg "update" (fun () -> let k = v () and x = v () in f [ TMap (k, x); k; v () ] (TMap (k, x)));
  reg "get-in" (fun () -> f [ TMap (TKeyword, TAny); v () ] (TOption TAny));
  reg "assoc-in" (fun () -> f [ TMap (TKeyword, TAny); v (); TAny ] (TMap (TKeyword, TAny)));
  reg "comp" (fun () -> f [ v (); v () ] (v ()));
  reg "juxt" (fun () -> f [ v (); v () ] (v ()));
  reg "partial" (fun () -> f [ v (); v () ] (v ()));
  reg "mapcat" (fun () -> let a = v () and b = v () in f [ f [ a ] (TList b); v () ] (TList b));
  reg "interpose" (fun () -> let a = v () in f [ a; v () ] (TList a));
  reg "reverse" (fun () -> let a = v () in f [ a ] a);
  reg "distinct" (fun () -> let a = v () in f [ a ] a);
  reg "second" (fun () -> f [ v () ] (v ()));
  reg "last" (fun () -> f [ v () ] (v ()));
  reg "butlast" (fun () -> f [ v () ] (v ()));
  reg "min" (fun () -> let a = v () in f [ a; a ] a);
  reg "max" (fun () -> let a = v () in f [ a; a ] a);
  reg "every?" (fun () -> let a = v () in f [ f [ a ] TBool; v () ] TBool);
  reg "some" (fun () -> let a = v () in f [ f [ a ] TBool; v () ] TBool);
  reg "take-while" (fun () -> let a = v () in f [ f [ a ] TBool; TList a ] (TList a));
  reg "drop-while" (fun () -> let a = v () in f [ f [ a ] TBool; TList a ] (TList a));
  reg "zipmap" (fun () -> let k = v () and x = v () in f [ v (); v () ] (TMap (k, x)));
  reg "sort" (fun () -> f [ v () ] (v ()));
  reg "sort-by" (fun () -> let a = v () and k = v () in f [ f [ a ] k; v () ] (v ()));
  reg "group-by" (fun () -> let a = v () and k = v () in f [ f [ a ] k; v () ] (TMap (k, TList a)));
  reg "frequencies" (fun () -> let a = v () in f [ TList a ] (TMap (a, TInt)));
  ()

let is_numeric_op = function "+" | "-" | "*" | "/" | "+." | "-." | "*." | "/." -> true | _ -> false
let is_cmp_op = function "<" | "<=" | ">" | ">=" -> true | _ -> false

let is_special_builtin = function
  | "first" | "next" | "rest" | "seq" | "get" | "nth" | "conj" | "assoc"
  | "dissoc" | "map" | "filter" | "reduce" | "mapv" | "filterv" | "into"
  | "apply" | "kw-get" | "contains?" | "empty?" | "count" | "range"
  | "concat" | "merge" | "list" | "vector" | "hash-map" | "hash-set"
  | "str" | "println" | "print" | "pr-str" | "swap!"
  | "select-keys" | "update" | "get-in" | "assoc-in" | "comp" | "juxt"
  | "partial" | "mapcat" | "interpose" | "reverse" | "distinct" | "second"
  | "last" | "butlast" | "min" | "max" | "every?" | "some" | "take-while"
  | "drop-while" | "zipmap" | "sort" | "sort-by" | "group-by" | "frequencies"
  | "vec" | "set" -> true
  | _ -> false

(* ---------- inference ---------- *)

let instantiate_builtin_ty name = Hashtbl.find builtin_table name ()

let last xs = List.nth xs (List.length xs - 1)

let rec infer_program (forms : form list) (mname : string) (path : string) (globals : globals) : modl =
  let m = { mname; ocaml_name = ocaml_mod_of_ns mname; mpath = path; requires = []; tops = []; effects = []; iface_only = false; uses_ctypes = false } in
  let ctx = { modl = m; globals; env = []; implicits = []; mimplicits = ref []; externs = Hashtbl.create 7 } in
  List.iter (infer_top ctx) forms;
  if !(ctx.mimplicits) <> [] then
    Hashtbl.replace module_implicits mname (List.rev !(ctx.mimplicits));
  m

and infer_top ctx f =
  match f with
  | List (l, Atom (_, Symbol "ns") :: rest) -> parse_ns ctx l rest
  | List (_, Atom (_, Symbol "def") :: _) -> ctx.modl.tops <- ctx.modl.tops @ [ TDef (infer_def ctx f) ]
  | List (_, Atom (_, Symbol "defn") :: _) -> ctx.modl.tops <- ctx.modl.tops @ [ TDef (infer_defn ctx f) ]
  | List (l, Atom (_, Symbol "extern-type") :: [ Atom (_, Symbol n) ]) ->
    (* declares an opaque foreign handle type for this module *)
    if Hashtbl.mem ctx.externs n then type_error l ("duplicate extern-type " ^ n);
    Hashtbl.replace ctx.externs n ();
    ctx.modl.tops <- ctx.modl.tops @ [ TExtern (l, n) ]
  | List (l, Atom (_, Symbol "ffi") :: _) ->
    ctx.modl.tops <- ctx.modl.tops @ [ infer_ffi ctx l f ]
  | List (l, Atom (_, Symbol "defrecord") :: Atom (_, Symbol name) :: Vector (_, fields) :: _) ->
    (* (defrecord Point [x y]) — map-backed record: positional ctor
       `->Point` plus `Point?` predicate, fields keyed by same-name kw *)
    let flds =
      List.map
        (function Atom (_, Symbol s) -> s | _ -> type_error l "defrecord fields must be symbols")
        (Array.to_list fields)
    in
    let param_vec = Vector (l, Array.of_list (List.map (fun s -> Atom (l, Symbol s)) flds)) in
    let map_lit =
      Map (l, List.map (fun s -> (Atom (l, Keyword s), Atom (l, Symbol s))) flds)
    in
    let ctor =
      List (l, [ Atom (l, Symbol "defn"); Atom (l, Symbol ("->" ^ name));
                 param_vec; map_lit ])
    in
    let checks =
      List.map (fun s -> List (l, [ Atom (l, Symbol "contains?"); Atom (l, Symbol "v"); Atom (l, Keyword s) ])) flds
    in
    let v_ty =
      Meta (l, List (l, [ Atom (l, Symbol "map"); Atom (l, Symbol "keyword"); Atom (l, Symbol "any") ]),
            Atom (l, Symbol "v"))
    in
    let pred_body =
      List (l, Atom (l, Symbol "and") :: List (l, [ Atom (l, Symbol "map?"); Atom (l, Symbol "v") ]) :: checks)
    in
    let pred =
      List (l, [ Atom (l, Symbol "defn"); Atom (l, Symbol (name ^ "?"));
                 Vector (l, [| v_ty |]); pred_body ])
    in
    ctx.modl.tops <- ctx.modl.tops @ [ TDef (infer_defn ctx ctor); TDef (infer_defn ctx pred) ]
  | List (_, Atom (_, Symbol "defmacro") :: _) ->
    (try Macro.register_defmacro ctx.modl.mname f
     with Macro.Macro_error (l, msg) -> type_error l msg)
  | _ -> ctx.modl.effects <- ctx.modl.effects @ [ infer_expr ctx f ]

and parse_ns ctx l rest =
  match rest with
  | Atom (_, Symbol _) :: clauses ->
    List.iter
      (fun c ->
        match c with
        | List (_, Atom (_, Keyword "require") :: specs) ->
          List.iter
            (fun spec ->
              match spec with
              | Vector (_, els) when Array.length els >= 1 ->
                (match els.(0) with
                 | Atom (_, Symbol ns) ->
                   let rec opts i alias implicits =
                     if i >= Array.length els then (alias, implicits)
                     else
                       match els.(i), (if i + 1 < Array.length els then Some els.(i + 1) else None) with
                       | Atom (_, Keyword "as"), Some (Atom (_, Symbol a)) -> opts (i + 2) (Some a) implicits
                       | Atom (_, Keyword "implicits"), Some (Atom (_, Bool b)) -> opts (i + 2) alias b
                       | Atom (_, Keyword "implicits"), _ -> opts (i + 1) alias true
                       | _ -> type_error l "unsupported :require option"
                   in
                   let alias, implicits = opts 1 None false in
                   ctx.modl.requires <- ctx.modl.requires @ [ (Option.value ~default:ns alias, ns) ];
                   (match implicits with
                    | true ->
                      (match Hashtbl.find_opt module_implicits ns with
                       | Some entries ->
                         List.iter
                           (fun (n, k) ->
                             ctx.implicits <-
                               (k, fun () -> mk l k (EGlobal (ocaml_mod_of_ns ns, munge n, n)))
                               :: ctx.implicits)
                           entries
                       | None -> ())
                    | false -> ())
                 | _ -> type_error l "unsupported :require spec (want [ns] or [ns :as alias] :implicits true)")
              | _ -> type_error l "unsupported :require spec (want a vector)")
            specs
        | _ -> type_error l "unsupported ns clause (only :require is supported)")
      clauses
  | _ -> type_error l "malformed ns form"

and add_implicit ctx l name key =
  ctx.mimplicits := (name, key) :: !(ctx.mimplicits);
  ctx.implicits <-
    (key, fun () -> mk l key (EGlobal (ctx.modl.ocaml_name, munge name, name)))
    :: ctx.implicits

and register_implicit ctx l name imp (top : topdef) =
  match imp with
  | None -> ()
  | Some key_ann ->
    let key = match key_ann with Some t -> t | None -> top.tsch.sty in
    top.timplicit <- Some key;
    add_implicit ctx l name key

and infer_def ctx f =
  let l = atom_loc f in
  match f with
  | List (_, _ :: namef :: rest) ->
    let name, mode_hint, ty_ann, rest, imp =
      match namef with
      | Atom (_, Symbol n) -> (n, None, None, rest, None)
      | Meta (_, _, Atom (_, Symbol n)) as mf ->
        let mh, ta, _ = split_meta mf in
        (n, mh, ta, rest, implicit_ann mf)
      | _ -> type_error l "def requires a name"
    in
    let e = match rest with
      | [ e ] -> e
      | [ Atom (_, Str _); e ] -> e  (* docstring *)
      | _ -> type_error l "malformed def"
    in
    let texpr = infer_expr ctx e in
    (match ty_ann with Some t -> unify texpr.loc texpr.ety t | None -> ());
    (match imp with Some (Some t) -> unify texpr.loc texpr.ety t | _ -> ());
    let sch = generalize [] texpr.ety in
    let top = { tname = name; tloc = l; tsch = sch; texpr; tis_fn = false; tmode = (match mode_hint with Some m -> m | None -> Shared); timplicit = None } in
    register_global ctx name sch false;
    register_implicit ctx l name imp top;
    top
  | _ -> type_error l "malformed def"

and infer_defn ctx f =
  let l = atom_loc f in
  match f with
  | List (_, _ :: namef :: rest) ->
    let name, mode_hint, ty_ann, imp =
      match namef with
      | Atom (_, Symbol n) -> (n, None, None, None)
      | Meta (_, _, Atom (_, Symbol n)) as mf ->
        let mh, ta, _ = split_meta mf in
        (n, mh, ta, implicit_ann mf)
      | _ -> type_error l "defn requires a name"
    in
    let rest = match rest with Atom (_, Str _) :: r -> r | r -> r in
    (* `defn f ^(fn [..] r) [args] body` — meta on the param vector *)
    let rest, ty_ann =
      match rest with
      | (Meta _ as mf) :: r ->
        let _, ta, inner = split_meta mf in
        (inner :: r, (match ta with Some _ -> ta | None -> ty_ann))
      | r -> (r, ty_ann)
    in
    (match rest with
     | Vector (_, params) :: body ->
       (* allow self-recursion: bind name to a fresh var while the body is
          inferred, then unify it with the inferred fn type *)
       let saved = ctx.env and saved_imp = ctx.implicits in
       let self_v = fresh_var () in
       ctx.env <- (name, { vscheme = mono self_v; vkind = KGlobal (ctx.modl.ocaml_name, munge name); vvariadic = false }) :: ctx.env;
       let fe = infer_fn ctx l (Some name) params body in
       ctx.env <- saved; ctx.implicits <- saved_imp;
       unify l self_v fe.ety;
       (match ty_ann with Some t -> unify l fe.ety t | None -> ());
       (match imp with Some (Some t) -> unify l fe.ety t | _ -> ());
       (* carry (implicit …) marks from the signature onto the stored
          scheme — unify is transparent over TImplicit so the inferred
          type alone would forget which params are implicit *)
       let sch_ty =
         match ty_ann with
         | Some t ->
           (match repr t, repr fe.ety with
            | TFun (sts, _), TFun (its, r) when List.length sts = List.length its ->
              TFun (List.map2
                      (fun st it -> match repr st with TImplicit _ -> TImplicit it | _ -> it)
                      sts its,
                    r)
            | _ -> fe.ety)
         | None -> fe.ety
       in
       let sch = generalize [] sch_ty in
       let variadic = match fe.desc with EFun fn -> fn.variadic <> None | _ -> false in
       let top = { tname = name; tloc = l; tsch = sch; texpr = fe; tis_fn = true; tmode = (match mode_hint with Some m -> m | None -> Shared); timplicit = None } in
       register_global ctx name sch variadic;
       register_implicit ctx l name imp top;
       top
     | (List (_, Vector _ :: _) :: _) as rest when List.for_all (function List (_, Vector _ :: _) -> true | _ -> false) rest ->
       (* multi-arity: (defn f ([p] b) ([p p] b) ...)
          Each arity compiles to its own global `f__a<argc>`; calls to `f`
          are rewritten to the matching arity in infer_app_no_macro.
          Placeholder schemes are registered up-front so recursive calls
          dispatch before bodies are inferred. *)
       let arities =
         List.map
           (fun af ->
             match af with
             | List (al, Vector (_, ps) :: body) -> (al, ps, body)
             | _ -> type_error l "malformed arity")
           rest
       in
       let infos =
         List.map
           (fun (al, ps, body) ->
             let an = Printf.sprintf "%s__a%d" name (Array.length ps) in
             let ph = TFun (List.init (Array.length ps) (fun _ -> fresh_var ()), fresh_var ()) in
             register_global ctx an (mono ph) false;
             (al, ps, body, an, ph))
           arities
       in
       let tops =
         List.map
           (fun (al, ps, body, an, ph) ->
             let fe = infer_fn ctx al (Some an) ps body in
             unify al ph fe.ety;
             { tname = an; tloc = al; tsch = generalize [] fe.ety; texpr = fe;
               tis_fn = true; tmode = (match mode_hint with Some m -> m | None -> Shared); timplicit = None })
           infos
       in
       List.iter (fun t -> register_global ctx t.tname t.tsch false) tops;
       (* `f` aliases the first arity: value use gets arity 1's type; direct
          calls are arity-rewritten. *)
       let first = List.hd tops in
       let alias_e = mk l first.texpr.ety (EGlobal (ctx.modl.ocaml_name, munge first.tname, first.tname)) in
       let alias = { tname = name; tloc = l; tsch = first.tsch; texpr = alias_e; tis_fn = false; tmode = Shared; timplicit = None } in
       register_global ctx name alias.tsch false;
       ctx.modl.tops <- ctx.modl.tops @ (List.map (fun t -> TDef t) tops);
       alias
     | _ -> type_error l "malformed defn body (want [params] body or ([params] body)+)")
  | _ -> type_error l "malformed defn"


(* FFI: parse a keyword into a type. Scalars, (option <t>), collections,
   declared extern-types; :fn<...> callbacks are not yet supported. *)
and ffi_ty ctx l f : ty =
  let rec kw k =
    match String.index_opt k '<' with
    | None ->
      (match k with
       | "int" -> TInt | "float" -> TFloat | "bool" -> TBool | "char" -> TChar
       | "string" -> TString | "unit" -> TUnit | "keyword" -> TKeyword
       | "symbol" -> TSymbol | "any" -> TAny | "nil" -> TUnit
       | n when Hashtbl.mem ctx.externs n -> TCon (n, [])
       | n -> type_error l ("unknown ffi type :" ^ n))
    | Some i ->
      let head = String.sub k 0 i in
      let inner =
        if k.[String.length k - 1] <> '>' then type_error l ("malformed ffi type :" ^ k)
        else String.sub k (i + 1) (String.length k - i - 2)
      in
      let args = List.map kw (String.split_on_char ';' inner) in
      (match head, args with
       | "option", [ t ] -> TOption t
       | "vec", [ t ] -> TVec t
       | "list", [ t ] -> TList t
       | "set", [ t ] -> TSet t
       | "atom", [ t ] -> TAtom t
       | "map", [ k2; v ] -> TMap (k2, v)
       | "fn", _ -> type_error l "ffi :fn<...> callbacks are not yet supported"
       | _ -> type_error l ("bad ffi type constructor :" ^ k))
  in
  match f with
  | Atom (_, Keyword k) -> kw k
  | _ -> type_error l "ffi expects a type keyword (:int, :option<int>, :reader, ...)"

(* static check that [t] can appear in an ffi signature *)
and ffi_check_closed l t =
  match repr t with
  | TVar _ -> type_error l "ffi signatures must be statically closed"
  | TAny -> type_error l "any cannot cross the FFI boundary (dyn is an internal repr)"
  | TImplicit _ -> type_error l "implicit params cannot cross the FFI boundary"
  | TTuple _ -> type_error l "tuple has no FFI mapping"
  | TList t | TVec t | TSet t | TAtom t | TOption t -> ffi_check_closed l t
  | TMap (a, b) -> ffi_check_closed l a; ffi_check_closed l b
  | TFun (a, r) -> List.iter (ffi_check_closed l) a; ffi_check_closed l r
  | _ -> ()

(* (ffi name [arg-tys] ret-ty {:ocaml "stub" | :native "sym" [:library p]}) *)
and infer_ffi ctx l f : top =
  match f with
  | List (_, _ :: namef :: Vector (_, argfs) :: retf :: optfs) ->
    let name, imp =
      match namef with
      | Atom (_, Symbol n) -> (n, None)
      | Meta (_, _, Atom (_, Symbol n)) as mf -> (n, implicit_ann mf)
      | _ -> type_error l "ffi requires a name"
    in
    let args = List.map (ffi_ty ctx l) (Array.to_list argfs) in
    let ret = ffi_ty ctx l retf in
    List.iter (ffi_check_closed l) args;
    ffi_check_closed l ret;
    (match args with [ TUnit ] -> type_error l "explicit :unit argument — use []" | _ -> ());
    let sel, lib =
      let sel = ref None and lib = ref None in
      List.iter
        (fun o ->
          match o with
          | Map (_, kvs) ->
            List.iter
              (fun (k, v) ->
                match k, v with
                | Atom (_, Keyword "ocaml"), Atom (_, Str s) -> sel := Some (FOcaml s)
                | Atom (_, Keyword "native"), Atom (_, Str s) -> sel := Some (FNative s)
                | Atom (_, Keyword "js"), _ ->
                  type_error l "ffi :js backend needs the melange emit — not yet implemented"
                | Atom (_, Keyword "library"), Atom (_, Str s) -> lib := Some s
                | _ -> type_error l "unsupported ffi option (want :ocaml/:native \"sym\", :library \"path\")")
              kvs
          | _ -> type_error l "ffi options must be a literal map")
        optfs;
      (match !sel with
       | None -> type_error l "ffi requires a :ocaml or :native selector"
       | Some s -> (s, !lib))
    in
    (match sel with
     | FOcaml _ ->
       if List.length args > 5 then type_error l "ffi :ocaml supports at most 5 arguments";
       if lib <> None then type_error l ":library does not apply to :ocaml ffi"
     | FNative _ -> ctx.modl.uses_ctypes <- true);
    let fty = TFun (args, ret) in
    register_global ctx name (mono fty) false;
    (match imp with
     | Some key_ann -> add_implicit ctx l name (match key_ann with Some t -> t | None -> fty)
     | None -> ());
    TFfi (l, name, args, ret, sel, lib)
  | _ -> type_error l "malformed ffi (want (ffi name [tys] ty {:ocaml|:native \"sym\"}))"

and register_global ctx name sch variadic =
  let tbl =
    match Hashtbl.find_opt ctx.globals ctx.modl.mname with
    | Some t -> t
    | None -> let t = Hashtbl.create 17 in Hashtbl.replace ctx.globals ctx.modl.mname t; t
  in
  Hashtbl.replace tbl name { gsch = sch; gvar = variadic; gexp = true }

and infer_fn ctx l name params body : expr =
  let items = Array.to_list params in
  let rec split acc = function
    | [] -> (List.rev acc, None)
    | Atom (_, Symbol "&") :: Atom (_, Symbol r) :: [] -> (List.rev acc, Some r)
    | Atom (_, Symbol "&") :: [ Meta (_, _, Atom (_, Symbol r)) ] -> (List.rev acc, Some r)
    | x :: xs -> split (x :: acc) xs
  in
  let ps, variadic = split [] items in
  (* non-symbol params destructure into a temp + extra bindings; the
     destructured names see each other only inside the body *)
  let mk_param f =
    let _, ta, inner = split_meta f in
    match inner with
    | Atom (_, Symbol s) ->
      let b = fresh_binder s in
      b.bty <- (match ta with Some t -> t | None -> fresh_var ());
      (match implicit_ann f with
       | Some (Some t) -> b.bty <- TImplicit t
       | Some None -> b.bty <- TImplicit b.bty
       | None -> ());
      ((s, b), None)
    | (Vector _ | Map _) ->
      let b = fresh_binder "dp" in
      b.bty <- (match ta with Some t -> t | None -> fresh_var ());
      (("", b), Some (inner, b))
    | _ -> type_error l "fn params must be symbols or destructuring patterns"
  in
  let binders, destr_jobs = List.split (List.map mk_param ps) in
  let destr_jobs = List.filter_map (fun x -> x) destr_jobs in
  let vbinder =
    match variadic with
    | None -> None
    | Some s -> let b = fresh_binder s in b.bty <- TList (fresh_var ()); Some (s, b)
  in
  let saved = ctx.env and saved_imp = ctx.implicits in
  (* named fn self-binding: `(fn f ...) → f` refers to the fn itself *)
  let self_b =
    match name with
    | Some n ->
      let fb = fresh_binder n in
      let rest_ty = (match vbinder with Some (_, vb) -> [ vb.bty ] | None -> []) in
      fb.bty <- TFun (List.map (fun (_, p) -> p.bty) binders @ rest_ty, fresh_var ());
      ctx.env <- (n, { vscheme = mono fb.bty; vkind = KLocal fb; vvariadic = false }) :: ctx.env;
      Some fb
    | None -> None
  in
  List.iter
    (fun (s, b) -> if s <> "" then ctx.env <- (s, { vscheme = mono b.bty; vkind = KLocal b; vvariadic = false }) :: ctx.env)
    binders;
  (match vbinder with
   | Some (s, b) -> ctx.env <- (s, { vscheme = mono b.bty; vkind = KLocal b; vvariadic = false }) :: ctx.env
   | None -> ());
  (* destructure jobs: each temp binder feeds bind_pattern, extending env *)
  let d_pairs =
    List.concat
      (List.map
         (fun (pat, tb) -> bind_pattern ctx l pat (mk l tb.bty (ELocal tb)))
         destr_jobs)
  in
  let body_es = List.map (infer_expr ctx) body in
  ctx.env <- saved; ctx.implicits <- saved_imp;
  let body_e =
    match body_es with
    | [] -> mk l TUnit ENil
    | [ e ] -> e
    | es -> mk l (last es).ety (EDo es)
  in
  let body_e = match d_pairs with [] -> body_e | _ -> mk l body_e.ety (ELet (d_pairs, body_e)) in
  let ptys = List.map (fun (_, b) -> b.bty) binders in
  let fty =
    match vbinder with
    | Some (_, vb) -> TFun (ptys @ [ vb.bty ], body_e.ety)
    | None -> TFun (ptys, body_e.ety)
  in
  (match self_b with Some fb -> unify l fb.bty fty | None -> ());
  mk l fty
    (EFun { fname = name; fself = self_b; params = List.map snd binders; variadic = (match vbinder with Some (_, b) -> Some b | None -> None); body = body_e; fescapes = false })

and infer_expr ctx f : expr =
  match f with
  | Atom (l, a) ->
    (match a with
     | Int i -> mk l TInt (EInt i)
     | Float x -> mk l TFloat (EFloat x)
     | Bool b -> mk l TBool (EBool b)
     | Char c -> mk l TChar (EChar c)
     | Str s -> mk l TString (EStr s)
     | Keyword k -> mk l TKeyword (EKeyword k)
     | Nil -> mk l TUnit ENil
     | Symbol "None" -> mk l (TOption (fresh_var ())) (EOpt None)
     | Symbol s -> infer_symbol ctx l s)
  | Vector (l, items) ->
    let es = List.map (infer_expr ctx) (Array.to_list items) in
    let elem = fresh_var () in
    let het =
      try List.iter (fun e -> unify e.loc elem e.ety) es; false
      with Type_error _ -> true
    in
    if het && !strict && not !strict_ok then
      type_error l "strict: heterogeneous literal requires ^any";
    mk l (TVec (if het then TAny else elem)) (EVecLit es)
  | Map (l, kvs) ->
    let kes = List.map (fun (k, v) -> (infer_expr ctx k, infer_expr ctx v)) kvs in
    let kt = fresh_var () and vt = fresh_var () in
    let het_k =
      try List.iter (fun (k, _) -> unify k.loc kt k.ety) kes; false
      with Type_error _ -> true
    in
    let het_v =
      try List.iter (fun (_, v) -> unify v.loc vt v.ety) kes; false
      with Type_error _ -> true
    in
    if (het_k || het_v) && !strict && not !strict_ok then
      type_error l "strict: heterogeneous literal requires ^any";
    mk l (TMap ((if het_k then TAny else kt), (if het_v then TAny else vt))) (EMapLit kes)
  | Set (l, items) ->
    let es = List.map (infer_expr ctx) items in
    let elem = fresh_var () in
    let het =
      try List.iter (fun e -> unify e.loc elem e.ety) es; false
      with Type_error _ -> true
    in
    if het && !strict && not !strict_ok then
      type_error l "strict: heterogeneous literal requires ^any";
    mk l (TSet (if het then TAny else elem)) (ESetLit es)
  | Quote (l, qf) -> quote_to_expr l qf
  | Meta (l, _, inner) ->
    let _, ta0, _ = split_meta f in
    let saved = !strict_ok in
    (match ta0 with Some t when strict_decl t -> strict_ok := true | _ -> ());
    let e = infer_expr ctx inner in
    strict_ok := saved;
    (match split_meta f with
     | _, Some t, _ ->
       (match repr e.ety, repr t with
        | TAny, c ->
          e.ety <- t;
          mk l t (EUnbox (e, c))
        | TOption TAny, TOption c ->
          e.ety <- t;
          mk l t (EUnboxOpt (e, c))
        | _ -> unify e.loc e.ety t; e)
     | _ -> e)
  | List (l, items) -> infer_call ctx l items

and infer_symbol ctx l s : expr =
  (* hygiene: a marked symbol (x__h7) resolves as a local binder under its
     marked name only; if that misses, the *unmarked* name resolves globals
     and builtins but never the caller's locals — that is what makes
     defmacro hygienic. *)
  match lookup ctx.env s with
  | Some { vkind = KLocal b; _ } ->
    b.bused <- b.bused + 1;
    mk l b.bty (ELocal b)
  | _ ->
    let s = Macro.unmark s in
    match String.index_opt s '/' with
  | Some i when i > 0 ->
    let ns = String.sub s 0 i and n = String.sub s (i + 1) (String.length s - i - 1) in
    let target = match List.assoc_opt ns ctx.modl.requires with Some full -> full | None -> ns in
    if target = ctx.modl.mname then infer_symbol ctx l n
    else (
      match Hashtbl.find_opt ctx.globals target with
      | Some tbl ->
        (match Hashtbl.find_opt tbl n with
         | Some { gsch = sch; gexp = true; _ } ->
           mk l (instantiate sch) (EGlobal (ocaml_mod_of_ns target, munge n, s))
         | Some _ -> type_error l (Printf.sprintf "%s is not exported by module %s" s target)
         | None -> type_error l (Printf.sprintf "unresolved symbol %s (no such var in %s)" s target))
      | None -> type_error l (Printf.sprintf "unresolved symbol %s (module %s not loaded)" s target))
  | _ ->
    (match lookup ctx.env s with
     | Some { vscheme = sch; vkind = KGlobal (m, n); _ } -> mk l (instantiate sch) (EGlobal (m, n, s))
     | Some { vkind = KBuiltin; _ } -> mk l (instantiate_builtin_ty s) (EBuiltin s)
     | _ ->
       (match Hashtbl.find_opt ctx.globals ctx.modl.mname with
        | Some tbl when Hashtbl.mem tbl s ->
          (match Hashtbl.find_opt tbl s with
           | Some { gsch = sch; _ } -> mk l (instantiate sch) (EGlobal (ctx.modl.ocaml_name, munge s, s))
           | None -> type_error l ("unresolved symbol " ^ s))
        | _ ->
          (match Hashtbl.find_opt builtin_table s with
           | Some _ -> mk l (instantiate_builtin_ty s) (EBuiltin s)
           | None -> type_error l ("unresolved symbol " ^ s))))

and quote_to_expr _l f : expr =
  let rec go f : expr =
    match f with
    | Atom (l, Int i) -> mk l TInt (EInt i)
    | Atom (l, Float x) -> mk l TFloat (EFloat x)
    | Atom (l, Bool b) -> mk l TBool (EBool b)
    | Atom (l, Char c) -> mk l TChar (EChar c)
    | Atom (l, Str s) -> mk l TString (EStr s)
    | Atom (l, Keyword k) -> mk l TKeyword (EKeyword k)
    | Atom (l, Symbol s) -> mk l TSymbol (ESymbol s)
    | Atom (l, Nil) -> mk l TUnit ENil
    | Vector (l, items) ->
      let es = List.map go (Array.to_list items) in
      let elem = fresh_var () in
      List.iter (fun e -> unify e.loc elem e.ety) es;
      mk l (TVec elem) (EVecLit es)
    | List (l, items) ->
      let es = List.map go items in
      let elem = fresh_var () in
      List.iter (fun e -> unify e.loc elem e.ety) es;
      mk l (TList elem) (EListLit es)
    | Map (l, kvs) ->
      let kes = List.map (fun (k, v) -> (go k, go v)) kvs in
      let kt = fresh_var () and vt = fresh_var () in
      List.iter (fun (k, v) -> unify k.loc kt k.ety; unify v.loc vt v.ety) kes;
      mk l (TMap (kt, vt)) (EMapLit kes)
    | Set (l, items) ->
      let es = List.map go items in
      let elem = fresh_var () in
      List.iter (fun e -> unify e.loc elem e.ety) es;
      mk l (TSet elem) (ESetLit es)
    | Meta (_, _, inner) | Quote (_, inner) -> go inner
  in
  go f

and desugar_thread l is_first f args =
  match args with
  | [] -> f
  | a :: rest ->
    let applied =
      match a with
      | List (l2, g :: gs) -> List (l2, if is_first then (g :: f :: gs) else (g :: gs) @ [ f ])
      | g -> List (l, [ g; f ])
    in
    desugar_thread l is_first applied rest

and infer_call ctx l items : expr =
  (* hygiene: unmark a marked head symbol so special forms inside a
     syntax-quoted template still dispatch as special forms *)
  let items =
    match items with
    | Atom (lh, Symbol s) :: rest ->
      let s' = Macro.unmark s in
      if s' = s then items else Atom (lh, Symbol s') :: rest
    | _ -> items
  in
  match items with
  | [] -> mk l (TList (fresh_var ())) (EListLit [])
  | Atom (_, Symbol "if") :: [ c; t; e ] -> infer_if ctx l c t e
  | Atom (_, Symbol "if") :: [ c; t ] -> infer_if ctx l c t (Atom (l, Nil))
  | Atom (_, Symbol "do") :: body -> infer_do ctx l body
  | Atom (_, Symbol "when") :: c :: body ->
    infer_if ctx l c (List (l, Atom (l, Symbol "do") :: body)) (Atom (l, Nil))
  | Atom (_, Symbol "let") :: Vector (_, binds) :: body -> infer_let ctx l binds body
  | Atom (_, Symbol "fn") :: rest -> infer_fn_call ctx l rest
  | Atom (_, Symbol "and") :: args -> infer_and ctx l args
  | Atom (_, Symbol "or") :: args -> infer_or ctx l args
  | Atom (_, Symbol "cond") :: args -> infer_cond ctx l args
  | Atom (_, Symbol "->") :: x :: steps -> infer_expr ctx (desugar_thread l true x steps)
  | Atom (_, Symbol "->>") :: x :: steps -> infer_expr ctx (desugar_thread l false x steps)
  | Atom (_, Symbol "match") :: scrut :: clauses -> infer_match ctx l scrut clauses
  | Atom (_, Symbol "case") :: scrut :: clauses ->
    (* (case x lit v lit v default) — literals become match patterns *)
    (match List.rev clauses with
     | dflt :: pairs ->
       let pairs = List.rev pairs in
       if List.length pairs mod 2 <> 0 then type_error l "case: literal/body pairs expected";
       let rec go = function
         | k :: v :: t -> k :: v :: go t
         | _ -> [] in
       infer_match ctx l scrut (go pairs @ [ Atom (l, Symbol "_"); dflt ])
     | [] -> type_error l "malformed case")
  | Atom (_, Symbol "Some") :: [ arg ] ->
    let e = infer_expr ctx arg in
    mk l (TOption e.ety) (EOpt (Some e))
  | Atom (_, Symbol "if-let") :: Vector (_, [| b; src |]) :: body -> infer_if_let ctx l b src body
  | Atom (_, Symbol "when-let") :: Vector (_, [| b; src |]) :: body ->
    infer_if_let ctx l b src [ List (l, Atom (l, Symbol "do") :: body); Atom (l, Nil) ]
  | Atom (_, Symbol "quote") :: [ qf ] -> quote_to_expr l qf
  | Atom (_, Keyword k) :: args ->
    (* (:k m) / (:k m default) *)
    let kw = mk l TKeyword (EKeyword k) in
    infer_special ctx l "kw-get" (mk l (fresh_var ()) (EBuiltin "kw-get"))
      (kw :: List.map (infer_expr ctx) args)
  | callee :: args -> infer_app ctx l callee args

and join_branches l a b =
  match repr a.ety, repr b.ety with
  | TAny, TAny -> (TAny, a, b)
  | TAny, _ -> (TAny, a, mk b.loc TAny (EBox b))
  | _, TAny -> (TAny, mk a.loc TAny (EBox a), b)
  | _ -> unify l a.ety b.ety; (a.ety, a, b)

and infer_if ctx l c t e =
  let ce = infer_expr ctx c in
  unify ce.loc ce.ety TBool;
  let te = infer_expr ctx t and ee = infer_expr ctx e in
  let ret, te, ee = join_branches l te ee in
  mk l ret (EIf (ce, te, ee))

and infer_do ctx l body =
  let es = List.map (infer_expr ctx) body in
  match es with [] -> mk l TUnit ENil | _ -> mk l (last es).ety (EDo es)

(* Destructuring: a binding pattern is a symbol, a vector `[p ..]` whose
   elements destructure by index, or a map `{ :keys [..] :as s :or {..} |
   (:kw p) }`. bind_pattern appends (temp/elem) binder pairs and registers
   names in ctx.env. *)
and bind_pattern ctx l pat rhs : (binder * expr) list =
  let _, ta, inner = split_meta pat in
  let bind_one b rhs =
    (match ta with Some t -> unify l rhs.ety t; b.bty <- t | None -> ());
    b.bty <- rhs.ety;
    b.blit <- is_lit rhs;
    [(b, rhs)]
  in
  let bind_sym s rhs =
    let b = fresh_binder s in
    b.bty <- rhs.ety;
    ctx.env <- (s, { vscheme = mono b.bty; vkind = KLocal b; vvariadic = false }) :: ctx.env;
    (match implicit_ann pat with
     | Some key_ann ->
       let key = match key_ann with Some t -> t | None -> b.bty in
       ctx.implicits <- (key, fun () -> mk rhs.loc key (ELocal b)) :: ctx.implicits
     | None -> ());
    bind_one b rhs
  in
  match inner with
  | Atom (_, Symbol s) -> bind_sym s rhs
  | Atom (_, Nil) -> []  (* nil pattern binds nothing *)
  | Vector (vl, items) ->
    let rhs =
      match repr rhs.ety with
      | TAny -> mk vl (TVec TAny) (EUnbox (rhs, TVec TAny))
      | _ -> rhs
    in
    let tmp = fresh_binder "dv" in
    tmp.bty <- rhs.ety;
    let el = fresh_var () in
    unify vl rhs.ety (TVec el);
    let tmp_e = mk vl rhs.ety (ELocal tmp) in
    (tmp, rhs)
    :: List.concat
         (List.mapi
            (fun i p ->
              let ith =
                mk vl el
                  (ECall (mk vl (TFun ([ TVec el; TInt ], el)) (EBuiltin "nth"),
                          [ tmp_e; mk vl TInt (EInt i) ]))
              in
              bind_pattern ctx vl p ith)
            (Array.to_list items))
  | Map (ml, kvs) ->
    let rhs =
      match repr rhs.ety with
      | TAny -> mk ml (TMap (TAny, TAny)) (EUnbox (rhs, TMap (TAny, TAny)))
      | _ -> rhs
    in
    let tmp = fresh_binder "dm" in
    tmp.bty <- rhs.ety;
    let tmp_e = mk ml rhs.ety (ELocal tmp) in
    (* :or defaults are collected before the other entries are bound *)
    let or_defaults =
      match
        List.find_map
          (fun (k, v) -> match k with Atom (_, Keyword "or") -> Some v | _ -> None)
          kvs
      with
      | Some (Map (_, ds)) -> ds
      | _ -> []
    in
    let default_for kname =
      List.find_map
        (fun (dk, dv) ->
          match dk with
          | Atom (_, Keyword k) when k = kname -> Some dv
          | Atom (_, Symbol k) when k = kname -> Some dv
          | _ -> None)
        or_defaults
    in
    (* (:kw m) or (:kw m default) *)
    let kw_get kw def =
      let kw_e = mk ml TKeyword (EKeyword kw) in
      let vt = fresh_var () in
      unify ml rhs.ety (TMap (TKeyword, vt));
      match def with
      | Some df ->
        let de = infer_expr ctx df in
        unify ml de.ety vt;
        mk ml vt (ECall (mk ml (TFun ([ TKeyword; TMap (TKeyword, vt); vt ], vt)) (EBuiltin "kw-get"), [ kw_e; tmp_e; de ]))
      | None ->
        mk ml (TOption vt) (ECall (mk ml (TFun ([ TKeyword; TMap (TKeyword, vt) ], TOption vt)) (EBuiltin "kw-get"), [ kw_e; tmp_e ]))
    in
    (* (get m "s" def) — string keys *)
    let str_get skey def =
      let sk_e = mk ml TString (EStr skey) in
      let vt = fresh_var () in
      unify ml rhs.ety (TMap (TString, vt));
      match def with
      | Some df ->
        let de = infer_expr ctx df in
        unify ml de.ety vt;
        mk ml vt (ECall (mk ml (TFun ([ TString; TMap (TString, vt); vt ], vt)) (EBuiltin "get"), [ tmp_e; sk_e; de ]))
      | None ->
        mk ml (TOption vt) (ECall (mk ml (TFun ([ TString; TMap (TString, vt) ], TOption vt)) (EBuiltin "get"), [ tmp_e; sk_e ]))
    in
    (tmp, rhs)
    :: List.concat
         (List.map
            (fun (kf, pf) ->
              match kf, pf with
              | Atom (_, Keyword "keys"), Vector (_, syms) ->
                List.concat
                  (List.map
                     (fun sf ->
                       match sf with
                       | Atom (sl, Symbol sn) -> bind_pattern ctx sl sf (kw_get sn (default_for sn))
                       | _ -> type_error l ":keys entries must be symbols")
                     (Array.to_list syms))
              | Atom (_, Keyword "strs"), Vector (_, syms) ->
                List.concat
                  (List.map
                     (fun sf ->
                       match sf with
                       | Atom (sl, Symbol sn) -> bind_pattern ctx sl sf (str_get sn (default_for sn))
                       | _ -> type_error l ":strs entries must be symbols")
                     (Array.to_list syms))
              | Atom (_, Keyword "as"), Atom (sl, Symbol sn) -> bind_pattern ctx sl (Atom (sl, Symbol sn)) (mk ml rhs.ety (ELocal tmp))
              | Atom (_, Keyword "or"), Map _ -> []
              | Atom (_, Symbol _), Atom (_, Keyword kw) -> bind_pattern ctx ml kf (kw_get kw (default_for kw))
              | Atom (_, Symbol _), Atom (_, Str sk) -> bind_pattern ctx ml kf (str_get sk (default_for sk))
              | Atom (_, Keyword kw), _ -> bind_pattern ctx ml pf (kw_get kw (default_for kw))
              | Atom (_, Str sk), _ -> bind_pattern ctx ml pf (str_get sk (default_for sk))
              | _ -> type_error l "unsupported map destructuring entry")
            kvs)
  | _ -> type_error l "unsupported destructuring pattern"

and infer_let ctx l binds body =
  let items = Array.to_list binds in
  let saved = ctx.env and saved_imp = ctx.implicits in
  let rec go acc = function
    | [] -> List.rev acc
    | bform :: eform :: rest ->
      let e = infer_expr ctx eform in
      let pairs = bind_pattern ctx l bform e in
      go (List.rev_append pairs acc) rest
    | _ -> type_error l "let requires an even number of binding forms"
  in
  let pairs = go [] items in
  let body_es = List.map (infer_expr ctx) body in
  ctx.env <- saved; ctx.implicits <- saved_imp;
  let body_e = match body_es with [] -> mk l TUnit ENil | [ e ] -> e | es -> mk l (last es).ety (EDo es) in
  mk l body_e.ety (ELet (pairs, body_e))

and infer_and ctx l args =
  match args with
  | [] -> mk l TBool (EBool true)
  | [ a ] ->
    let e = infer_expr ctx a in
    unify e.loc e.ety TBool; e
  | a :: rest ->
    let e = infer_expr ctx a in
    unify e.loc e.ety TBool;
    mk l TBool (EIf (e, infer_and ctx l rest, mk l TBool (EBool false)))

and infer_or ctx l args =
  match args with
  | [] -> mk l TBool (EBool false)
  | [ a ] ->
    let e = infer_expr ctx a in
    unify e.loc e.ety TBool; e
  | a :: rest ->
    let e = infer_expr ctx a in
    unify e.loc e.ety TBool;
    mk l TBool (EIf (e, mk l TBool (EBool true), infer_or ctx l rest))

and infer_cond ctx l args =
  match args with
  | [] -> mk l TUnit ENil
  | [ _ ] -> type_error l "cond requires pairs"
  | Atom (_, Keyword "else") :: e :: _ -> infer_expr ctx e
  | c :: e :: rest -> infer_if ctx l c e (List (l, Atom (l, Symbol "cond") :: rest))

and infer_if_let ctx l b src body =
  let src_e = infer_expr ctx src in
  let payload = fresh_var () in
  unify src_e.loc src_e.ety (TOption payload);
  let _, _, inner = split_meta b in
  let name = match inner with Atom (_, Symbol s) -> s | _ -> type_error l "if-let binding must be a symbol" in
  let binder = fresh_binder name in
  binder.bty <- payload;
  let saved = ctx.env and saved_imp = ctx.implicits in
  ctx.env <- (name, { vscheme = mono payload; vkind = KLocal binder; vvariadic = false }) :: ctx.env;
  let then_f, else_f =
    match body with [ t ] -> (t, Atom (l, Nil)) | [ t; e ] -> (t, e) | _ -> type_error l "if-let takes then/else"
  in
  let te = infer_expr ctx then_f in
  ctx.env <- saved; ctx.implicits <- saved_imp;
  let ee = infer_expr ctx else_f in
  let ret, te, ee = join_branches l te ee in
  mk l ret (EMatchOpt (src_e, binder, te, ee))

(* match lowers to a nested if/let chain over existing forms — no new edesc.
   Clause forms:
     literal atom          -> guard `=` then body
     _ or symbol           -> (bind &) body   (irrefutable)
     [p1 .. pn]            -> guard count=n, then per-elem destructure
     {map pattern}         -> irrefutable destructure *)
and infer_match ctx l scrut clauses =
  let se = infer_expr ctx scrut in
  if List.length clauses mod 2 <> 0 then type_error l "match requires pattern/body pairs";
  let ret = fresh_var () in
  let lit_expr = function
    | Atom (al, a) ->
      (match a with
       | Int i -> Some (mk al TInt (EInt i))
       | Float x -> Some (mk al TFloat (EFloat x))
       | Bool b -> Some (mk al TBool (EBool b))
       | Char c -> Some (mk al TChar (EChar c))
       | Str s2 -> Some (mk al TString (EStr s2))
       | Keyword k -> Some (mk al TKeyword (EKeyword k))
       | Nil -> Some (mk al TUnit ENil)
       | _ -> None)
    | _ -> None
  in
  let scrut_any = match repr se.ety with TAny -> true | _ -> false in
  let eq_guard le =
    unify le.loc se.ety le.ety;
    let ce = mk l (TFun ([ se.ety; se.ety ], TBool)) (EBuiltin (if scrut_any then "dyn-eq" else "=")) in
    mk l TBool (ECall (ce, [ se; le ]))
  in
  let rec analyze = function
    | [] -> []
    | pat :: body_f :: rest ->
      let clause =
        (match lit_expr pat with
         | Some le ->
           let saved = ctx.env and saved_imp = ctx.implicits in
           let te = infer_expr ctx body_f in
           ctx.env <- saved; ctx.implicits <- saved_imp;
           (te, fun te' next -> mk l ret (EIf (eq_guard le, te', next)))
         | None ->
           (match pat with
            | Atom (_, Symbol "None") ->
              let dead = fresh_binder "_" in
              dead.bty <- fresh_var ();
              unify l se.ety (TOption dead.bty);
              let saved = ctx.env and saved_imp = ctx.implicits in
              let te = infer_expr ctx body_f in
              ctx.env <- saved; ctx.implicits <- saved_imp;
              (te, fun te' next -> mk l ret (EMatchOpt (se, dead, next, te')))
            | Atom (_, Symbol "_") ->
              let te = infer_expr ctx body_f in
              (te, fun te' _ -> te')
            | Atom (_, Symbol _) ->
              let saved = ctx.env and saved_imp = ctx.implicits in
              let pairs = bind_pattern ctx (atom_loc pat) pat se in
              let te = infer_expr ctx body_f in
              ctx.env <- saved; ctx.implicits <- saved_imp;
              (te, fun te' _ -> mk l ret (ELet (pairs, te')))
            | Map (ml, _) ->
              if scrut_any then (
                let dm = fresh_binder "mm" in
                dm.bty <- TMap (TAny, TAny);
                let saved = ctx.env and saved_imp = ctx.implicits in
                let pairs = bind_pattern ctx ml pat (mk ml (TMap (TAny, TAny)) (ELocal dm)) in
                let te = infer_expr ctx body_f in
                ctx.env <- saved; ctx.implicits <- saved_imp;
                (te, fun te' next -> mk l ret (EDynMap (se, dm, mk l ret (ELet (pairs, te')), next))))
              else (
                let saved = ctx.env and saved_imp = ctx.implicits in
                let pairs = bind_pattern ctx ml pat se in
                let te = infer_expr ctx body_f in
                ctx.env <- saved; ctx.implicits <- saved_imp;
                (te, fun te' _ -> mk l ret (ELet (pairs, te'))))
            | Vector (vl, items) ->
              let n = Array.length items in
              if scrut_any then (
                let dv = fresh_binder "mv" in
                dv.bty <- TVec TAny;
                let dv_e = mk vl (TVec TAny) (ELocal dv) in
                let pairs = bind_pattern ctx vl pat dv_e in
                let cnt = mk vl TInt (ECall (mk vl (TFun ([ TVec TAny ], TInt)) (EBuiltin "count"), [ dv_e ])) in
                let guard = mk vl TBool (ECall (mk vl (TFun ([ TInt; TInt ], TBool)) (EBuiltin "="), [ cnt; mk vl TInt (EInt n) ])) in
                let saved = ctx.env and saved_imp = ctx.implicits in
                let te = infer_expr ctx body_f in
                ctx.env <- saved; ctx.implicits <- saved_imp;
                (te, fun te' next -> mk l ret (EDynVec (se, dv, mk l ret (EIf (guard, mk l ret (ELet (pairs, te')), next)), next))))
              else (
                let el = fresh_var () in
                unify vl se.ety (TVec el);
                let cnt = mk vl TInt (ECall (mk vl (TFun ([ TVec el ], TInt)) (EBuiltin "count"), [ se ])) in
                let guard = mk vl TBool (ECall (mk vl (TFun ([ TInt; TInt ], TBool)) (EBuiltin "="), [ cnt; mk vl TInt (EInt n) ])) in
                let saved = ctx.env and saved_imp = ctx.implicits in
                let pairs = bind_pattern ctx vl pat se in
                let te = infer_expr ctx body_f in
                ctx.env <- saved; ctx.implicits <- saved_imp;
                (te, fun te' next -> mk l ret (EIf (guard, mk l ret (ELet (pairs, te')), next))))
            | List (_, Atom (_, Symbol "Some") :: [ p ]) ->
              let pl = atom_loc p in
              let nb = fresh_binder "ov" in
              nb.bty <- fresh_var ();
              unify pl se.ety (TOption nb.bty);
              let saved = ctx.env and saved_imp = ctx.implicits in
              let pairs = bind_pattern ctx pl p (mk pl nb.bty (ELocal nb)) in
              let te = infer_expr ctx body_f in
              ctx.env <- saved; ctx.implicits <- saved_imp;
              (te, fun te' next -> mk l ret (EMatchOpt (se, nb, mk l ret (ELet (pairs, te')), next)))
            | List (_, Atom (_, Symbol "quote") :: [ qf ]) ->
              (match lit_expr qf with
               | Some le ->
                 let saved = ctx.env and saved_imp = ctx.implicits in
                 let te = infer_expr ctx body_f in
                 ctx.env <- saved; ctx.implicits <- saved_imp;
                 (te, fun te' next -> mk l ret (EIf (eq_guard le, te', next)))
               | None -> type_error l "unsupported quoted match pattern")
            | _ -> type_error l "unsupported match pattern"))
      in
      clause :: analyze rest
    | _ -> type_error l "match requires pattern/body pairs"
  in
  let items = analyze clauses in
  let ret_any =
    List.exists (fun (te, _) -> match repr te.ety with TAny -> true | _ -> false) items
  in
  if ret_any then
    (match repr ret with TVar v -> v.link <- Some TAny | _ -> ())
  else
    List.iter (fun (te, _) -> unify te.loc ret te.ety) items;
  let join te =
    if ret_any && not (match repr te.ety with TAny -> true | _ -> false)
    then mk te.loc TAny (EBox te) else te
  in
  List.fold_right
    (fun (te, build) next -> build (join te) next)
    items
    (mk l ret (ECall (mk l (TFun ([ TUnit ], ret)) (EBuiltin "no-match"), [ mk l TUnit ENil ])))

and infer_fn_call ctx l rest =
  match rest with
  | Vector (_, params) :: body -> infer_fn ctx l None params body
  | Atom (_, Symbol name) :: Vector (_, params) :: body -> infer_fn ctx l (Some name) params body
  | _ -> type_error l "malformed fn"

and macro_lookup ctx s =
  let s' = Macro.unmark s in
  match String.index_opt s' '/' with
  | Some i ->
    let ns = String.sub s' 0 i and n = String.sub s' (i + 1) (String.length s' - i - 1) in
    let target = match List.assoc_opt ns ctx.modl.requires with Some f -> f | None -> ns in
    Macro.find_macro target n
  | None -> Macro.find_macro ctx.modl.mname s'

(* clone a type with fresh unification vars — used to match an implicit
   entry against a needed dictionary type without mutating the entry *)
and shallow_clone t =
  let tbl = Hashtbl.create 7 in
  let rec go t =
    match repr t with
    | TVar v ->
      (match Hashtbl.find_opt tbl v.id with
       | Some x -> x
       | None -> let x = fresh_var () in Hashtbl.replace tbl v.id x; x)
    | TImplicit t -> TImplicit (go t)
    | TList t -> TList (go t)
    | TVec t -> TVec (go t)
    | TSet t -> TSet (go t)
    | TAtom t -> TAtom (go t)
    | TOption t -> TOption (go t)
    | TMap (k, v) -> TMap (go k, go v)
    | TTuple ts -> TTuple (List.map go ts)
    | TCon (n, ts) -> TCon (n, List.map go ts)
    | TFun (ts, r) -> TFun (List.map go ts, go r)
    | t -> t
  in
  ignore tbl; go t

and implicit_resolve ctx l (needed : ty) : expr =
  let rec go = function
    | [] -> type_error l ("no implicit instance of type " ^ string_of_ty needed ^ " in scope")
    | (ety, thunk) :: rest ->
      let cand = shallow_clone ety in
      (match (try unify l cand needed; true with Type_error _ -> false) with
       | true -> thunk ()
       | false -> go rest)
  in
  go ctx.implicits

(* append resolved implicit dictionaries when the callee's trailing
   params are TImplicit and the call supplies only the explicit prefix *)
and fill_implicits ctx l (ce : expr) (arg_es : expr list) : expr list =
  match repr ce.ety with
  | TFun (ts, _) ->
    let nexplicit, implicits = Typ.split_implicit_params ts in
    if implicits <> [] && List.length arg_es = nexplicit then begin
      (* pin shared type vars with the explicit arg types first —
         otherwise resolution order, not the argument type, picks the
         dict (e.g. a later string->string instance would steal an
         int call by unifying `a` to string) *)
      let explicit_ts = List.filteri (fun i _ -> i < nexplicit) ts in
      List.iter2 (fun st ae -> unify l st ae.ety) explicit_ts arg_es;
      arg_es @ List.map (fun t -> implicit_resolve ctx l (dimp t)) implicits
    end
    else arg_es
  | _ -> arg_es

and infer_app ctx l callee args =
  match callee with
  | Atom (_, Symbol s) ->
    (match macro_lookup ctx s with
     | Some fn ->
       let expanded =
         (try Macro.expand fn args l
          with Macro.Macro_error (l2, msg) -> type_error l2 msg)
       in
       infer_expr ctx expanded
     | None -> infer_app_no_macro ctx l s args)
  | Atom (_, Keyword k) ->
    let arg_es = List.map (infer_expr ctx) args in
    infer_special ctx l "kw-get" (mk l (fresh_var ()) (EBuiltin "kw-get"))
      (mk l TKeyword (EKeyword k) :: arg_es)
  | _ ->
    let ce = infer_expr ctx callee in
    let arg_es = List.map (infer_expr ctx) args in
    let arg_es = fill_implicits ctx l ce arg_es in
    let ret = fresh_var () in
    unify ce.loc ce.ety (TFun (List.map (fun e -> e.ety) arg_es, ret));
    mk l ret (ECall (ce, arg_es))

and infer_app_no_macro ctx l s args =
  (* multi-arity dispatch: (f x y) where `f` was defined with arity 2
     resolves to the `f__a2` global. *)
  let s =
    let candidate = s ^ "__a" ^ string_of_int (List.length args) in
    let target =
      match String.index_opt s '/' with
      | Some i ->
        let ns = String.sub s 0 i and n = String.sub s (i + 1) (String.length s - i - 1) in
        let tgt = match List.assoc_opt ns ctx.modl.requires with Some f -> f | None -> ns in
        (match Hashtbl.find_opt ctx.globals tgt with
         | Some tbl when Hashtbl.mem tbl (n ^ "__a" ^ string_of_int (List.length args)) ->
           Some (String.sub s 0 (i + 1) ^ n ^ "__a" ^ string_of_int (List.length args))
         | _ -> None)
      | None ->
        (match Hashtbl.find_opt ctx.globals ctx.modl.mname with
         | Some tbl when Hashtbl.mem tbl candidate -> Some candidate
         | _ -> None)
    in
    match target with Some s2 -> s2 | None -> s
  in
  let arg_es = List.map (infer_expr ctx) args in
  let ce = infer_symbol ctx l s in
  (match ce.desc with
   | EBuiltin name when is_numeric_op name -> infer_numeric l name arg_es
   | EBuiltin name when is_cmp_op name -> infer_cmp l name arg_es
   | EBuiltin name when is_special_builtin name -> infer_special ctx l name ce arg_es
   | _ ->
     (* variadic callsite rewrite: if callee is a global fn declared
        variadic (a & rest param), wrap extra args into a list literal *)
     let arg_es = rewrite_variadic_call ctx s l arg_es in
     let arg_es = fill_implicits ctx l ce arg_es in
     let ret = fresh_var () in
     unify ce.loc ce.ety (TFun (List.map (fun e -> e.ety) arg_es, ret));
     mk l ret (ECall (ce, arg_es)))

and rewrite_variadic_call ctx s l arg_es =
  match String.index_opt s '/' with
  | Some i when i > 0 ->
    let ns = String.sub s 0 i and n = String.sub s (i + 1) (String.length s - i - 1) in
    let target = match List.assoc_opt ns ctx.modl.requires with Some full -> full | None -> ns in
    (match Hashtbl.find_opt ctx.globals target with
     | Some tbl ->
       (match Hashtbl.find_opt tbl n with
        | Some { gsch = sch; gvar = true; gexp = true } ->
          (match repr sch.sty with
           | TFun (ts, _) when List.length ts >= 1 ->
             let fixed = List.length ts - 1 in
             if List.length arg_es > fixed then
               let hd, tl =
                 List.fold_left (fun (a, b) e -> if List.length a < fixed then (a @ [ e ], b) else (a, b @ [ e ])) ([], []) arg_es
               in
               hd @ [ mk l (List.nth ts (List.length ts - 1)) (EListLit tl) ]
             else arg_es
           | _ -> arg_es)
        | _ -> arg_es)
     | None -> arg_es)
  | _ ->
    (match Hashtbl.find_opt ctx.globals ctx.modl.mname with
     | Some tbl ->
       (match Hashtbl.find_opt tbl s with
        | Some { gsch = sch; gvar = true; gexp = true } ->
          (match repr sch.sty with
           | TFun (ts, _) ->
             let fixed = List.length ts - 1 in
             if List.length arg_es > fixed then
               let hd, tl =
                 List.fold_left (fun (a, b) e -> if List.length a < fixed then (a @ [ e ], b) else (a, b @ [ e ])) ([], []) arg_es
               in
               let elem = match repr (List.nth ts (List.length ts - 1)) with TList x -> x | t -> t in
               hd @ [ mk l (TList elem) (EListLit tl) ]
             else arg_es
           | _ -> arg_es)
        | _ -> arg_es)
     | None -> arg_es)

and infer_numeric l name arg_es =
  let float_op = String.length name > 0 && name.[String.length name - 1] = '.' in
  match arg_es with
  | [ a; b ] ->
    let nty =
      if float_op then TFloat
      else if match repr a.ety with TFloat -> true | _ -> (match repr b.ety with TFloat -> true | _ -> false)
      then TFloat else TInt
    in
    unify a.loc a.ety nty; unify b.loc b.ety nty;
    let op = if float_op then name else (match repr nty with TFloat -> name ^ "." | _ -> name) in
    mk l nty (ECall (mk l (TFun ([ nty; nty ], nty)) (EBuiltin op), arg_es))
  | [ a ] when name = "-" || name = "-." ->
    let nty = if float_op then TFloat else (match repr a.ety with TFloat -> TFloat | _ -> TInt) in
    unify a.loc a.ety nty;
    mk l nty (ECall (mk l (TFun ([ nty ], nty)) (EBuiltin (if nty = TFloat then "neg." else "neg")), arg_es))
  | a :: b :: rest ->
    (* variadic arithmetic: (+ a b c) = (+ (+ a b) c) *)
    List.fold_left (fun acc e -> infer_numeric l name [ acc; e ]) (infer_numeric l name [ a; b ]) rest
  | _ -> type_error l (name ^ " expects at least 1 numeric argument")

and infer_cmp l name arg_es =
  match arg_es with
  | [ a; b ] ->
    let nty = if match repr a.ety with TFloat -> true | _ -> (match repr b.ety with TFloat -> true | _ -> false) then TFloat else TInt in
    unify a.loc a.ety nty; unify b.loc b.ety nty;
    let op = match repr nty with TFloat -> name ^ "." | _ -> name in
    mk l TBool (ECall (mk l (TFun ([ nty; nty ], TBool)) (EBuiltin op), arg_es))
  | a1 :: (_ :: _ as rest) ->
    (* variadic comparison: (< a b c) = (and (< a b) (< b c)); each argument
       is bound once so effects are not repeated *)
    let temps =
      List.map
        (fun e ->
          let b = fresh_binder "c" in
          b.bty <- e.ety;
          (b, e))
        (a1 :: rest)
    in
    let locals = List.map (fun (b, e) -> mk l e.ety (ELocal b)) temps in
    let cmps = List.map2 (fun x y -> infer_cmp l name [ x; y ]) locals (List.tl locals) in
    let chain = List.fold_right (fun c acc -> mk l TBool (EIf (c, acc, mk l TBool (EBool false)))) (List.tl cmps) (List.hd cmps) in
    mk l TBool (ELet (temps, chain))
  | _ -> type_error l (name ^ " expects at least 2 arguments")

(* Special builtins: typing depends on argument shapes. *)
and infer_special ctx l name ce arg_es =
  ignore ctx;
  let ty_args = List.map (fun e -> repr e.ety) arg_es in
  let with_coll c on_vec on_list on_set on_map on_other =
    match repr c with
    | TVec a -> on_vec a
    | TList a -> on_list a
    | TSet a -> on_set a
    | TMap (k, v) -> on_map k v
    | TString -> on_other TString
    | TVar _ ->
      let a = fresh_var () in
      unify l c (TList a);
      on_list a
    | t -> type_error l (Printf.sprintf "%s: unsupported collection type %s" name (string_of_ty t))
  in
  match name, ty_args with
  | "kw-get", [ TKeyword; m ] | "kw-get", [ TKeyword; m; _ ] ->
    let vt = fresh_var () in
    unify l m (TMap (TKeyword, vt));
    let ret = if List.length ty_args = 3 then (unify l vt (List.nth ty_args 2); vt) else TOption vt in
    mk l ret (ECall (ce, arg_es))
  | "first", [ c ] ->
    let ret = with_coll c (fun a -> TOption a) (fun a -> TOption a) (fun a -> TOption a) (fun k v -> TOption (TTuple [ k; v ])) (fun _ -> TOption TChar) in
    mk l ret (ECall (ce, arg_es))
  | "next", [ c ] ->
    let ret = with_coll c (fun a -> TOption (TList a)) (fun a -> TOption (TList a)) (fun a -> TOption (TList a)) (fun k v -> TOption (TList (TTuple [ k; v ]))) (fun _ -> TOption (TList TChar)) in
    mk l ret (ECall (ce, arg_es))
  | "rest", [ c ] ->
    let ret = with_coll c (fun a -> TList a) (fun a -> TList a) (fun a -> TList a) (fun k v -> TList (TTuple [ k; v ])) (fun _ -> TList TChar) in
    mk l ret (ECall (ce, arg_es))
  | "seq", [ c ] ->
    let ret = with_coll c (fun a -> TList a) (fun a -> TList a) (fun a -> TList a) (fun k v -> TList (TTuple [ k; v ])) (fun _ -> TList TChar) in
    mk l ret (ECall (ce, arg_es))
  | "count", [ c ] ->
    let _ = with_coll c (fun _ -> TInt) (fun _ -> TInt) (fun _ -> TInt) (fun _ _ -> TInt) (fun _ -> TInt) in
    mk l TInt (ECall (ce, arg_es))
  | "empty?", [ c ] ->
    let _ = with_coll c (fun _ -> TBool) (fun _ -> TBool) (fun _ -> TBool) (fun _ _ -> TBool) (fun _ -> TBool) in
    mk l TBool (ECall (ce, arg_es))
  | "contains?", [ c; x ] ->
    let ok = with_coll c (fun a -> unify l x a; true) (fun a -> unify l x a; true) (fun a -> unify l x a; true) (fun k _v -> unify l x k; true) (fun _ -> false) in
    if not ok then type_error l "contains? not supported on this type";
    mk l TBool (ECall (ce, arg_es))
  | "get", [ c; k ] | "get", [ c; k; _ ] ->
    let ret =
      with_coll c
        (fun a -> unify l k TInt; a)
        (fun a -> unify l k TInt; a)
        (fun a -> unify l k a; a)  (* sets: (get s x) -> x or nil; value type = elem *)
        (fun kk v -> unify l k kk; v)
        (fun _ -> type_error l "get not supported")
    in
    let ret = if List.length ty_args = 3 then (unify l ret (List.nth ty_args 2); ret) else TOption ret in
    mk l ret (ECall (ce, arg_es))
  | "nth", [ c; i ] | "nth", [ c; i; _ ] ->
    unify l i TInt;
    let ret =
      with_coll c (fun a -> a) (fun a -> a) (fun a -> a) (fun _ _ -> type_error l "nth not supported on map") (fun _ -> TChar)
    in
    let ret = if List.length ty_args = 3 then (unify l ret (List.nth ty_args 2); ret) else ret in
    mk l ret (ECall (ce, arg_es))
  | "conj", c :: xs ->
    let ret =
      with_coll c
        (fun a -> List.iter (unify l a) xs; TVec a)
        (fun a -> List.iter (unify l a) xs; TList a)
        (fun a -> List.iter (unify l a) xs; TSet a)
        (fun kk v -> List.iter (fun x -> unify l x (TTuple [ kk; v ])) xs; TMap (kk, v))
        (fun _ -> type_error l "conj not supported")
    in
    mk l ret (ECall (ce, arg_es))
  | "assoc", c :: rest ->
    let ret =
      with_coll c
        (fun a ->
          (match rest with
           | [ i; x ] -> unify l i TInt; unify l x a
           | _ -> type_error l "assoc on vector: (assoc v i x)");
          TVec a)
        (fun _ -> type_error l "assoc not supported on list")
        (fun _ -> type_error l "assoc not supported on set")
        (fun kk v ->
          let rec pairs = function
            | [] -> ()
            | [ _ ] -> type_error l "assoc requires k/v pairs"
            | k2 :: v2 :: r -> unify l k2 kk; unify l v2 v; pairs r
          in
          pairs rest;
          TMap (kk, v))
        (fun _ -> type_error l "assoc not supported")
    in
    mk l ret (ECall (ce, arg_es))
  | "dissoc", m :: ks ->
    (match repr m with
     | TMap (kk, v) -> List.iter (fun k -> unify l k kk) ks; mk l (TMap (kk, v)) (ECall (ce, arg_es))
     | TVar _ -> let kk = fresh_var () and v = fresh_var () in unify l m (TMap (kk, v)); mk l (TMap (kk, v)) (ECall (ce, arg_es))
     | _ -> type_error l "dissoc expects a map")
  | "map", [ f; c ] ->
    let a = fresh_var () and b = fresh_var () in
    unify l f (TFun ([ a ], b));
    let ret = with_coll c (fun x -> unify l a x; TVec b) (fun x -> unify l a x; TList b) (fun x -> unify l a x; TVec b) (fun k v -> unify l a (TTuple [ k; v ]); TList b) (fun _ -> TList b) in
    mk l ret (ECall (ce, arg_es))
  | "filter", [ f; c ] ->
    let a = fresh_var () in
    unify l f (TFun ([ a ], TBool));
    let ret = with_coll c (fun x -> unify l a x; TVec a) (fun x -> unify l a x; TList a) (fun x -> unify l a x; TSet a) (fun k v -> unify l a (TTuple [ k; v ]); TMap (k, v)) (fun _ -> TList a) in
    mk l ret (ECall (ce, arg_es))
  | "reduce", [ f; init; c ] ->
    let a = fresh_var () in
    let _ = with_coll c (fun x -> unify l a x) (fun x -> unify l a x) (fun x -> unify l a x) (fun k v -> unify l a (TTuple [ k; v ])) (fun _ -> unify l a TChar) in
    unify l f (TFun ([ init; a ], init));
    mk l init (ECall (ce, arg_es))
  | "mapv", [ f; c ] ->
    let a = fresh_var () and b = fresh_var () in
    unify l f (TFun ([ a ], b));
    let _ = with_coll c (fun x -> unify l a x) (fun x -> unify l a x) (fun x -> unify l a x) (fun k v -> unify l a (TTuple [ k; v ])) (fun _ -> unify l a TChar) in
    mk l (TVec b) (ECall (ce, arg_es))
  | "filterv", [ f; c ] ->
    let a = fresh_var () in
    unify l f (TFun ([ a ], TBool));
    let _ = with_coll c (fun x -> unify l a x) (fun x -> unify l a x) (fun x -> unify l a x) (fun k v -> unify l a (TTuple [ k; v ])) (fun _ -> unify l a TChar) in
    mk l (TVec a) (ECall (ce, arg_es))
  | "vec", [ c ] ->
    let a = with_coll c (fun x -> x) (fun x -> x) (fun x -> x) (fun _ _ -> type_error l "vec on map") (fun _ -> TChar) in
    mk l (TVec a) (ECall (ce, arg_es))
  | "set", [ c ] ->
    let a = with_coll c (fun x -> x) (fun x -> x) (fun x -> x) (fun _ _ -> type_error l "set on map") (fun _ -> TChar) in
    mk l (TSet a) (ECall (ce, arg_es))
  | "into", [ dst; src ] ->
    let a = fresh_var () in
    let ret =
      match repr dst with
      | TVec x -> unify l a x; TVec a
      | TList x -> unify l a x; TList a
      | TSet x -> unify l a x; TSet a
      | TVar _ -> unify l dst (TVec a); TVec a
      | _ -> type_error l "into expects a collection destination"
    in
    let _ = with_coll src (fun x -> unify l a x) (fun x -> unify l a x) (fun x -> unify l a x) (fun k v -> unify l a (TTuple [ k; v ])) (fun _ -> unify l a TChar) in
    mk l ret (ECall (ce, arg_es))
  | "take", [ n; c ] | "drop", [ n; c ] ->
    unify l n TInt;
    let _ = with_coll c (fun _ -> ()) (fun _ -> ()) (fun _ -> ()) (fun _ _ -> ()) (fun _ -> ()) in
    mk l c (ECall (ce, arg_es))
  | "apply", [ f; xs ] ->
    let ret = fresh_var () in
    (match repr f with
     | TFun (ts, r) ->
       (match List.rev ts with
        | last :: _ -> unify l xs (TList last); unify l ret r
        | [] -> type_error l "apply: arity mismatch");
       mk l ret (ECall (ce, arg_es))
     | _ -> type_error l "apply: not a function")
  | "range", [ _ ] | "range", [ _; _ ] ->
    List.iter (fun t -> unify l t TInt) ty_args;
    mk l (TList TInt) (ECall (ce, arg_es))
  | "concat", [] | "concat", _ :: _ ->
    let a = fresh_var () in
    List.iter (fun t -> unify l t (TList a)) ty_args;
    mk l (TList a) (ECall (ce, arg_es))
  | "merge", _ :: _ ->
    let kk = fresh_var () and v = fresh_var () in
    List.iter (fun t -> unify l t (TMap (kk, v))) ty_args;
    mk l (TMap (kk, v)) (ECall (ce, arg_es))
  | "list", _ ->
    let a = fresh_var () in
    List.iter (fun t -> unify l t a) ty_args;
    mk l (TList a) (EListLit arg_es)
  | "vector", _ ->
    let a = fresh_var () in
    List.iter (fun t -> unify l t a) ty_args;
    mk l (TVec a) (EVecLit arg_es)
  | "hash-map", _ ->
    let kes =
      let rec go acc = function
        | [] -> List.rev acc
        | e1 :: e2 :: r -> go ((e1, e2) :: acc) r
        | _ -> type_error l "hash-map requires even forms"
      in
      go [] arg_es
    in
    let kk = fresh_var () and v = fresh_var () in
    List.iter (fun (k2, v2) -> unify k2.loc kk k2.ety; unify v2.loc v v2.ety) kes;
    mk l (TMap (kk, v)) (EMapLit kes)
  | "hash-set", _ ->
    let a = fresh_var () in
    List.iter (fun t -> unify l t a) ty_args;
    mk l (TSet a) (ESetLit arg_es)
  | "select-keys", [ m; ks ] ->
    let kk = fresh_var () and v = fresh_var () in
    unify l m (TMap (kk, v));
    (match repr ks with
     | TList k2 | TVec k2 | TSet k2 -> unify l kk k2
     | TVar _ -> unify l ks (TList kk)
     | _ -> type_error l "select-keys: key list must be a seqable collection");
    mk l (TMap (kk, v)) (ECall (ce, arg_es))
  | "update", [ m; k; f ] ->
    let kk = fresh_var () and v = fresh_var () in
    unify l m (TMap (kk, v));
    unify l k kk;
    unify l f (TFun ([ v ], v));
    mk l (TMap (kk, v)) (ECall (ce, arg_es))
  | "get-in", [ m; ks ] ->
    unify l m (TMap (TKeyword, TAny));
    (match repr ks with
     | TList k2 | TVec k2 -> unify l TKeyword k2
     | TVar _ -> unify l ks (TList TKeyword)
     | _ -> type_error l "get-in: path must be a list/vector of keywords");
    mk l (TOption TAny) (ECall (ce, arg_es))
  | "assoc-in", [ m; ks; v2 ] ->
    unify l m (TMap (TKeyword, TAny));
    (match repr ks with
     | TList k2 | TVec k2 -> unify l TKeyword k2
     | TVar _ -> unify l ks (TList TKeyword)
     | _ -> type_error l "assoc-in: path must be a list/vector of keywords");
    unify l v2 TAny;
    mk l (TMap (TKeyword, TAny)) (ECall (ce, arg_es))
  | "comp", [ f; g ] ->
    let x = fresh_var () and a = fresh_var () and b = fresh_var () in
    unify l g (TFun ([ x ], a));
    unify l f (TFun ([ a ], b));
    mk l (TFun ([ x ], b)) (ECall (ce, arg_es))
  | "juxt", [ f; g ] ->
    let a = fresh_var () and b = fresh_var () and c = fresh_var () in
    unify l f (TFun ([ a ], b));
    unify l g (TFun ([ a ], c));
    mk l (TFun ([ a ], TTuple [ b; c ])) (ECall (ce, arg_es))
  | "partial", f :: fixed ->
    let x = fresh_var () and r = fresh_var () in
    unify l f (TFun (fixed @ [ x ], r));
    mk l (TFun ([ x ], r)) (ECall (ce, arg_es))
  | "mapcat", [ f; c ] ->
    let a = fresh_var () and b = fresh_var () in
    unify l f (TFun ([ a ], TList b));
    let _ = with_coll c (fun x -> unify l a x) (fun x -> unify l a x) (fun x -> unify l a x) (fun k v -> unify l a (TTuple [ k; v ])) (fun _ -> unify l a TChar) in
    mk l (TList b) (ECall (ce, arg_es))
  | "interpose", [ sep; c ] ->
    let a = fresh_var () in
    let _ = with_coll c (fun x -> unify l a x; unify l sep a) (fun x -> unify l a x; unify l sep a) (fun x -> unify l a x; unify l sep a) (fun k v -> unify l a (TTuple [ k; v ]); unify l sep a) (fun _ -> unify l a TChar; unify l sep a) in
    mk l (TList a) (ECall (ce, arg_es))
  | "reverse", [ c ] ->
    (match repr c with TVec _ | TList _ -> () | TVar _ -> unify l c (TList (fresh_var ())) | _ -> type_error l "reverse expects a list/vector");
    mk l c (ECall (ce, arg_es))
  | "distinct", [ c ] ->
    let ret = with_coll c (fun a -> TList a) (fun a -> TList a) (fun a -> TList a) (fun _ _ -> type_error l "distinct on map") (fun _ -> TList TChar) in
    mk l ret (ECall (ce, arg_es))
  | "second", [ c ] ->
    let ret = with_coll c (fun a -> TOption a) (fun a -> TOption a) (fun a -> TOption a) (fun _ _ -> TOption TAny) (fun _ -> TOption TChar) in
    mk l ret (ECall (ce, arg_es))
  | "last", [ c ] ->
    let ret = with_coll c (fun a -> TOption a) (fun a -> TOption a) (fun a -> TOption a) (fun _ _ -> TOption TAny) (fun _ -> TOption TChar) in
    mk l ret (ECall (ce, arg_es))
  | "butlast", [ c ] ->
    let ret = with_coll c (fun a -> TList a) (fun a -> TList a) (fun a -> TList a) (fun _ _ -> type_error l "butlast on map") (fun _ -> TList TChar) in
    mk l ret (ECall (ce, arg_es))
  | "min", [ a; b ] | "max", [ a; b ] ->
    let nty = if match repr a with TFloat -> true | _ -> (match repr b with TFloat -> true | _ -> false) then TFloat else TInt in
    unify l a nty; unify l b nty;
    mk l nty (ECall (ce, arg_es))
  | "every?", [ f; c ] | "some", [ f; c ] ->
    let a = fresh_var () in
    unify l f (TFun ([ a ], TBool));
    let _ = with_coll c (fun x -> unify l a x) (fun x -> unify l a x) (fun x -> unify l a x) (fun k v -> unify l a (TTuple [ k; v ])) (fun _ -> unify l a TChar) in
    mk l TBool (ECall (ce, arg_es))
  | "take-while", [ f; c ] | "drop-while", [ f; c ] ->
    let a = fresh_var () in
    unify l f (TFun ([ a ], TBool));
    (match repr c with
     | TList x -> unify l a x
     | TVar _ -> unify l c (TList a)
     | _ -> type_error l (name ^ " expects a list"));
    mk l (TList a) (ECall (ce, arg_es))
  | "zipmap", [ ks; vs ] ->
    let kk = fresh_var () and v = fresh_var () in
    unify l ks (TList kk); unify l vs (TList v);
    mk l (TMap (kk, v)) (ECall (ce, arg_es))
  | "sort", [ c ] ->
    let ret = with_coll c (fun a -> TList a) (fun a -> TList a) (fun a -> TList a) (fun _ _ -> type_error l "sort on map") (fun _ -> TList TChar) in
    mk l ret (ECall (ce, arg_es))
  | "sort", [ cmp; c ] ->
    let a = fresh_var () in
    unify l cmp (TFun ([ a; a ], TInt));
    unify l c (TList a);
    mk l (TList a) (ECall (ce, arg_es))
  | "sort-by", [ f; c ] ->
    let a = fresh_var () and k = fresh_var () in
    unify l f (TFun ([ a ], k));
    let _ = with_coll c (fun x -> unify l a x) (fun x -> unify l a x) (fun x -> unify l a x) (fun _ _ -> type_error l "sort-by on map") (fun _ -> unify l a TChar) in
    mk l (TList a) (ECall (ce, arg_es))
  | "group-by", [ f; c ] ->
    let a = fresh_var () and k = fresh_var () in
    unify l f (TFun ([ a ], k));
    let _ = with_coll c (fun x -> unify l a x) (fun x -> unify l a x) (fun x -> unify l a x) (fun _ _ -> type_error l "group-by on map") (fun _ -> unify l a TChar) in
    mk l (TMap (k, TList a)) (ECall (ce, arg_es))
  | "frequencies", [ c ] ->
    let ret = with_coll c (fun a -> TMap (a, TInt)) (fun a -> TMap (a, TInt)) (fun a -> TMap (a, TInt)) (fun _ _ -> type_error l "frequencies on map") (fun _ -> TMap (TChar, TInt)) in
    mk l ret (ECall (ce, arg_es))
  | ("str" | "println" | "print" | "pr-str"), _ ->
    (* a bare binder (ELocal) whose type is still free gets marked `any`:
       nothing else will constrain it, and the dyn-at-boundary contract
       lets call sites box literals for it. Non-binder args (calls, lets)
       keep their inferred type — unifying a free application-result var
       with `any` would poison it before a signature can pin it down. *)
    List.iter
      (fun e ->
        (match e.desc with
         | ELocal b -> (match repr b.bty with TVar _ -> unify l b.bty TAny | _ -> ())
         | _ -> ()))
      arg_es;
    let ret = if name = "str" || name = "pr-str" then TString else TUnit in
    mk l ret (ECall (ce, arg_es))
  | "swap!", [ a; f ] ->
    let at = fresh_var () in
    unify l a (TAtom at); unify l f (TFun ([ at ], at));
    mk l at (ECall (ce, arg_es))
  | _ -> type_error l (Printf.sprintf "%s: bad arguments (%d given)" name (List.length ty_args))
