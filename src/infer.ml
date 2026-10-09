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

(* ns -> (name -> (scheme * variadic)) *)
type globals = (string, (string, scheme * bool) Hashtbl.t) Hashtbl.t

type ctx = {
  modl : modl;
  globals : globals;
  mutable env : env;
}

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
  Buffer.contents b

let ocaml_mod_of_ns ns =
  String.split_on_char '.' ns
  |> List.map (fun seg ->
         let seg = String.map (fun c -> if c = '-' then '_' else c) seg in
         if String.length seg > 0 then String.capitalize_ascii seg else seg)
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
         (* type variable; same name maps to same rigid var *)
         (match Hashtbl.find_opt tbl v with
          | Some t -> t
          | None -> let t = fresh_rigid () in Hashtbl.replace tbl v t; t)
       | v -> TCon (v, []))
    | List (_, [ Atom (_, Symbol "vec"); t ]) -> TVec (go t)
    | List (_, [ Atom (_, Symbol "list"); t ]) -> TList (go t)
    | List (_, [ Atom (_, Symbol "set"); t ]) -> TSet (go t)
    | List (_, [ Atom (_, Symbol "atom"); t ]) -> TAtom (go t)
    | List (_, [ Atom (_, Symbol "option"); t ]) -> TOption (go t)
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
  reg "constantly" (fun () -> let a = v () and b = v () in f [ a; b ] a);
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
  ()

let is_numeric_op = function "+" | "-" | "*" | "/" | "+." | "-." | "*." | "/." -> true | _ -> false
let is_cmp_op = function "<" | "<=" | ">" | ">=" -> true | _ -> false

let is_special_builtin = function
  | "first" | "next" | "rest" | "seq" | "get" | "nth" | "conj" | "assoc"
  | "dissoc" | "map" | "filter" | "reduce" | "mapv" | "filterv" | "into"
  | "apply" | "kw-get" | "contains?" | "empty?" | "count" | "range"
  | "concat" | "merge" | "list" | "vector" | "hash-map" | "hash-set"
  | "str" | "println" | "print" | "pr-str" | "swap!" -> true
  | _ -> false

(* ---------- inference ---------- *)

let instantiate_builtin_ty name = Hashtbl.find builtin_table name ()

let last xs = List.nth xs (List.length xs - 1)

let rec infer_program (forms : form list) (mname : string) (path : string) (globals : globals) : modl =
  let m = { mname; ocaml_name = ocaml_mod_of_ns mname; mpath = path; requires = []; defs = []; effects = [] } in
  let ctx = { modl = m; globals; env = [] } in
  List.iter (infer_top ctx) forms;
  m

and infer_top ctx f =
  match f with
  | List (l, Atom (_, Symbol "ns") :: rest) -> parse_ns ctx l rest
  | List (_, Atom (_, Symbol "def") :: _) -> ctx.modl.defs <- ctx.modl.defs @ [ infer_def ctx f ]
  | List (_, Atom (_, Symbol "defn") :: _) -> ctx.modl.defs <- ctx.modl.defs @ [ infer_defn ctx f ]
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
              | Vector (_, [| Atom (_, Symbol ns) |]) ->
                ctx.modl.requires <- ctx.modl.requires @ [ (ns, ns) ]
              | Vector (_, [| Atom (_, Symbol ns); Atom (_, Keyword "as"); Atom (_, Symbol alias) |]) ->
                ctx.modl.requires <- ctx.modl.requires @ [ (alias, ns) ]
              | _ -> type_error l "unsupported :require spec (want [ns] or [ns :as alias])")
            specs
        | _ -> type_error l "unsupported ns clause (only :require is supported)")
      clauses
  | _ -> type_error l "malformed ns form"

and infer_def ctx f =
  let l = atom_loc f in
  match f with
  | List (_, _ :: namef :: rest) ->
    let name, mode_hint, ty_ann, rest =
      match namef with
      | Atom (_, Symbol n) -> (n, None, None, rest)
      | Meta (_, m, Atom (_, Symbol n)) ->
        let mh, ta, _ = split_meta (Meta (no_loc, m, Atom (no_loc, Symbol n))) in
        (n, mh, ta, rest)
      | _ -> type_error l "def requires a name"
    in
    let e = match rest with
      | [ e ] -> e
      | [ Atom (_, Str _); e ] -> e  (* docstring *)
      | _ -> type_error l "malformed def"
    in
    let texpr = infer_expr ctx e in
    (match ty_ann with Some t -> unify texpr.loc texpr.ety t | None -> ());
    let sch = generalize [] texpr.ety in
    let top = { tname = name; tloc = l; tsch = sch; texpr; tis_fn = false; tmode = (match mode_hint with Some m -> m | None -> Shared) } in
    register_global ctx name sch false;
    top
  | _ -> type_error l "malformed def"

and infer_defn ctx f =
  let l = atom_loc f in
  match f with
  | List (_, _ :: namef :: rest) ->
    let name, mode_hint, ty_ann =
      match namef with
      | Atom (_, Symbol n) -> (n, None, None)
      | Meta (_, m, Atom (_, Symbol n)) ->
        let mh, ta, _ = split_meta (Meta (no_loc, m, Atom (no_loc, Symbol n))) in
        (n, mh, ta)
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
       let saved = ctx.env in
       let self_v = fresh_var () in
       ctx.env <- (name, { vscheme = mono self_v; vkind = KGlobal (ctx.modl.ocaml_name, munge name); vvariadic = false }) :: ctx.env;
       let fe = infer_fn ctx l (Some name) params body in
       ctx.env <- saved;
       unify l self_v fe.ety;
       (match ty_ann with Some t -> unify l fe.ety t | None -> ());
       let sch = generalize [] fe.ety in
       let variadic = match fe.desc with EFun fn -> fn.variadic <> None | _ -> false in
       let top = { tname = name; tloc = l; tsch = sch; texpr = fe; tis_fn = true; tmode = (match mode_hint with Some m -> m | None -> Shared) } in
       register_global ctx name sch variadic;
       top
     | _ -> type_error l "defn requires a single arity [params] body (multi-arity is v1)")
  | _ -> type_error l "malformed defn"

and register_global ctx name sch variadic =
  let tbl =
    match Hashtbl.find_opt ctx.globals ctx.modl.mname with
    | Some t -> t
    | None -> let t = Hashtbl.create 17 in Hashtbl.replace ctx.globals ctx.modl.mname t; t
  in
  Hashtbl.replace tbl name (sch, variadic)

and infer_fn ctx l name params body : expr =
  let items = Array.to_list params in
  let rec split acc = function
    | [] -> (List.rev acc, None)
    | Atom (_, Symbol "&") :: Atom (_, Symbol r) :: [] -> (List.rev acc, Some r)
    | Atom (_, Symbol "&") :: [ Meta (_, _, Atom (_, Symbol r)) ] -> (List.rev acc, Some r)
    | x :: xs -> split (x :: acc) xs
  in
  let ps, variadic = split [] items in
  let mk_param f =
    let _, ta, inner = split_meta f in
    match inner with
    | Atom (_, Symbol s) ->
      let b = fresh_binder s in
      b.bty <- (match ta with Some t -> t | None -> fresh_var ());
      (s, b)
    | _ -> type_error l "fn params must be symbols (destructuring is v1)"
  in
  let binders = List.map mk_param ps in
  let vbinder =
    match variadic with
    | None -> None
    | Some s -> let b = fresh_binder s in b.bty <- TList (fresh_var ()); Some (s, b)
  in
  let saved = ctx.env in
  List.iter (fun (s, b) -> ctx.env <- (s, { vscheme = mono b.bty; vkind = KLocal b; vvariadic = false }) :: ctx.env) binders;
  (match vbinder with
   | Some (s, b) -> ctx.env <- (s, { vscheme = mono b.bty; vkind = KLocal b; vvariadic = false }) :: ctx.env
   | None -> ());
  let body_es = List.map (infer_expr ctx) body in
  ctx.env <- saved;
  let body_e =
    match body_es with
    | [] -> mk l TUnit ENil
    | [ e ] -> e
    | es -> mk l (last es).ety (EDo es)
  in
  let ptys = List.map (fun (_, b) -> b.bty) binders in
  let fty =
    match vbinder with
    | Some (_, vb) -> TFun (ptys @ [ vb.bty ], body_e.ety)
    | None -> TFun (ptys, body_e.ety)
  in
  mk l fty
    (EFun { fname = name; params = List.map snd binders; variadic = (match vbinder with Some (_, b) -> Some b | None -> None); body = body_e; fescapes = false })

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
     | Symbol s -> infer_symbol ctx l s)
  | Vector (l, items) ->
    let es = List.map (infer_expr ctx) (Array.to_list items) in
    let elem = fresh_var () in
    let het =
      try List.iter (fun e -> unify e.loc elem e.ety) es; false
      with Type_error _ -> true
    in
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
    mk l (TMap ((if het_k then TAny else kt), (if het_v then TAny else vt))) (EMapLit kes)
  | Set (l, items) ->
    let es = List.map (infer_expr ctx) items in
    let elem = fresh_var () in
    let het =
      try List.iter (fun e -> unify e.loc elem e.ety) es; false
      with Type_error _ -> true
    in
    mk l (TSet (if het then TAny else elem)) (ESetLit es)
  | Quote (l, qf) -> quote_to_expr l qf
  | Meta (l, _, inner) ->
    let e = infer_expr ctx inner in
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
         | Some (sch, _) -> mk l (instantiate sch) (EGlobal (ocaml_mod_of_ns target, munge n, s))
         | None -> type_error l (Printf.sprintf "unresolved symbol %s (no such var in %s)" s target))
      | None -> type_error l (Printf.sprintf "unresolved symbol %s (module %s not loaded)" s target))
  | _ ->
    (match lookup ctx.env s with
     | Some { vscheme = sch; vkind = KGlobal (m, n); _ } -> mk l (instantiate sch) (EGlobal (m, n, s))
     | Some { vkind = KBuiltin; _ } -> mk l (instantiate_builtin_ty s) (EBuiltin s)
     | _ ->
       (match Hashtbl.find_opt ctx.globals ctx.modl.mname with
        | Some tbl when Hashtbl.mem tbl s ->
          let sch, _ = Hashtbl.find tbl s in
          mk l (instantiate sch) (EGlobal (ctx.modl.ocaml_name, munge s, s))
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

and infer_if ctx l c t e =
  let ce = infer_expr ctx c in
  unify ce.loc ce.ety TBool;
  let te = infer_expr ctx t and ee = infer_expr ctx e in
  unify ee.loc te.ety ee.ety;
  mk l te.ety (EIf (ce, te, ee))

and infer_do ctx l body =
  let es = List.map (infer_expr ctx) body in
  match es with [] -> mk l TUnit ENil | _ -> mk l (last es).ety (EDo es)

and infer_let ctx l binds body =
  let items = Array.to_list binds in
  let saved = ctx.env in
  let rec go acc = function
    | [] -> List.rev acc
    | bform :: eform :: rest ->
      let _, ta, inner = split_meta bform in
      (match inner with
       | Atom (_, Symbol s) ->
         let e = infer_expr ctx eform in
         (match ta with Some t -> unify e.loc e.ety t | None -> ());
         let b = fresh_binder s in
         b.bty <- e.ety;
         ctx.env <- (s, { vscheme = mono b.bty; vkind = KLocal b; vvariadic = false }) :: ctx.env;
         go ((b, e) :: acc) rest
       | _ -> type_error l "let bindings must be symbols (destructuring is v1)")
    | _ -> type_error l "let requires an even number of binding forms"
  in
  let pairs = go [] items in
  let body_es = List.map (infer_expr ctx) body in
  ctx.env <- saved;
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
  let saved = ctx.env in
  ctx.env <- (name, { vscheme = mono payload; vkind = KLocal binder; vvariadic = false }) :: ctx.env;
  let then_f, else_f =
    match body with [ t ] -> (t, Atom (l, Nil)) | [ t; e ] -> (t, e) | _ -> type_error l "if-let takes then/else"
  in
  let te = infer_expr ctx then_f in
  ctx.env <- saved;
  let ee = infer_expr ctx else_f in
  unify ee.loc te.ety ee.ety;
  mk l te.ety (EMatchOpt (src_e, binder, te, ee))

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
    let ret = fresh_var () in
    unify ce.loc ce.ety (TFun (List.map (fun e -> e.ety) arg_es, ret));
    mk l ret (ECall (ce, arg_es))

and infer_app_no_macro ctx l s args =
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
        | Some (sch, true) ->
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
        | Some (sch, true) ->
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
  | _ -> type_error l (name ^ " expects 1 or 2 numeric arguments")

and infer_cmp l name arg_es =
  match arg_es with
  | [ a; b ] ->
    let nty = if match repr a.ety with TFloat -> true | _ -> (match repr b.ety with TFloat -> true | _ -> false) then TFloat else TInt in
    unify a.loc a.ety nty; unify b.loc b.ety nty;
    let op = match repr nty with TFloat -> name ^ "." | _ -> name in
    mk l TBool (ECall (mk l (TFun ([ nty; nty ], TBool)) (EBuiltin op), arg_es))
  | _ -> type_error l (name ^ " expects 2 arguments")

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
  | "into", [ dst; src ] ->
    let a = fresh_var () in
    unify l dst (TVec a);
    let _ = with_coll src (fun x -> unify l a x) (fun x -> unify l a x) (fun x -> unify l a x) (fun k v -> unify l a (TTuple [ k; v ])) (fun _ -> unify l a TChar) in
    mk l (TVec a) (ECall (ce, arg_es))
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
  | ("str" | "println" | "print" | "pr-str"), _ ->
    let ret = if name = "str" || name = "pr-str" then TString else TUnit in
    mk l ret (ECall (ce, arg_es))
  | "swap!", [ a; f ] ->
    let at = fresh_var () in
    unify l a (TAtom at); unify l f (TFun ([ at ], at));
    mk l at (ECall (ce, arg_es))
  | _ -> type_error l (Printf.sprintf "%s: bad arguments (%d given)" name (List.length ty_args))
