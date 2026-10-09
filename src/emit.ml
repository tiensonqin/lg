(* OCaml emitter: typed AST -> OCaml source text.
   Runtime targets: Clj_core.{Vec,Map,Set,List,Atom,Keyword,Symbol} and the
   embedded Lg_rt prelude (printers + helpers). *)

open Ast
open Typ
open Infer

(* TImplicit is invisible downstream: binders, args and printers see
   the wrapped dictionary type *)
let repr t = Typ.dimp t

let uid_ctr = ref 0
let fresh_uid () = incr uid_ctr; !uid_ctr

(* when set, emit OxCaml mode annotations: stack_ on non-escaping
   allocations, local_ on non-escaping params/bindings, unique_ on
   once-used owned bindings *)
let oxcaml = ref false

let sanitize s = munge s

let buf_add = Buffer.add_string

let ocaml_str s = Printf.sprintf "%S" s
let ocaml_char = function
  | '\n' -> "'\\n'" | '\t' -> "'\\t'" | '\r' -> "'\\r'" | '\b' -> "'\\b'"
  | '\'' -> "'\\''" | '\\' -> "'\\\\'" | c -> Printf.sprintf "'%c'" c

let ocaml_float x =
  let s = Printf.sprintf "%g" x in
  if String.contains s '.' || String.contains s 'e' || String.contains s 'n' then s else s ^ "."

(* namespaced keyword/symbol literal: "ns/name" -> ~ns *)
let kw_expr k =
  match String.index_opt k '/' with
  | Some i when i > 0 && i < String.length k - 1 ->
    Printf.sprintf "(Clj_core.Keyword.keyword ~ns:%S %S)" (String.sub k 0 i) (String.sub k (i + 1) (String.length k - i - 1))
  | _ -> Printf.sprintf "(Clj_core.Keyword.keyword %S)" k

let sym_expr s =
  match String.index_opt s '/' with
  | Some i when i > 0 && i < String.length s - 1 ->
    Printf.sprintf "(Clj_core.Symbol.symbol ~ns:%S %S)" (String.sub s 0 i) (String.sub s (i + 1) (String.length s - i - 1))
  | _ -> Printf.sprintf "(Clj_core.Symbol.symbol %S)" s

(* current enclosing module — same-module globals emit unqualified *)
let cur_mod = ref ""

let rec emit_expr (b : Buffer.t) (e : expr) : unit =
  match e.desc with
  | EInt i -> buf_add b (if i < 0 then "(" ^ string_of_int i ^ ")" else string_of_int i)
  | EFloat x -> buf_add b (if x < 0. then "(" ^ ocaml_float x ^ ")" else ocaml_float x)
  | EBool x -> buf_add b (string_of_bool x)
  | EChar c -> buf_add b (ocaml_char c)
  | EStr s -> buf_add b (ocaml_str s)
  | EKeyword k -> buf_add b (kw_expr k)
  | ESymbol s -> buf_add b (sym_expr s)
  | ENil -> buf_add b "()"
  | ELocal bd -> buf_add b (sanitize bd.bname ^ "__" ^ string_of_int bd.bid)
  | EGlobal (m, n, _) -> if m = !cur_mod then buf_add b n else buf_add b (m ^ "." ^ n)
  | EBuiltin name -> buf_add b (emit_builtin_value name)
  | EFun fn ->
    (match fn.Ast.fself with
     | Some sb ->
       buf_add b ("(let rec " ^ sanitize sb.bname ^ "__" ^ string_of_int sb.bid ^ " = ")
     | None -> ());
    buf_add b "(fun ";
    let pesc =
      if !oxcaml then
        (try List.map (fun p -> not (Modes.is_escaping_use p fn.Ast.body || Modes.occurs_in_result p fn.Ast.body)) fn.params
         with _ -> List.map (fun _ -> false) fn.params)
      else []
    in
    List.iteri
      (fun i p ->
        if i < List.length pesc && List.nth pesc i then buf_add b "(local_ ";
        buf_add b (sanitize p.bname ^ "__" ^ string_of_int p.bid);
        if i < List.length pesc && List.nth pesc i then buf_add b ")" else buf_add b " ")
      fn.params;
    (match fn.variadic with Some p -> buf_add b (sanitize p.bname ^ "__" ^ string_of_int p.bid ^ " ") | None -> ());
    buf_add b "-> ";
    (match repr e.ety with
     | TFun (_, r) when is_any r && not (is_any fn.body.ety) ->
       buf_add b ("(Lg_rt." ^ dyn_ctor fn.body.ety ^ " ("); emit_expr b fn.body; buf_add b "))"
     | _ -> emit_expr b fn.body);
    buf_add b ")";
    (match fn.Ast.fself with
     | Some sb -> buf_add b (" in " ^ sanitize sb.bname ^ "__" ^ string_of_int sb.bid ^ ")")
     | None -> ())
  | ECall (ce, args) -> emit_call b e.ety ce args
  | EIf (c, t, x) ->
    if is_any c.ety then buf_add b "(if (Lg_rt.dyn_truthy " else buf_add b "(if ";
    emit_expr b c;
    if is_any c.ety then buf_add b ")" else ();
    buf_add b " then ";
    emit_expr b t; buf_add b " else "; emit_expr b x; buf_add b ")"
  | EDo es ->
    buf_add b "(ignore (";
    List.iteri (fun i a ->
        if i > 0 then buf_add b "); ignore (";
        emit_expr b a)
      es;
    buf_add b "))"
  | ELet (pairs, body) ->
    List.iter
      (fun (bd, init) ->
        let selfrec =
          match init.desc with
          | EFun fn -> Modes.occurs_anywhere bd fn.body
          | _ -> false
        in
        buf_add b (if selfrec then "(let rec " else "(let ");
        (match bd.bmode, !oxcaml with
         | Ast.Local, false -> buf_add b "(* @local *) "
         | Ast.Owned, false -> buf_add b "(* @owned *) "
         | _ -> ());
        buf_add b (sanitize bd.bname ^ "__" ^ string_of_int bd.bid ^ " = ");
        (match bd.bmode, !oxcaml with
         | Ast.Local, true -> buf_add b "(local_ "
         | Ast.Owned, true -> buf_add b "(unique_ "
         | _ -> ());
        emit_expr b init;
        (match bd.bmode, !oxcaml with
         | Ast.Local, true | Ast.Owned, true -> buf_add b ")"
         | _ -> ());
        buf_add b " in ")
      pairs;
    emit_expr b body;
    List.iter (fun _ -> buf_add b ")") pairs
  | ETuple es ->
    buf_add b "("; List.iteri (fun i a -> if i > 0 then buf_add b ", "; emit_expr b a) es; buf_add b ")"
  | EVecLit es ->
    let el = match repr e.ety with TVec a -> a | _ -> TAny in
    if !oxcaml && e.emode = Ast.Local then buf_add b "(stack_ ";
    buf_add b "(Clj_core.Vec.of_list [";
    List.iteri (fun i x -> if i > 0 then buf_add b "; "; emit_elem b el x) es;
    buf_add b "])";
    if !oxcaml && e.emode = Ast.Local then buf_add b ")"
  | EListLit es ->
    let el = match repr e.ety with TList a -> a | _ -> TAny in
    buf_add b "[";
    List.iteri (fun i x -> if i > 0 then buf_add b "; "; emit_elem b el x) es;
    buf_add b "]"
  | EMapLit kes ->
    let kt, vt = match repr e.ety with TMap (k, v) -> (k, v) | _ -> (TAny, TAny) in
    if !oxcaml && e.emode = Ast.Local then buf_add b "(stack_ ";
    buf_add b "(Clj_core.Map.of_list [";
    List.iteri
      (fun i (k, v) ->
        if i > 0 then buf_add b "; ";
        buf_add b "("; emit_elem b kt k; buf_add b ", "; emit_elem b vt v; buf_add b ")")
      kes;
    buf_add b "])";
    if !oxcaml && e.emode = Ast.Local then buf_add b ")"
  | ESetLit es ->
    let el = match repr e.ety with TSet a -> a | _ -> TAny in
    if !oxcaml && e.emode = Ast.Local then buf_add b "(stack_ ";
    buf_add b "(Clj_core.Set.of_list [";
    List.iteri (fun i x -> if i > 0 then buf_add b "; "; emit_elem b el x) es;
    buf_add b "])";
    if !oxcaml && e.emode = Ast.Local then buf_add b ")"
  | EDynVec (se', bd, t, x) ->
    buf_add b "(match "; emit_expr b se'; buf_add b (" with Lg_rt.DVec " ^ sanitize bd.bname ^ "__" ^ string_of_int bd.bid ^ " -> ");
    emit_expr b t; buf_add b " | _ -> "; emit_expr b x; buf_add b ")"
  | EDynMap (se', bd, t, x) ->
    buf_add b "(match "; emit_expr b se'; buf_add b (" with Lg_rt.DMap " ^ sanitize bd.bname ^ "__" ^ string_of_int bd.bid ^ " -> ");
    emit_expr b t; buf_add b " | _ -> "; emit_expr b x; buf_add b ")"
  | EOpt (Some e) -> buf_add b ("(Some " ^ arg_str e ^ ")")
  | EOpt None -> buf_add b "None"
  | EBox e -> buf_add b (box_deep e.ety (arg_str e))
  | EUnbox (e', t') -> buf_add b ("(" ^ unbox_fn t' ^ " " ^ arg_str e' ^ ")")
  | EUnboxOpt (e', t') ->
    buf_add b ("(match " ^ arg_str e' ^ " with Some d -> Some (" ^ unbox_fn t' ^ " d) | None -> None)")
  | EMatchOpt (src, bd, t, x) ->
    buf_add b "(match "; emit_expr b src; buf_add b " with Some ";
    buf_add b (sanitize bd.bname ^ "__" ^ string_of_int bd.bid);
    buf_add b " -> "; emit_expr b t; buf_add b " | None -> "; emit_expr b x; buf_add b ")"

and emit_args b es = List.iteri (fun i a -> if i > 0 then buf_add b "; "; emit_expr b a) es
and arg_str e = let b = Buffer.create 16 in emit_expr b e; Buffer.contents b
and emit_call b ret ce args =
  match ce.desc with
  | EBuiltin name -> emit_builtin_call b ret name args
  | _ ->
    (* box args into dyn when the callee's formal param is `any` *)
    let pts = match repr ce.ety with TFun (ts, _) -> ts | _ -> [] in
    buf_add b "("; emit_expr b ce;
    List.iteri
      (fun i a ->
        buf_add b " ";
        if i < List.length pts && is_any (List.nth pts i) && not (is_any a.ety)
        then buf_add b (box_of a)
        else emit_expr b a)
      args;
    buf_add b ")";
  ignore ret

(* ---- printers for str/println/pr-str ---- *)
and printer_call t e =
  let es = arg_str e in
  match Typ.repr t with
  | TInt -> "(Lg_rt.str_int " ^ es ^ ")"
  | TFloat -> "(Lg_rt.str_float " ^ es ^ ")"
  | TBool -> "(Lg_rt.str_bool " ^ es ^ ")"
  | TChar -> "(Lg_rt.str_char " ^ es ^ ")"
  | TString -> "(Lg_rt.str_string " ^ es ^ ")"
  | TKeyword -> "(Lg_rt.str_kw " ^ es ^ ")"
  | TSymbol -> "(Lg_rt.str_sym " ^ es ^ ")"
  | TUnit -> "(Lg_rt.str_unit " ^ es ^ ")"
  | TList a -> "(Lg_rt.str_list " ^ gen_printer a ^ " " ^ es ^ ")"
  | TVec a -> "(Lg_rt.str_vec " ^ gen_printer a ^ " " ^ es ^ ")"
  | TMap (k, v) -> "(Lg_rt.str_map " ^ gen_printer k ^ " " ^ gen_printer v ^ " " ^ es ^ ")"
  | TSet a -> "(Lg_rt.str_set " ^ gen_printer a ^ " " ^ es ^ ")"
  | TOption a -> "(Lg_rt.str_opt " ^ gen_printer a ^ " " ^ es ^ ")"
  | TTuple ts ->
    let vs = List.mapi (fun i _ -> "t" ^ string_of_int i) ts in
    let ps = List.map2 (fun v t -> "(" ^ gen_printer t ^ " " ^ v ^ ")") vs ts in
    "(let (" ^ String.concat ", " vs ^ ") = " ^ es ^ " in \"(\" ^ String.concat \", \" [" ^ String.concat "; " ps ^ "] ^ \")\")"
  | TAny -> "(Lg_rt.str_dyn " ^ es ^ ")"
  | _ -> "\"<val>\""
and gen_printer t : string =
  let rec go t =
    match Typ.repr t with
    | TInt -> "Lg_rt.str_int" | TFloat -> "Lg_rt.str_float" | TBool -> "Lg_rt.str_bool"
    | TChar -> "Lg_rt.str_char" | TString -> "Lg_rt.str_string" | TKeyword -> "Lg_rt.str_kw"
    | TSymbol -> "Lg_rt.str_sym" | TUnit -> "Lg_rt.str_unit"
    | TList a -> "(Lg_rt.str_list " ^ go a ^ ")"
    | TVec a -> "(Lg_rt.str_vec " ^ go a ^ ")"
    | TMap (k, v) -> "(Lg_rt.str_map " ^ go k ^ " " ^ go v ^ ")"
    | TSet a -> "(Lg_rt.str_set " ^ go a ^ ")"
    | TOption a -> "(Lg_rt.str_opt " ^ go a ^ ")"
    | TTuple ts ->
      let vs = List.mapi (fun i _ -> "t" ^ string_of_int i) ts in
      let ps = List.map2 (fun v t -> "(" ^ go t ^ " " ^ v ^ ")") vs ts in
      "(fun t -> let (" ^ String.concat ", " vs ^ ") = t in \"(\" ^ String.concat \", \" [" ^ String.concat "; " ps ^ "] ^ \")\")"
    | TAny -> "Lg_rt.str_dyn"
    | _ -> "(fun _ -> \"<val>\")"
  in
  "(" ^ go t ^ ")"

(* ---- dyn boxing (TAny <-> Lg_rt.dyn) ---- *)
and dyn_ctor t =
  match Typ.repr t with
  | TInt -> "DInt" | TFloat -> "DFloat" | TBool -> "DBool" | TChar -> "DChar"
  | TString -> "DStr" | TKeyword -> "DKw" | TSymbol -> "DSym" | TUnit -> "DUnit"
  | TOption _ -> "DOpt" | TList _ -> "DList" | TVec _ -> "DVec"
  | TMap _ -> "DMap" | TSet _ -> "DSet"
  | _ -> "DStr"

and unbox_fn t =
  match Typ.repr t with
  | TInt -> "Lg_rt.as_int" | TFloat -> "Lg_rt.as_float" | TBool -> "Lg_rt.as_bool"
  | TChar -> "Lg_rt.as_char" | TString -> "Lg_rt.as_string" | TKeyword -> "Lg_rt.as_kw"
  | TSymbol -> "Lg_rt.as_sym" | TUnit -> "Lg_rt.as_unit" | TOption _ -> "Lg_rt.as_opt"
  | TList _ -> "Lg_rt.as_list" | TVec _ -> "Lg_rt.as_vec" | TMap _ -> "Lg_rt.as_map"
  | TSet _ -> "Lg_rt.as_set" | _ -> "Lg_rt.as_string"

(* deep box: a homogeneous collection crossed into `any` is re-boxed
   element-wise so the OCaml type is the closed Lg_rt.dyn *)
and box_deep ety es =
  match Typ.repr ety with
  | TVec el -> "(Lg_rt.DVec (Clj_core.Vec.map (fun x -> " ^ box_deep el "x" ^ ") " ^ es ^ "))"
  | TList el -> "(Lg_rt.DList (List.map (fun x -> " ^ box_deep el "x" ^ ") " ^ es ^ "))"
  | TSet el -> "(Lg_rt.DSet (Clj_core.Set.of_list (List.map (fun x -> " ^ box_deep el "x" ^ ") (Clj_core.Set.to_list " ^ es ^ "))))"
  | TMap _ -> "(Lg_rt.DMap " ^ nest_map_of ety es ^ ")"
  | TOption a -> "(Lg_rt.DOpt (match " ^ es ^ " with Some x -> Some (" ^ box_deep a "x" ^ ") | None -> None))"
  | TTuple _ | TFun _ -> "(Lg_rt.DStr \"<fn>\")"
  | TAny -> es
  | _ -> "(Lg_rt." ^ dyn_ctor ety ^ " " ^ es ^ ")"

and box_of e = box_deep e.ety (arg_str e)

(* a statically-typed map re-built as clj-core's (dyn, (dyn,dyn) nest) map —
   the shape Map.get_in / assoc_in / update_in / select_keys on dyn maps take,
   and the payload of Lg_rt.DMap *)
and nest_map_of ety es =
  match Typ.repr ety with
  | TMap (k, v) ->
    "(List.fold_left (fun m (k, v) -> Clj_core.Map.assoc m " ^ box_deep k "k" ^ " " ^ box_nest v "v"
    ^ ") (Clj_core.Map.of_list []) (List.of_seq (Clj_core.Map.seq " ^ es ^ ")))"
  | TAny -> "(match " ^ es ^ " with Lg_rt.DMap m -> m | _ -> Clj_core.Map.of_list [])"
  | _ -> "(Clj_core.Map.of_list [])"

(* a map value in a nest map: sub-maps are Nest, leaves are Leaf dyn *)
and box_nest ety es =
  match Typ.repr ety with
  | TMap _ -> "(Clj_core.Map.Nest " ^ nest_map_of ety es ^ ")"
  | TAny -> "(match " ^ es ^ " with Lg_rt.DMap m -> Clj_core.Map.Nest m | d -> Clj_core.Map.Leaf d)"
  | _ -> "(Clj_core.Map.Leaf " ^ box_deep ety es ^ ")"

(* the dyn-map arg of get-in / assoc-in / select-keys *)
and dyn_map_arg e = nest_map_of e.ety (arg_str e)

(* `Some dyn` lookup on a (dyn,(dyn,dyn)nest) map, keyed by a dyn *)
and dyn_map_get mstr kdyn =
  "(match Clj_core.Map.get " ^ mstr ^ " " ^ kdyn
  ^ " with Some (Clj_core.Map.Leaf d) -> Some d | Some (Clj_core.Map.Nest s) -> Some (Lg_rt.DMap s) | None -> None)"

(* unwrapped lookup with default *)
and dyn_map_get_or dstr mstr kdyn =
  "(match Clj_core.Map.get " ^ mstr ^ " " ^ kdyn
  ^ " with Some (Clj_core.Map.Leaf d) -> d | Some (Clj_core.Map.Nest s) -> Lg_rt.DMap s | None -> " ^ dstr ^ ")"
and is_any t = match Typ.repr t with TAny -> true | _ -> false
and as_dyn_list e =
  match Typ.repr e.ety with
  | TList el | TVec el | TSet el | TOption el ->
    if is_any el then as_list e
    else "(List.map (fun x -> Lg_rt." ^ dyn_ctor el ^ " x) " ^ as_list e ^ ")"
  | _ -> as_list e

(* emit an element expr, boxing it into dyn when the collection is hetero *)
and emit_elem b elem_ty e =
  if is_any elem_ty && not (is_any e.ety) then buf_add b (box_of e) else emit_expr b e

(* coll dispatch by static type *)
and coll_kind t =
  match Typ.repr t with
  | TVec _ -> `Vec | TList _ -> `List | TSet _ -> `Set | TMap _ -> `Map | TString -> `Str | _ -> `List

(* the collection arg as an OCaml list expr *)
and as_list e =
  let a = arg_str e in
  match coll_kind e.ety with
  | `Vec -> "(Clj_core.Vec.to_list " ^ a ^ ")"
  | `Set -> "(Clj_core.Set.to_list " ^ a ^ ")"
  | `Map -> "(List.of_seq (Clj_core.Map.seq " ^ a ^ "))"
  | `Str -> "(Lg_rt.string_chars " ^ a ^ ")"
  | `List -> a

(* ---- FBIP: unique-owner update chains -> mutable builder + one freeze ----
   A spine of conj/assoc/into/pop/dissoc/disj/update calls rooted at a fresh
   literal (or a once-used binder of a literal) is unique-owned: emit one
   mutable builder instead of n intermediate persistent values. *)

and owned_root e =
  match e.desc with
  | EVecLit _ | EMapLit _ | ESetLit _ -> true
  | ELocal bd -> bd.bused <= 1 && bd.bmode = Ast.Local && bd.blit
  | _ -> false

and coll_spine e : (expr * cop list) option =
  match e.desc with
  | ECall ({ desc = EBuiltin n; _ }, args) -> chain_step n args
  | _ -> None

and chain_step n args : (expr * cop list) option =
  match n, args with
  | _, c :: _ ->
    let step mk =
      let root_ops =
        match coll_spine c with
        | Some _ as r -> r
        | None -> if owned_root c then Some (c, []) else None
      in
      match root_ops, mk (repr c.ety) with
      | Some (r, ops), Some more -> Some (r, ops @ more)
      | _ -> None
    in
    (match n, args with
     | "conj", _ :: xs when xs <> [] ->
       step (function
         | TVec _ -> Some (List.map (fun x -> CPush x) xs)
         | TMap _ -> Some (List.map (fun x -> CPair x) xs)
         | TSet _ -> Some (List.map (fun x -> CAdd x) xs)
         | _ -> None)
     | "assoc", _ :: i :: x :: rest ->
       step (function
         | TVec _ when rest = [] -> Some [ CSet (i, x) ]
         | TMap _ when List.length rest mod 2 = 0 ->
           let rec ps = function a :: b :: t -> (a, b) :: ps t | [] -> [] | _ -> [] in
           Some (List.map (fun (k, v) -> CPut (k, v)) ((i, x) :: ps rest))
         | TMap _ -> None
         | _ -> None)
     | "dissoc", _ :: ks when ks <> [] ->
       step (function TMap _ -> Some (List.map (fun k -> CDrop k) ks) | _ -> None)
     | "pop", [ _ ] -> step (function TVec _ -> Some [ CPop ] | _ -> None)
     | "update", [ _; i; f ] ->
       step (function TVec _ -> Some [ CUpd (i, f) ] | TMap _ -> Some [ CUpdMap (i, f) ] | _ -> None)
     | "into", [ _; xs ] ->
       (match repr xs.ety with
        | TMap _ -> step (function TMap _ -> Some [ CMExt xs ] | _ -> None)
        | TVec _ | TList _ | TSet _ ->
          step (function TVec _ -> Some [ CExt xs ] | TSet _ -> Some [ CSExt xs ] | _ -> None)
        | _ -> None)
     | "disj", _ :: xs when xs <> [] ->
       step (function TSet _ -> Some (List.map (fun x -> CDel x) xs) | _ -> None)
     | _ -> None)
  | _ -> None

and emit_owned_chain b name args : bool =
  match chain_step name args with
  | None -> false
  | Some (root, ops) ->
    (match repr root.ety with
     | TVec el -> emit_vbuilder b root el ops; true
     | TMap (k, v) -> emit_mbuilder b root k v ops; true
     | TSet el -> emit_sbuilder b root el ops; true
     | _ -> false)

and vroot b root =
  match root.desc with
  | EVecLit es ->
    let el = match repr root.ety with TVec a -> a | _ -> TAny in
    buf_add b "(Lg_rt.vb_of_arr [|";
    List.iteri (fun i x -> if i > 0 then buf_add b "; "; emit_elem b el x) es;
    buf_add b "|])"
  | _ -> buf_add b "(Lg_rt.vb_of_vec "; emit_expr b root; buf_add b ")"

and mroot b root kt vt =
  match root.desc with
  | EMapLit kes ->
    buf_add b "(Lg_rt.mb_of_list [";
    List.iteri
      (fun i (k, v) ->
        if i > 0 then buf_add b "; ";
        buf_add b "("; emit_elem b kt k; buf_add b ", "; emit_elem b vt v; buf_add b ")")
      kes;
    buf_add b "])"
  | _ -> buf_add b "(Lg_rt.mb_of_map "; emit_expr b root; buf_add b ")"

and sroot b root =
  match root.desc with
  | ESetLit es ->
    let el = match repr root.ety with TSet a -> a | _ -> TAny in
    buf_add b "(Lg_rt.sb_of_list [";
    List.iteri (fun i x -> if i > 0 then buf_add b "; "; emit_elem b el x) es;
    buf_add b "])"
  | _ -> buf_add b "(Lg_rt.sb_of_set "; emit_expr b root; buf_add b ")"

(* element of a source collection, reboxed when the target elem is `any` *)
and ext_elem el sel emit_x =
  if is_any el && not (is_any sel) then
    let b2 = Buffer.create 16 in
    buf_add b2 (box_deep sel emit_x);
    Buffer.contents b2
  else emit_x

and emit_vop b bn el op =
  let ax e = arg_str e in
  let elem e = let b2 = Buffer.create 16 in emit_elem b2 el e; Buffer.contents b2 in
  match op with
  | CPush x -> buf_add b ("Lg_rt.vb_push " ^ bn ^ " " ^ elem x ^ "; ")
  | CSet (i, x) -> buf_add b ("Lg_rt.vb_set " ^ bn ^ " " ^ ax i ^ " " ^ elem x ^ "; ")
  | CUpd (i, f) -> buf_add b ("Lg_rt.vb_update " ^ bn ^ " " ^ ax i ^ " " ^ ax f ^ "; ")
  | CPop -> buf_add b ("Lg_rt.vb_pop " ^ bn ^ "; ")
  | CExt xs ->
    let it, sel =
      match repr xs.ety with
      | TVec sel -> ("Clj_core.Vec.iter", sel)
      | TList sel -> ("Clj_core.List.iter", sel)
      | TSet sel -> ("Clj_core.Set.iter", sel)
      | _ -> ("", TUnit)
    in
    buf_add b ("(" ^ it ^ " (fun x -> Lg_rt.vb_push " ^ bn ^ " " ^ ext_elem el sel "x" ^ ") " ^ ax xs ^ "); ")
  | _ -> ()

and emit_mop b bn kt vt op =
  let ax e = arg_str e in
  let ke e = let b2 = Buffer.create 16 in emit_elem b2 kt e; Buffer.contents b2 in
  let ve e = let b2 = Buffer.create 16 in emit_elem b2 vt e; Buffer.contents b2 in
  match op with
  | CPut (k, v) -> buf_add b ("Lg_rt.mb_assoc " ^ bn ^ " " ^ ke k ^ " " ^ ve v ^ "; ")
  | CDrop k -> buf_add b ("Lg_rt.mb_dissoc " ^ bn ^ " " ^ ke k ^ "; ")
  | CUpdMap (k, f) -> buf_add b ("Lg_rt.mb_update " ^ bn ^ " " ^ ke k ^ " " ^ ax f ^ "; ")
  | CPair kv -> buf_add b ("Lg_rt.mb_assoc_pair " ^ bn ^ " " ^ ax kv ^ "; ")
  | CMExt m2 ->
    (match repr m2.ety with
     | TMap (sk, sv) ->
       buf_add b
         ("(Clj_core.Map.iter (fun k v -> Lg_rt.mb_assoc " ^ bn ^ " "
          ^ ext_elem kt sk "k" ^ " " ^ ext_elem vt sv "v" ^ ") " ^ ax m2 ^ "); ")
     | _ -> ())
  | _ -> ()

and emit_sop b bn el op =
  let ax e = arg_str e in
  let elem e = let b2 = Buffer.create 16 in emit_elem b2 el e; Buffer.contents b2 in
  match op with
  | CAdd x -> buf_add b ("Lg_rt.sb_add " ^ bn ^ " " ^ elem x ^ "; ")
  | CDel x -> buf_add b ("Lg_rt.sb_disj " ^ bn ^ " " ^ elem x ^ "; ")
  | CSExt xs ->
    let it, sel =
      match repr xs.ety with
      | TVec sel -> ("Clj_core.Vec.iter", sel)
      | TList sel -> ("Clj_core.List.iter", sel)
      | TSet sel -> ("Clj_core.Set.iter", sel)
      | _ -> ("", TUnit)
    in
    buf_add b ("(" ^ it ^ " (fun x -> Lg_rt.sb_add " ^ bn ^ " " ^ ext_elem el sel "x" ^ ") " ^ ax xs ^ "); ")
  | _ -> ()

and emit_vbuilder b root el ops =
  let bn = "vb__" ^ string_of_int (fresh_uid ()) in
  buf_add b ("(let " ^ bn ^ " = "); vroot b root; buf_add b " in ";
  List.iter (emit_vop b bn el) ops;
  buf_add b ("Lg_rt.vb_freeze " ^ bn ^ ")")

and emit_mbuilder b root kt vt ops =
  let bn = "mb__" ^ string_of_int (fresh_uid ()) in
  buf_add b ("(let " ^ bn ^ " = "); mroot b root kt vt; buf_add b " in ";
  List.iter (emit_mop b bn kt vt) ops;
  buf_add b ("Lg_rt.mb_freeze " ^ bn ^ ")")

and emit_sbuilder b root el ops =
  let bn = "sb__" ^ string_of_int (fresh_uid ()) in
  buf_add b ("(let " ^ bn ^ " = "); sroot b root; buf_add b " in ";
  List.iter (emit_sop b bn el) ops;
  buf_add b ("Lg_rt.sb_freeze " ^ bn ^ ")")

and emit_builtin_call b ret name args =
  if not (emit_owned_chain b name args) then begin
  let a n = arg_str (List.nth args n) in
  let t n = (List.nth args n).ety in
  let coll = if args = [] then `List else coll_kind (t 0) in
  (match name with
   | "+" | "-" | "*" | "/" | "+." | "-." | "*." | "/." | "neg" | "neg." ->
     let fl = String.contains name '.' in
     let unbox e = if is_any e.ety then "(" ^ (if fl then "Lg_rt.as_float" else "Lg_rt.as_int") ^ " " ^ arg_str e ^ ")" else arg_str e in
     (match name with
      | "neg" -> buf_add b ("(~- " ^ unbox (List.nth args 0) ^ ")")
      | "neg." -> buf_add b ("(~-. " ^ unbox (List.nth args 0) ^ ")")
      | _ ->
        let op = if fl then String.sub name 0 (String.length name - 1) ^ "." else name in
        buf_add b ("(" ^ unbox (List.nth args 0) ^ " " ^ op ^ " " ^ unbox (List.nth args 1) ^ ")"))
   | "<" | "<=" | ">" | ">=" | "<." | "<=." | ">." | ">=." ->
     let op = if name.[String.length name - 1] = '.' then String.sub name 0 (String.length name - 1) else name in
     let unbox e = if is_any e.ety then "(Lg_rt.as_int " ^ arg_str e ^ ")" else arg_str e in
     buf_add b ("(" ^ unbox (List.nth args 0) ^ " " ^ op ^ " " ^ unbox (List.nth args 1) ^ ")")
   | "=" -> buf_add b ("(" ^ a 0 ^ " = " ^ a 1 ^ ")")
   | "not=" -> buf_add b ("(" ^ a 0 ^ " <> " ^ a 1 ^ ")")
   | "not" -> buf_add b ("(not " ^ a 0 ^ ")")
   | "inc" -> buf_add b ("(" ^ a 0 ^ " + 1)")
   | "dec" -> buf_add b ("(" ^ a 0 ^ " - 1)")
   | "mod" -> buf_add b ("(" ^ a 0 ^ " mod " ^ a 1 ^ ")")
   | "abs" -> buf_add b ("(abs " ^ a 0 ^ ")")
   | "identity" -> buf_add b (a 0)
   | "constantly" -> buf_add b ("(fun _ -> " ^ a 0 ^ ")")
   | "float" ->
     buf_add b
       (match repr (t 0) with
        | TInt -> "(float_of_int " ^ a 0 ^ ")"
        | TChar -> "(float_of_int (Char.code " ^ a 0 ^ "))"
        | TString -> "(float_of_string " ^ a 0 ^ ")"
        | _ -> a 0)
   | "int" ->
     buf_add b
       (match repr (t 0) with
        | TFloat -> "(int_of_float " ^ a 0 ^ ")"
        | TChar -> "(Char.code " ^ a 0 ^ ")"
        | TString -> "(int_of_string " ^ a 0 ^ ")"
        | _ -> a 0)
   | "name" ->
     buf_add b
       (match repr (t 0) with
        | TKeyword -> "(Clj_core.Keyword.name " ^ a 0 ^ ")"
        | TSymbol -> "(Clj_core.Symbol.name " ^ a 0 ^ ")"
        | _ -> a 0)
   | "keyword" -> buf_add b ("(Clj_core.Keyword.of_string " ^ a 0 ^ ")")
   | "symbol" -> buf_add b ("(Clj_core.Symbol.of_string " ^ a 0 ^ ")")
   | "str" | "pr-str" ->
     let parts = List.map (fun e -> printer_call e.ety e) args in
     buf_add b ("(" ^ String.concat " ^ " (if parts = [] then [ "\"\"" ] else parts) ^ ")")
   | "println" | "print" ->
     let parts = List.map (fun e -> printer_call e.ety e) args in
     let joined = String.concat " ^ \" \" ^ " (if parts = [] then [ "\"\"" ] else parts) in
     buf_add b ("(" ^ (if name = "println" then "print_endline" else "print_string") ^ " (" ^ joined ^ "))")
   | "cons" -> buf_add b ("(" ^ a 0 ^ " :: " ^ a 1 ^ ")")
   | "list" -> buf_add b ("[" ^ String.concat "; " (List.map arg_str args) ^ "]")
   | "vector" -> buf_add b ("(Clj_core.Vec.of_list [" ^ String.concat "; " (List.map arg_str args) ^ "])")
   | "hash-map" ->
     let kt, vt = match repr ret with TMap (k, v) -> (k, v) | _ -> (TUnit, TUnit) in
     let enc ty e = if is_any ty && not (is_any e.ety) then box_of e else arg_str e in
     let rec pairs acc = function
       | k :: v :: rest -> pairs (("(" ^ enc kt k ^ ", " ^ enc vt v ^ ")") :: acc) rest
       | [] -> List.rev acc
       | [ _ ] -> acc
     in
     buf_add b ("(Clj_core.Map.of_list [" ^ String.concat "; " (pairs [] args) ^ "])")
   | "hash-set" ->
     let el = match repr ret with TSet e -> e | _ -> TUnit in
     buf_add b ("(Clj_core.Set.of_list [" ^ String.concat "; " (List.map (fun e -> if is_any el && not (is_any e.ety) then box_of e else arg_str e) args) ^ "])")
   | "first" ->
     (match coll with
      | `Vec -> buf_add b ("(Clj_core.Vec.first " ^ a 0 ^ ")")
      | `List -> buf_add b ("(match " ^ a 0 ^ " with [] -> None | x :: _ -> Some x)")
      | `Set -> buf_add b ("(Clj_core.Set.first " ^ a 0 ^ ")")
      | `Map -> buf_add b ("(match List.of_seq (Clj_core.Map.seq " ^ a 0 ^ ") with [] -> None | kv :: _ -> Some kv)")
      | `Str -> buf_add b ("(if String.length " ^ a 0 ^ " > 0 then Some " ^ a 0 ^ ".[0] else None)"))
   | "next" ->
     buf_add b ("(match " ^ as_list (List.nth args 0) ^ " with [] -> None | _ :: t -> Some t)")
   | "rest" -> buf_add b ("(match " ^ as_list (List.nth args 0) ^ " with [] -> [] | _ :: t -> t)")
   | "seq" -> buf_add b (as_list (List.nth args 0))
   | "count" ->
     (match coll with
      | `Vec -> buf_add b ("(Clj_core.Vec.count " ^ a 0 ^ ")")
      | `List -> buf_add b ("(List.length " ^ a 0 ^ ")")
      | `Set -> buf_add b ("(Clj_core.Set.count " ^ a 0 ^ ")")
      | `Map -> buf_add b ("(Clj_core.Map.count " ^ a 0 ^ ")")
      | `Str -> buf_add b ("(String.length " ^ a 0 ^ ")"))
   | "empty?" ->
     (match coll with
      | `Vec -> buf_add b ("(Clj_core.Vec.is_empty " ^ a 0 ^ ")")
      | `List -> buf_add b ("(" ^ a 0 ^ " = [])")
      | `Set -> buf_add b ("(Clj_core.Set.is_empty " ^ a 0 ^ ")")
      | `Map -> buf_add b ("(Clj_core.Map.is_empty " ^ a 0 ^ ")")
      | `Str -> buf_add b ("(String.length " ^ a 0 ^ " = 0)"))
   | "map?" ->
     (match repr (t 0) with
      | TMap _ -> buf_add b "true"
      | TAny -> buf_add b ("(match " ^ dyn_map_arg (List.nth args 0) ^ " with Clj_core.Map.Nest _ -> true | _ -> false)")
      | _ -> buf_add b "false")
   | "contains?" ->
     (match coll with
      | `Vec -> buf_add b ("(Clj_core.Vec.contains_ " ^ a 0 ^ " " ^ a 1 ^ ")")
      | `List -> buf_add b ("(List.mem " ^ a 1 ^ " " ^ a 0 ^ ")")
      | `Set -> buf_add b ("(Clj_core.Set.contains_ " ^ a 0 ^ " " ^ a 1 ^ ")")
      | `Map -> buf_add b ("(Clj_core.Map.contains_ " ^ a 0 ^ " " ^ a 1 ^ ")")
      | `Str -> buf_add b "(failwith \"contains? on string\")")
   | "get" when (match repr (t 0) with TAny -> true | _ -> false) ->
     let mstr = dyn_map_arg (List.nth args 0) in
     let kd = box_of (List.nth args 1) in
     if List.length args = 3 then buf_add b (dyn_map_get_or (box_of (List.nth args 2)) mstr kd)
     else buf_add b (dyn_map_get mstr kd)
   | "get" ->
     (match coll with
      | `Vec ->
        if List.length args = 3 then
          let el = match repr (t 0) with TVec e -> e | _ -> TUnit in
          let d = if is_any el then box_of (List.nth args 2) else a 2 in
          buf_add b ("(match Clj_core.Vec.nth_opt " ^ a 0 ^ " " ^ a 1 ^ " with Some v -> v | None -> " ^ d ^ ")")
        else buf_add b ("(Clj_core.Vec.get " ^ a 0 ^ " " ^ a 1 ^ ")")
      | `List ->
        if List.length args = 3 then
          let el = match repr (t 0) with TList e -> e | _ -> TUnit in
          let d = if is_any el then box_of (List.nth args 2) else a 2 in
          buf_add b ("(match List.nth_opt " ^ a 0 ^ " " ^ a 1 ^ " with Some v -> v | None -> " ^ d ^ ")")
        else buf_add b ("(List.nth_opt " ^ a 0 ^ " " ^ a 1 ^ ")")
      | `Set ->
        if List.length args = 3 then buf_add b ("(if Clj_core.Set.contains_ " ^ a 0 ^ " " ^ a 1 ^ " then " ^ a 1 ^ " else " ^ a 2 ^ ")")
        else buf_add b ("(if Clj_core.Set.contains_ " ^ a 0 ^ " " ^ a 1 ^ " then Some " ^ a 1 ^ " else None)")
      | `Map ->
        (match repr (t 0) with
         | TMap (k, _) when is_any k ->
           let kd = box_of (List.nth args 1) in
           if List.length args = 3 then buf_add b (dyn_map_get_or (box_of (List.nth args 2)) (a 0) kd)
           else buf_add b (dyn_map_get (a 0) kd)
         | _ ->
           if List.length args = 3 then buf_add b ("(Clj_core.Map.get_or " ^ a 2 ^ " " ^ a 0 ^ " " ^ a 1 ^ ")")
           else buf_add b ("(Clj_core.Map.get " ^ a 0 ^ " " ^ a 1 ^ ")"))
      | `Str -> buf_add b "(failwith \"get on string\")")
   | "nth" ->
     (match coll with
      | `Vec ->
        if List.length args = 3 then buf_add b ("(match Clj_core.Vec.nth_opt " ^ a 0 ^ " " ^ a 1 ^ " with Some v -> v | None -> " ^ a 2 ^ ")")
        else buf_add b ("(Clj_core.Vec.nth " ^ a 0 ^ " " ^ a 1 ^ ")")
      | `List ->
        if List.length args = 3 then buf_add b ("(match List.nth_opt " ^ a 0 ^ " " ^ a 1 ^ " with Some v -> v | None -> " ^ a 2 ^ ")")
        else buf_add b ("(List.nth " ^ a 0 ^ " " ^ a 1 ^ ")")
      | `Str ->
        if List.length args = 3 then buf_add b ("(if " ^ a 1 ^ " < String.length " ^ a 0 ^ " then " ^ a 0 ^ ".[" ^ a 1 ^ "] else " ^ a 2 ^ ")")
        else buf_add b ("(" ^ a 0 ^ ".[" ^ a 1 ^ "])")
      | _ -> buf_add b "(failwith \"nth\")")
   | "conj" ->
     let elem_ty = match repr (t 0) with TVec el -> el | TList el -> el | TSet el -> el | _ -> TUnit in
     let arg i =
       let e = List.nth args i in
       if is_any elem_ty && not (is_any e.ety) then box_of e else a i
     in
     (match coll with
      | `Vec ->
        buf_add b (List.fold_left (fun acc i -> "(Clj_core.Vec.conj " ^ acc ^ " " ^ arg i ^ ")") (a 0) (List.init (List.length args - 1) (fun i -> i + 1)))
      | `List ->
        buf_add b (List.fold_left (fun acc i -> "(" ^ arg i ^ " :: " ^ acc ^ ")") (a 0) (List.init (List.length args - 1) (fun i -> List.length args - 1 - i)))
      | `Set ->
        buf_add b (List.fold_left (fun acc i -> "(Clj_core.Set.conj " ^ acc ^ " " ^ arg i ^ ")") (a 0) (List.init (List.length args - 1) (fun i -> i + 1)))
      | `Map ->
        buf_add b (List.fold_left
                     (fun acc i -> "(match Clj_core.Vec.to_list " ^ a i ^ " with [k; v] -> Clj_core.Map.conj " ^ acc ^ " (k, v) | _ -> failwith \"conj: map entry must be [k v]\")")
                     (a 0) (List.init (List.length args - 1) (fun i -> i + 1)))
      | `Str -> buf_add b "(failwith \"conj on string\")")
   | "assoc" ->
     (match coll with
      | `Vec ->
        let el = match repr (t 0) with TVec e -> e | _ -> TUnit in
        let v = if is_any el then box_of (List.nth args 2) else a 2 in
        buf_add b ("(Clj_core.Vec.assoc " ^ a 0 ^ " " ^ a 1 ^ " " ^ v ^ ")")
      | `Map ->
        let vt = match repr (t 0) with TMap (_, v) -> v | _ -> TUnit in
        let va i = let e = List.nth args i in if is_any vt && not (is_any e.ety) then box_of e else a i in
        let rec go acc i =
          if i + 1 >= List.length args then acc
          else go ("(Clj_core.Map.assoc " ^ acc ^ " " ^ a i ^ " " ^ va (i + 1) ^ ")") (i + 2)
        in
        buf_add b (go (a 0) 1)
      | _ -> buf_add b "(failwith \"assoc\")")
   | "dissoc" ->
     buf_add b (List.fold_left (fun acc i -> "(Clj_core.Map.dissoc " ^ acc ^ " " ^ a i ^ ")") (a 0) (List.init (List.length args - 1) (fun i -> i + 1)))
   | "keys" -> buf_add b ("(List.of_seq (Clj_core.Map.keys " ^ a 0 ^ "))")
   | "vals" -> buf_add b ("(List.of_seq (Clj_core.Map.vals " ^ a 0 ^ "))")
   | "merge" -> buf_add b (List.fold_left (fun acc i -> "(Clj_core.Map.merge " ^ acc ^ " " ^ a i ^ ")") (a 0) (List.init (List.length args - 1) (fun i -> i + 1)))
   | "kw-get" ->
     let kd = "(Lg_rt.DKw " ^ a 0 ^ ")" in
     (match repr (t 1) with
      | TMap (k, _) when is_any k ->
        if List.length args = 3 then buf_add b (dyn_map_get_or (box_of (List.nth args 2)) (a 1) kd)
        else buf_add b (dyn_map_get (a 1) kd)
      | TAny ->
        let mstr = dyn_map_arg (List.nth args 1) in
        if List.length args = 3 then buf_add b (dyn_map_get_or (box_of (List.nth args 2)) mstr kd)
        else buf_add b (dyn_map_get mstr kd)
      | _ ->
        if List.length args = 3 then buf_add b ("(Clj_core.Map.get_or " ^ a 2 ^ " " ^ a 1 ^ " " ^ a 0 ^ ")")
        else buf_add b ("(Clj_core.Map.get " ^ a 1 ^ " " ^ a 0 ^ ")"))
   | "vec" -> buf_add b ("(Clj_core.Vec.of_list " ^ as_list (List.nth args 0) ^ ")")
   | "peek" -> buf_add b ("(Clj_core.Vec.peek " ^ a 0 ^ ")")
   | "pop" -> buf_add b ("(Clj_core.Vec.pop " ^ a 0 ^ ")")
   | "set" -> buf_add b ("(Clj_core.Set.of_list " ^ as_list (List.nth args 0) ^ ")")
   | "disj" -> buf_add b (List.fold_left (fun acc i -> "(Clj_core.Set.disj " ^ acc ^ " " ^ a i ^ ")") (a 0) (List.init (List.length args - 1) (fun i -> i + 1)))
   | "union" -> buf_add b ("(Clj_core.Set.union " ^ a 0 ^ " " ^ a 1 ^ ")")
   | "map" ->
     let f = a 0 in
     (match coll_kind (t 1) with
      | `Vec -> buf_add b ("(Clj_core.Vec.map " ^ f ^ " " ^ a 1 ^ ")")
      | `List -> buf_add b ("(List.map " ^ f ^ " " ^ a 1 ^ ")")
      | `Set -> buf_add b ("(Clj_core.Vec.of_list (List.map " ^ f ^ " (Clj_core.Set.to_list " ^ a 1 ^ ")))")
      | `Map -> buf_add b ("(Clj_core.Map.map (fun v -> " ^ f ^ " v) " ^ a 1 ^ ")")
      | `Str -> buf_add b ("(List.map " ^ f ^ " (Lg_rt.string_chars " ^ a 1 ^ "))"))
   | "filter" ->
     let f = a 0 in
     (match coll_kind (t 1) with
      | `Vec -> buf_add b ("(Clj_core.Vec.filter " ^ f ^ " " ^ a 1 ^ ")")
      | `List -> buf_add b ("(List.filter " ^ f ^ " " ^ a 1 ^ ")")
      | `Set -> buf_add b ("(Clj_core.Set.filter " ^ f ^ " " ^ a 1 ^ ")")
      | `Map -> buf_add b ("(Clj_core.Map.filter (fun k v -> " ^ f ^ " (k, v)) " ^ a 1 ^ ")")
      | `Str -> buf_add b "(failwith \"filter on string\")")
   | "reduce" ->
     buf_add b ("(match " ^ a 2 ^ " with "
                ^ (match coll_kind (t 2) with
                   | `Vec -> "_ -> Clj_core.Vec.reduce " ^ a 0 ^ " " ^ a 1 ^ " " ^ a 2
                   | `Set -> "_ -> List.fold_left " ^ a 0 ^ " " ^ a 1 ^ " (Clj_core.Set.to_list " ^ a 2 ^ ")"
                   | `Map -> "_ -> Clj_core.Map.fold (fun acc k v -> " ^ a 0 ^ " acc (k, v)) " ^ a 1 ^ " " ^ a 2
                   | `Str -> "_ -> List.fold_left " ^ a 0 ^ " " ^ a 1 ^ " (Lg_rt.string_chars " ^ a 2 ^ ")"
                   | `List -> "_ -> List.fold_left " ^ a 0 ^ " " ^ a 1 ^ " " ^ a 2)
                ^ ")")
   | "mapv" ->
     (match coll_kind (t 1) with
      | `Vec -> buf_add b ("(Clj_core.Vec.map " ^ a 0 ^ " " ^ a 1 ^ ")")
      | _ -> buf_add b ("(Clj_core.Vec.of_list (List.map " ^ a 0 ^ " " ^ as_list (List.nth args 1) ^ ")))"))
   | "filterv" ->
     (match coll_kind (t 1) with
      | `Vec -> buf_add b ("(Clj_core.Vec.filter " ^ a 0 ^ " " ^ a 1 ^ ")")
      | _ -> buf_add b ("(Clj_core.Vec.of_list (List.filter " ^ a 0 ^ " " ^ as_list (List.nth args 1) ^ ")))"))
   | "into" ->
     let src_items =
       let el = match Typ.repr (t 0) with TVec x -> x | TList x -> x | TSet x -> x | _ -> TUnit in
       if is_any el then as_dyn_list (List.nth args 1) else as_list (List.nth args 1)
     in
     (match coll with
      | `Vec -> buf_add b ("(List.fold_left Clj_core.Vec.conj " ^ a 0 ^ " " ^ src_items ^ ")")
      | `Set -> buf_add b ("(List.fold_left Clj_core.Set.conj " ^ a 0 ^ " " ^ src_items ^ ")")
      | `Map ->
        buf_add b ("(List.fold_left (fun m e -> match Clj_core.Vec.to_list e with [k; v] -> Clj_core.Map.conj m (k, v) | (k, v) -> Clj_core.Map.conj m (k, v) | _ -> m) " ^ a 0 ^ " " ^ as_list (List.nth args 1) ^ ")")
      | `List -> buf_add b ("(" ^ as_list (List.nth args 1) ^ " @ " ^ a 0 ^ ")")
      | `Str -> buf_add b "(failwith \"into string\")")
   | "take" ->
     (match coll_kind (t 1) with
      | `Vec -> buf_add b ("(Clj_core.Vec.take " ^ a 0 ^ " " ^ a 1 ^ ")")
      | `Set -> buf_add b ("(Lg_rt.list_take " ^ a 0 ^ " (Clj_core.Set.to_list " ^ a 1 ^ "))")
      | `Str -> buf_add b ("(Lg_rt.list_take " ^ a 0 ^ " (Lg_rt.string_chars " ^ a 1 ^ "))")
      | _ -> buf_add b ("(Lg_rt.list_take " ^ a 0 ^ " " ^ as_list (List.nth args 1) ^ ")"))
   | "drop" ->
     (match coll_kind (t 1) with
      | `Vec -> buf_add b ("(Clj_core.Vec.drop " ^ a 0 ^ " " ^ a 1 ^ ")")
      | `Set -> buf_add b ("(Lg_rt.list_drop " ^ a 0 ^ " (Clj_core.Set.to_list " ^ a 1 ^ "))")
      | `Str -> buf_add b ("(Lg_rt.list_drop " ^ a 0 ^ " (Lg_rt.string_chars " ^ a 1 ^ "))")
      | _ -> buf_add b ("(Lg_rt.list_drop " ^ a 0 ^ " " ^ as_list (List.nth args 1) ^ ")"))
   | "range" ->
     if List.length args = 2 then buf_add b ("(Lg_rt.range " ^ a 0 ^ " " ^ a 1 ^ ")")
     else buf_add b ("(Lg_rt.range 0 " ^ a 0 ^ ")")
   | "concat" -> buf_add b ("(List.concat [" ^ String.concat "; " (List.map as_list args) ^ "])")
   | "apply" -> buf_add b (emit_apply args)
   | "atom" ->
     if is_any ret then buf_add b ("(Clj_core.Atom.atom " ^ box_of (List.nth args 0) ^ ")")
     else (match repr ret with TAtom p when is_any p -> buf_add b ("(Clj_core.Atom.atom " ^ box_of (List.nth args 0) ^ ")") | _ -> buf_add b ("(Clj_core.Atom.atom " ^ a 0 ^ ")"))
   | "deref" -> buf_add b ("(Clj_core.Atom.deref " ^ a 0 ^ ")")
   | "reset!" ->
     let av = match repr (t 0) with TAtom p -> p | _ -> TAny in
     if is_any av then buf_add b ("(Clj_core.Atom.reset_bang " ^ a 0 ^ " " ^ box_of (List.nth args 1) ^ ")")
     else buf_add b ("(Clj_core.Atom.reset_bang " ^ a 0 ^ " " ^ a 1 ^ ")")
   | "no-match" -> buf_add b "(Lg_rt.no_match ())"
   | "dyn-eq" -> buf_add b ("(" ^ a 0 ^ " = " ^ box_of (List.nth args 1) ^ ")")
   | "select-keys" ->
     (match Typ.repr (t 0) with
      | TMap (k, _) when is_any k ->
        (* already a nest map: keys are dyn — box the kw list *)
        buf_add b ("(Lg_rt.dyn_map_of_nest_map (Clj_core.Map.select_keys " ^ a 0
                   ^ " (List.map (fun k -> Lg_rt.DKw k) " ^ as_list (List.nth args 1) ^ ")))")
      | TMap _ ->
        buf_add b ("(Clj_core.Map.select_keys " ^ a 0 ^ " " ^ as_list (List.nth args 1) ^ ")")
      | _ ->
        buf_add b ("(Lg_rt.dyn_map_of_nest_map (Clj_core.Map.select_keys " ^ dyn_map_arg (List.nth args 0)
                   ^ " (List.map (fun k -> Lg_rt.DKw k) " ^ as_list (List.nth args 1) ^ ")))"))
   | "update" -> buf_add b ("(Clj_core.Map.assoc " ^ a 0 ^ " " ^ a 1 ^ " (" ^ a 2 ^ " (match Clj_core.Map.get " ^ a 0 ^ " " ^ a 1 ^ " with Some uv__ -> uv__ | None -> failwith \"update: missing key\")))")
   | "get-in" | "assoc-in" ->
     let ks_arg = List.nth args 1 in
     (* clj-core's get_in/assoc_in walk 'k keys of the nest map — dyn here —
        so keyword paths are boxed to DKw and dyn paths pass through *)
     let kw_list =
       match repr ks_arg.ety with
       | TList el | TVec el when is_any el -> as_list ks_arg
       | _ -> "(List.map (fun k -> Lg_rt.DKw k) " ^ as_list ks_arg ^ ")"
     in
     if name = "get-in" then
       buf_add b ("(match Clj_core.Map.get_in " ^ dyn_map_arg (List.nth args 0) ^ " " ^ kw_list
                  ^ " with Some n -> (match n with Clj_core.Map.Leaf d -> Some d | Clj_core.Map.Nest s -> Some (Lg_rt.DMap s)) | None -> None)")
     else
       let v_arg = List.nth args 2 in
       let boxed = if is_any v_arg.ety then arg_str v_arg else box_of v_arg in
       buf_add b ("(Lg_rt.dyn_map_of_nest_map (Clj_core.Map.assoc_in " ^ dyn_map_arg (List.nth args 0)
                  ^ " " ^ kw_list ^ " (Clj_core.Map.Leaf " ^ boxed ^ ")))")
   | "comp" -> buf_add b ("(fun x__ -> " ^ a 0 ^ " (" ^ a 1 ^ " x__))")
   | "juxt" -> buf_add b ("(fun x__ -> (" ^ a 0 ^ " x__, " ^ a 1 ^ " x__))")
   | "partial" ->
     buf_add b ("(fun x__ -> (" ^ a 0 ^ String.concat "" (List.init (List.length args - 1) (fun i -> " " ^ a (i + 1))) ^ " x__))")
   | "mapcat" -> buf_add b ("(List.concat_map " ^ a 0 ^ " " ^ as_list (List.nth args 1) ^ ")")
   | "interpose" -> buf_add b ("(Lg_rt.interpose " ^ a 0 ^ " " ^ as_list (List.nth args 1) ^ ")")
   | "reverse" ->
     (match coll with
      | `Vec -> buf_add b ("(Clj_core.Vec.of_list (List.rev (Clj_core.Vec.to_list " ^ a 0 ^ ")))")
      | _ -> buf_add b ("(List.rev " ^ a 0 ^ ")"))
   | "distinct" -> buf_add b ("(Lg_rt.distinct " ^ as_list (List.nth args 0) ^ ")")
   | "second" -> buf_add b ("(Lg_rt.second_opt " ^ as_list (List.nth args 0) ^ ")")
   | "last" -> buf_add b ("(Lg_rt.last_opt " ^ as_list (List.nth args 0) ^ ")")
   | "butlast" -> buf_add b ("(Lg_rt.butlast " ^ as_list (List.nth args 0) ^ ")")
   | "min" -> buf_add b ("(Stdlib.min " ^ a 0 ^ " " ^ a 1 ^ ")")
   | "max" -> buf_add b ("(Stdlib.max " ^ a 0 ^ " " ^ a 1 ^ ")")
   | "every?" -> buf_add b ("(List.for_all " ^ a 0 ^ " " ^ as_list (List.nth args 1) ^ ")")
   | "some" -> buf_add b ("(List.exists " ^ a 0 ^ " " ^ as_list (List.nth args 1) ^ ")")
   | "take-while" -> buf_add b ("(Lg_rt.take_while " ^ a 0 ^ " " ^ as_list (List.nth args 1) ^ ")")
   | "drop-while" -> buf_add b ("(Lg_rt.drop_while " ^ a 0 ^ " " ^ as_list (List.nth args 1) ^ ")")
   | "zipmap" -> buf_add b ("(Clj_core.Map.of_list (List.combine " ^ as_list (List.nth args 0) ^ " " ^ as_list (List.nth args 1) ^ "))")
   | "sort" ->
     if List.length args = 2 then buf_add b ("(List.sort " ^ a 0 ^ " " ^ as_list (List.nth args 1) ^ ")")
     else buf_add b ("(List.sort Stdlib.compare " ^ as_list (List.nth args 0) ^ ")")
   | "sort-by" -> buf_add b ("(List.sort (fun a b -> Stdlib.compare (" ^ a 0 ^ " a) (" ^ a 0 ^ " b)) " ^ as_list (List.nth args 1) ^ ")")
   | "group-by" -> buf_add b ("(Lg_rt.group_by " ^ a 0 ^ " " ^ as_list (List.nth args 1) ^ ")")
   | "frequencies" -> buf_add b ("(Lg_rt.frequencies " ^ as_list (List.nth args 0) ^ ")")
   | "swap!" -> buf_add b ("(Clj_core.Atom.swap_bang " ^ a 0 ^ " " ^ a 1 ^ ")")
   | "some?" -> buf_add b ("(" ^ a 0 ^ " <> None)")
   | "none?" -> buf_add b ("(" ^ a 0 ^ " = None)")
   | _ -> buf_add b ("(failwith \"unhandled builtin " ^ name ^ "\")"))

  end

and emit_apply args =
  let f = arg_str (List.nth args 0) and xs = arg_str (List.nth args 1) in
  match (List.nth args 0).desc with
  | EBuiltin ("+" | "+." | "*" | "*." as op) ->
    (* variadic arithmetic: (apply + xs) folds *)
    let o = if String.contains op '.' then "( " ^ op ^ " )" else "( " ^ op ^ " )" in
    let z = if String.contains op '.' then "0." else (if op = "*" then "1" else "0") in
    "(List.fold_left " ^ o ^ " " ^ z ^ " " ^ xs ^ ")"
  | EBuiltin ("-" | "-." | "/" | "/." as op) ->
    let o = "( " ^ op ^ " )" in
    let z = if String.contains op '.' then "0." else "0" in
    "(match " ^ xs ^ " with [] -> " ^ z ^ " | x :: r -> List.fold_left " ^ o ^ " x r)"
  | _ ->
  (match repr (List.nth args 0).ety with
  | TFun (ts, _) ->
    let n = List.length ts in
    let last_is_list = match repr (List.nth ts (n - 1)) with TList _ -> true | _ -> false in
    if last_is_list && n >= 2 then
      "(match " ^ xs ^ " with "
      ^ String.concat "" (List.init (n - 1) (fun i -> Printf.sprintf "a%d :: " i))
      ^ "rest -> " ^ f ^ " "
      ^ String.concat " " (List.init (n - 1) (fun i -> Printf.sprintf "a%d" i))
      ^ " rest | _ -> failwith \"apply: arity\")"
    else
      "(match " ^ xs ^ " with ["
      ^ String.concat "; " (List.init n (fun i -> Printf.sprintf "a%d" i))
      ^ "] -> " ^ f ^ " "
      ^ String.concat " " (List.init n (fun i -> Printf.sprintf "a%d" i))
      ^ " | _ -> failwith \"apply: arity\")"
  | _ -> "(failwith \"apply\")")

and emit_builtin_value name =
  match name with
  | "+" -> "( + )" | "+." -> "( +. )" | "-" -> "( - )" | "-." -> "( -. )"
  | "*" -> "( * )" | "*." -> "( *. )" | "/" -> "( / )" | "/." -> "( /. )"
  | "=" -> "( = )" | "not=" -> "( <> )" | "<" -> "( < )" | "<=" -> "( <= )"
  | ">" -> "( > )" | ">=" -> "( >= )" | "not" -> "not" | "identity" -> "(fun x -> x)"
  | "inc" -> "(fun x -> x + 1)" | "dec" -> "(fun x -> x - 1)" | "abs" -> "abs"
  | "mod" -> "(fun a b -> a mod b)" | "constantly" -> "(fun x _ -> x)"
  | "cons" -> "(fun a l -> a :: l)"
  | "first" -> "(function [] -> None | x :: _ -> Some x)"
  | "rest" -> "(function [] -> [] | _ :: t -> t)"
  | "map" -> "List.map" | "filter" -> "List.filter" | "reduce" | "fold" -> "List.fold_left"
  | "vec" -> "Clj_core.Vec.of_list" | "count" -> "List.length" | "empty?" -> "(function [] -> true | _ -> false)"
  | "str" -> "(fun _ -> \"\")" | "println" -> "print_endline" | "print" -> "print_string"
  | "atom" -> "Clj_core.Atom.atom" | "deref" -> "Clj_core.Atom.deref"
  | "reset!" -> "Clj_core.Atom.reset_bang" | "swap!" -> "Clj_core.Atom.swap_bang"
  | "comp" -> "(fun f g x -> f (g x))" | "juxt" -> "(fun f g x -> (f x, g x))"
  | "mapcat" -> "List.concat_map" | "reverse" -> "List.rev" | "sort" -> "List.sort"
  | "every?" -> "List.for_all" | "some" -> "List.exists" | "min" -> "Stdlib.min" | "max" -> "Stdlib.max"
  | "keys" -> "(fun m -> List.of_seq (Clj_core.Map.keys m))" | "vals" -> "(fun m -> List.of_seq (Clj_core.Map.vals m))"
  | _ -> "(fun _ -> failwith \"builtin as value: " ^ name ^ "\")"

let emit_topdef b (d : topdef) =
  buf_add b "let ";
  (match d.tmode with Local -> buf_add b "(* @local *) " | Owned -> buf_add b "(* @owned *) " | Shared -> ());
  let rec_flag = match d.texpr.desc with EFun _ -> "rec " | _ -> "" in
  buf_add b rec_flag;
  buf_add b (munge d.tname);
  buf_add b " = ";
  emit_expr b d.texpr;
  buf_add b "\n"

(* Consecutive defs named `x__a<N>` are one multi-arity fn; emit them as a
   single `let rec .. and ..` group so arities can call each other. *)
let arity_root n =
  let ln = String.length n in
  let rec suffix_ok i =
    i = ln || (n.[i] >= '0' && n.[i] <= '9' && suffix_ok (i + 1))
  in
  let rec find i =
    if i > ln - 3 then None
    else if n.[i] = '_' && n.[i + 1] = '_' && n.[i + 2] = 'a' && i + 3 < ln && suffix_ok (i + 3)
    then Some (String.sub n 0 i)
    else find (i + 1)
  in
  find 0

let emit_def_group b ds =
  match ds with
  | [] -> ()
  | [ d ] -> emit_topdef b d
  | ds ->
    buf_add b "let rec ";
    List.iteri
      (fun i d ->
        if i > 0 then buf_add b " and ";
        buf_add b (munge d.tname);
        buf_add b " = ";
        emit_expr b d.texpr)
      ds;
    buf_add b "\n"

let emit_module b (m : modl) =
  cur_mod := m.ocaml_name;
  buf_add b ("module " ^ m.ocaml_name ^ " = struct\n");
  let rec groups acc = function
    | [] -> List.rev acc
    | d :: rest ->
      (match arity_root d.tname with
       | Some root ->
         let rec take acc2 = function
           | d2 :: tl when arity_root d2.tname = Some root -> take (d2 :: acc2) tl
           | tl -> (List.rev acc2, tl)
         in
         let same, rest' = take [] rest in
         groups ((d :: same) :: acc) rest'
       | None -> groups ([ d ] :: acc) rest)
  in
  List.iter (emit_def_group b) (groups [] m.defs);
  List.iter (fun e -> buf_add b "let () = (ignore ("; emit_expr b e; buf_add b "))\n") m.effects;
  buf_add b "end\n\n"

let emit_program (mods : modl list) : string =
  (match List.find_opt (fun m -> m.iface_only) mods with
   | Some m ->
     failwith ("module " ^ m.mname ^ " has only an .lgi interface — provide a .lg to emit/build")
   | None -> ());
  let b = Buffer.create 8192 in
  buf_add b "(* generated by lg — do not edit *)\n";
  buf_add b ("module Lg_rt = struct\n" ^ Embedded_runtime.lg_rt_src ^ "\nend\n");
  List.iter (emit_module b) mods;
  Buffer.contents b
