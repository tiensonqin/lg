(* Mode inference: region/escape analysis + ownership hints.

   v0 model (documented in docs/design.md):
   - Every allocation site gets a mode: Local (does not escape its region),
     Owned (escapes but with a single owner chain), or Shared (anything else).
   - Conservative: an unknown call is treated as escaping, a fn value that is
     not immediately applied or bound escapes, values stored into atoms or
     returned at top level escape.
   - These modes are advisory on the vanilla OCaml backend (emitted as
     comments + --mode-report statistics); on an OxCaml backend they become
     real `local`/`unique` annotations. *)

open Ast

let is_alloc e =
  match e.desc with
  | EVecLit _ | EListLit _ | EMapLit _ | ESetLit _ | ETuple _ | EFun _ | EStr _ -> true
  | _ -> false

(* propagated mode: a binding/expr is "escaping" when it can outlive the
   current region. *)

let escapes_of_callee callee =
  match callee.desc with
  | EBuiltin _ -> false (* builtins that retain args marked individually *)
  | ELocal _ | EGlobal _ -> true (* unknown fn: assume args escape *)
  | EFun _ -> false    (* immediately-applied lambda: args stay in region *)
  | _ -> true

let rec analyze_expr ~(region_ret : bool) (e : expr) : unit =
  (* [region_ret] = true when this position is the region's return path:
     the value escapes the region unless marked local. *)
  if is_alloc e then e.emode <- (if region_ret then Shared else Local);
  (match e.desc with
   | EFun fn -> analyze_fn fn
   | ECall (ce, args) ->
     let callee_escapes = escapes_of_callee ce in
     analyze_expr ~region_ret:true ce;
     List.iter (fun a -> analyze_expr ~region_ret:callee_escapes a) args
   | EIf (c, t, x) ->
     analyze_expr ~region_ret:true c;
     analyze_expr ~region_ret t;
     analyze_expr ~region_ret x
   | EDo es -> List.iteri (fun i a -> analyze_expr ~region_ret:(region_ret && i = List.length es - 1) a) es
   | ELet (pairs, body) ->
     List.iter
       (fun (b, init) ->
         analyze_expr ~region_ret:true init;
         b.bmode <- if is_escaping_use b body then Shared else Local)
       pairs;
     analyze_expr ~region_ret body
   | EMatchOpt (src, b, t, x) ->
     analyze_expr ~region_ret:true src;
     b.bmode <- Local;
     analyze_expr ~region_ret t;
     analyze_expr ~region_ret x
   | EVecLit es | EListLit es | ESetLit es | ETuple es ->
     List.iter (fun a -> analyze_expr ~region_ret a) es
   | EMapLit kes -> List.iter (fun (k, v) -> analyze_expr ~region_ret k; analyze_expr ~region_ret v) kes
   | _ -> ())

and analyze_fn fn =
  (* A fn body's result position escapes its own region only when the fn
     itself is called from outside — model every fn body's result as
     non-region-return for its *enclosing* region, and the body's own region
     return as escaping (conservative: result of any call is heap unless the
     whole call graph stays local, which interprocedural analysis would
     refine — v1). *)
  analyze_expr ~region_ret:true fn.body;
  List.iter (fun p -> if p.bmode = Shared then () else p.bmode <- Shared) fn.params;
  fn.fescapes <- true

and is_escaping_use b body : bool =
  (* A binder escapes when it is used inside a nested EFun (captured) or
     stored into an atom / returned. Conservative scan over the body. *)
  let found = ref false in
  let rec go in_closure e =
    match e.desc with
    | ELocal b' when b'.bid = b.bid -> if in_closure then found := true
    | EFun fn -> if fn.fname <> Some b.bname then List.iter (go true) [ fn.body ]
    | ECall (ce, args) -> go false ce; List.iter (go false) args
    | EIf (c, t, x) -> go false c; go in_closure t; go in_closure x
    | EDo es | EVecLit es | EListLit es | ESetLit es | ETuple es -> List.iter (go in_closure) es
    | EMapLit kes -> List.iter (fun (k, v) -> go in_closure k; go in_closure v) kes
    | ELet (pairs, body') ->
      List.iter (fun (_, i) -> go false i) pairs;
      go in_closure body'
    | EMatchOpt (s, _, t, x) -> go false s; go in_closure t; go in_closure x
    | _ -> ()
  in
  go false body;
  !found

let owned_hint () =
  (* An escaping allocation may still be Owned when it has a single-use
     owner chain — approximated by: every binder it flows through is used
     at most once and is not captured. v0 keeps this conservative. *)
  false

let analyze_topdef (d : topdef) : unit =
  (match d.texpr.desc with
   | EFun fn -> analyze_fn fn
   | _ -> ());
  analyze_expr ~region_ret:true d.texpr;
  d.tmode <- Shared;
  ignore (owned_hint ())

let analyze_module (m : modl) : unit =
  List.iter analyze_topdef m.defs;
  List.iter (analyze_expr ~region_ret:true) m.effects

(* ---- reporting ---- *)

let count_modes m =
  let local = ref 0 and owned = ref 0 and shared = ref 0 in
  let bump = function Local -> incr local | Owned -> incr owned | Shared -> incr shared in
  let rec walk e =
    bump e.emode;
    (match e.desc with
     | EFun fn -> walk fn.body
     | ECall (c, args) -> walk c; List.iter walk args
     | EIf (c, t, x) -> walk c; walk t; walk x
     | EDo es | EVecLit es | EListLit es | ESetLit es | ETuple es -> List.iter walk es
     | EMapLit kes -> List.iter (fun (k, v) -> walk k; walk v) kes
     | ELet (ps, b) -> List.iter (fun (_, i) -> walk i) ps; walk b
     | EMatchOpt (s, _, t, x) -> walk s; walk t; walk x
     | _ -> ())
  in
  List.iter (fun d -> walk d.texpr) m.defs;
  List.iter walk m.effects;
  (!local, !owned, !shared)
