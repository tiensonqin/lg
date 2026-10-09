(* Mode inference: region/escape analysis + ownership hints.

   v0 model (documented in docs/design.md):
   - Every expression gets a mode: Local (its value only needs to live in
     the current region), Owned (escapes but with a single owner chain), or
     Shared (anything else). For allocation sites this is the allocation
     mode; for calls it is the result mode.
   - Conservative: an unknown call is treated as escaping, a fn value that is
     not immediately applied or bound escapes, values stored into atoms or
     returned at top level escape.
   - These modes are advisory on the vanilla OCaml backend (emitted as
     comments + --mode-report statistics); on an OxCaml backend they become
     real `local_`/`stack_` annotations. *)

open Ast

let is_alloc e =
  match e.desc with
  | EVecLit _ | EListLit _ | EMapLit _ | ESetLit _ | ETuple _ | EFun _ | EStr _ ->
    (match e.desc with EListLit l -> l <> [] | _ -> true)
  | _ -> false

let rec occurs_anywhere p e =
  match e.desc with
  | ELocal b -> b.bid = p.bid
  | EFun fn -> occurs_anywhere p fn.body
  | ECall (c, args) -> occurs_anywhere p c || List.exists (occurs_anywhere p) args
  | EIf (c, t, x) -> occurs_anywhere p c || occurs_anywhere p t || occurs_anywhere p x
  | EDo es | EVecLit es | EListLit es | ESetLit es | ETuple es -> List.exists (occurs_anywhere p) es
  | EMapLit kes -> List.exists (fun (k, v) -> occurs_anywhere p k || occurs_anywhere p v) kes
  | ELet (ps, b) -> List.exists (fun (_, i) -> occurs_anywhere p i) ps || occurs_anywhere p b
  | EMatchOpt (s, _, t, x) -> occurs_anywhere p s || occurs_anywhere p t || occurs_anywhere p x
  | EVariant (s, _, _, t, x) -> occurs_anywhere p s || occurs_anywhere p t || occurs_anywhere p x
  | EBox e | EUnbox (e, _) | EUnboxOpt (e, _) -> occurs_anywhere p e
  | EOpt (Some e) -> occurs_anywhere p e
  | EDynVec (s, _, t, e) | EDynMap (s, _, t, e) ->
    occurs_anywhere p s || occurs_anywhere p t || occurs_anywhere p e
  | _ -> false

(* does p occur in the fn's result-carrying positions (the value returned
   to callers) — conservative over-approximation *)
let rec occurs_in_result p e =
  match e.desc with
  | EIf (_, t, x) -> occurs_in_result p t || occurs_in_result p x
  | ELet (_, b) -> occurs_in_result p b
  | EDo es -> (match List.rev es with [] -> false | l :: _ -> occurs_in_result p l)
  | EMatchOpt (_, _, t, x) -> occurs_in_result p t || occurs_in_result p x
  | EVariant (_, _, _, t, x) -> occurs_in_result p t || occurs_in_result p x
  | EDynVec (_, _, t, _) | EDynMap (_, _, t, _) -> occurs_in_result p t
  | _ -> occurs_anywhere p e

(* A binder escapes when it is used inside a nested EFun (captured) or
   stored into an atom / returned. Conservative scan over the body. *)
let is_escaping_use b es : bool =
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
    | EVariant (s, _, _, t, x) -> go false s; go in_closure t; go in_closure x
    | EDynVec (s, _, t, x) | EDynMap (s, _, t, x) ->
      go false s; go in_closure t; go in_closure x
    | EOpt (Some e) -> go in_closure e
    | EBox e | EUnbox (e, _) | EUnboxOpt (e, _) -> go false e
    | _ -> ()
  in
  List.iter (go false) es;
  !found

let param_escapes (fn : func) : bool list =
  List.map (fun p -> is_escaping_use p [ fn.body ] || occurs_in_result p fn.body) fn.params

(* ---- clj-core borrow surface (OxCaml build) ----
   Which builtin argument positions accept local values: the callee reads
   the argument but never retains it in its result or stores it. This must
   match the `@ local` declarations on the OxCaml build of clj-core —
   see tools/ox_setup.sh and docs/design.md.

   - All:   every argument position borrows (strict consumer)
   - Only:  only the listed positions borrow
   - Lazy:  the builtin is a lazy seq producer — arguments escape only into
            the returned seq, so they may be local exactly when the call's
            own result need only be local (the emit then selects the
            `Seq.*_local` variant). Anything not listed retains all args. *)
type borrow_spec = All | Only of int list | Lazy

let builtin_borrows : (string, borrow_spec) Hashtbl.t = Hashtbl.create 61
let () =
  List.iter
    (fun (n, s) -> Hashtbl.replace builtin_borrows n s)
    [ (* strict collection readers/consumers — the collection argument *)
      "get", Only [ 0 ]; "nth", Only [ 0 ]; "count", Only [ 0 ];
      "empty?", Only [ 0 ]; "peek", Only [ 0 ]; "first", Only [ 0 ];
      "last", Only [ 0 ]; "second", Only [ 0 ]; "contains?", Only [ 0 ];
      "kw-get", Only [ 0 ]; "get-in", Only [ 0 ]; "select-keys", Only [ 0 ];
      (* strict folds — the callback is invoked but not retained; the
         initial accumulator flows into the result so it is NOT a borrow *)
      "reduce", Only [ 0; 2 ]; "fold", Only [ 0; 2 ];
      "every?", Only [ 0; 1 ]; "some", Only [ 0; 1 ];
      "mapv", Only [ 0 ]; "filterv", Only [ 0 ];
      (* `into`/`vec`/`set` realize — the source is consumed, the
         destination is retained *)
      "vec", Only [ 0 ]; "set", Only [ 0 ];
      "merge", Only [ 1 ];
      "dorun", Only [ 0 ];
      "keys", Only [ 0 ]; "vals", Only [ 0 ];
      "re-seq", Only [ 0; 1 ]; "re-split", Only [ 0; 1 ];
      "re-find", Only [ 0 ]; "re-matches", Only [ 0 ];
      (* pure numeric/predicate readers *)
      "inc", All; "dec", All; "zero?", All; "pos?", All; "neg?", All;
      "even?", All; "odd?", All; "deref", All; "some?", All; "none?", All;
      (* string readers *)
      "subs", Only [ 0 ]; "split", Only [ 0; 1 ]; "join", Only [ 0; 1 ];
      "trim", Only [ 0 ]; "triml", Only [ 0 ]; "trimr", Only [ 0 ];
      "upper-case", Only [ 0 ]; "lower-case", Only [ 0 ]; "blank?", Only [ 0 ];
      "includes?", Only [ 0; 1 ]; "starts-with?", Only [ 0; 1 ];
      "ends-with?", Only [ 0; 1 ]; "re-find", Only [ 0 ];
      "re-matches", Only [ 0 ];
      (* structural equality reads both sides *)
      "=", Only [ 0; 1 ]; "not=", Only [ 0; 1 ];
      (* lazy seq producers — args escape only as far as the result seq *)
      "map", Lazy; "filter", Lazy; "remove", Lazy; "mapcat", Lazy;
      "keep", Lazy; "filter-map", Lazy; "map-indexed", Lazy;
      "take", Lazy; "drop", Lazy; "take-while", Lazy; "drop-while", Lazy;
      "take-nth", Lazy; "rest", Lazy; "next", Lazy; "cons", Lazy;
      "concat", Lazy; "interleave", Lazy; "interpose", Lazy;
      "partition", Lazy; "partition-all", Lazy; "nthrest", Lazy;
      "reductions", Lazy; "dedupe", Lazy;
      "lazy-seq", Lazy; "range", Lazy;
      "drop-last", Lazy; "not-empty", Lazy; "seq", Lazy;
      (* element-flow: arg is local iff the result is *)
      "take-last", Lazy; "butlast", Lazy; "sort", Lazy; "sort-by", Lazy;
      "reverse", Lazy; "doall", Lazy;
      (* collection constructors: elements are stored in the result — they
         escape exactly as far as the result does *)
      "list", Lazy; "vector", Lazy; "hash-map", Lazy; "hash-set", Lazy ]

(* lazy seq producers that have a `Seq.<name>_local` variant in the OxCaml
   clj-core build (result is `'a t @ local`). Emit picks the variant only
   when the call's own emode is Local. *)
let local_seq_fns : (string, string) Hashtbl.t = Hashtbl.create 31
let () =
  List.iter
    (fun (n, v) -> Hashtbl.replace local_seq_fns n v)
    [ "map", "Clj_core.Seq.map_local"; "filter", "Clj_core.Seq.filter_local";
      "remove", "Clj_core.Seq.remove_local"; "mapcat", "Clj_core.Seq.mapcat_local";
      "keep", "Clj_core.Seq.filter_map_local";
      "filter-map", "Clj_core.Seq.filter_map_local";
      "map-indexed", "Clj_core.Seq.mapi_local";
      "take", "Clj_core.Seq.take_local"; "drop", "Clj_core.Seq.drop_local";
      "take-while", "Clj_core.Seq.take_while_local";
      "drop-while", "Clj_core.Seq.drop_while_local";
      "take-nth", "Clj_core.Seq.take_nth_local"; "rest", "Clj_core.Seq.rest_local";
      "next", "Clj_core.Seq.next_local"; "cons", "Clj_core.Seq.cons_local";
      "concat", "Clj_core.Seq.concat_local"; "interleave", "Clj_core.Seq.interleave_local";
      "interpose", "Clj_core.Seq.interpose_local";
      "partition", "Clj_core.Seq.partition_local";
      "partition-all", "Clj_core.Seq.partition_all_local";
      "nthrest", "Clj_core.Seq.nthrest_local"; "reductions", "Clj_core.Seq.reductions_local";
      "dedupe", "Clj_core.Seq.dedupe_local";
      "iterate", "Clj_core.Seq.iterate_local";
      "repeat", "Clj_core.Seq.repeat_local"; "repeatedly", "Clj_core.Seq.repeatedly_local";
      "range", "Clj_core.Seq.range_local";
      "drop-last", "Clj_core.Seq.drop_last_local";
      "lazy-seq", "Clj_core.Seq.lazy_seq_local";
      "ints", "Clj_core.Seq.ints_local" ]

(* `local_` parameters emitted on defns, keyed "Ocaml_mod.munged_name" ->
   per-param bool. Filled during emit: callers may pass local values at
   positions marked true. *)
let global_local_params : (string, bool list) Hashtbl.t = Hashtbl.create 31

let arith_builtins =
  [ "+"; "-"; "*"; "/"; "mod"; "abs"; "min"; "max"; "<"; "<="; ">";
    ">="; "="; "<>"; "not"; "neg"; "float"; "int"; "succ"; "pred";
    "float_of_int"; "int_of_float" ]

(* OxCaml lowering aid: may this binder be emitted `local_`?
   Every use of the binder must sit in a position that accepts local
   values — arithmetic/comparison builtin arguments, borrow-annotated
   clj-core arguments, a self-recursive call at the same parameter index
   (whose params are themselves local_), a call to a defn whose parameter
   is annotated local_, an if-condition, a lazy seq producer argument when
   the producer's result is itself local, or a match scrutinee whose bound
   variables stay local. Collection literals that escape, boxing, atoms,
   closure capture, and calls to functions without borrow annotations all
   demand global. *)
let rec local_uses_ok (p : binder) ~(self_b : binder option) ~(self_name : string option)
    ~(pindex : int) (body : expr) : bool =
  let bad = ref false in
  let callee_is_self ce =
    match ce.desc with
    | ELocal b' -> (match self_b with Some sb -> b'.bid = sb.bid | None -> false)
    | EGlobal (_, _, lgn) -> self_name = Some lgn
    | _ -> false
  in
  let arg_ok ce i e_call =
    match ce.desc with
    | EBuiltin n ->
      List.mem n arith_builtins
      || (match Hashtbl.find_opt builtin_borrows n with
          | Some All -> true
          | Some (Only ix) -> List.mem i ix
          | Some Lazy -> e_call.emode = Local
          | None -> false)
    | EGlobal (m, n, _) ->
      (callee_is_self ce && i = pindex)
      || (match Hashtbl.find_opt global_local_params (m ^ "." ^ n) with
          | Some pl -> (match List.nth_opt pl i with Some x -> x | None -> false)
          | None -> false)
    | EFun fn ->
      (* immediately-applied lambda: the argument flows into a param that
         is itself only locally used *)
      (match List.nth_opt fn.params i with
       | Some lp ->
         local_uses_ok lp ~self_b:fn.fself ~self_name:fn.fname ~pindex:i fn.body
       | None -> false)
    | _ -> false
  in
  let rec go safe_ctx e =
    if !bad then ()
    else
      match e.desc with
      | ELocal b' when b'.bid = p.bid -> if not safe_ctx then bad := true
      | EFun fn ->
        (* capture of a local would store it in a heap closure *)
        if occurs_anywhere p fn.body then bad := true
      | ECall (ce, args) ->
        if occurs_anywhere p ce then bad := true
        else List.iteri (fun i a -> go (arg_ok ce i e) a) args
      | EIf (c, t, x) -> go true c; go false t; go false x
      | EDo es -> List.iter (go false) es
      | ELet (pairs, b) ->
        List.iter (fun (_, i) -> go false i) pairs;
        go false b
      | EMatchOpt (s, bd, t, x) ->
        (* the scrutinee is only read, but its bound component must itself
           stay local for the match to accept a local scrutinee *)
        (if occurs_anywhere p s then (
           go true s;
           if not (local_uses_ok bd ~self_b:None ~self_name:None ~pindex:(-1) t)
           then bad := true)
         else go false s);
        go false t; go false x
      | EVariant (s, _, bs, t, x) ->
        (if occurs_anywhere p s then (
           go true s;
           if
             not
               (List.for_all
                  (fun bd ->
                    local_uses_ok bd ~self_b:None ~self_name:None ~pindex:(-1) t)
                  bs)
           then bad := true)
         else go false s);
        go false t; go false x
      | EDynVec (s, bd, t, x) | EDynMap (s, bd, t, x) ->
        (if occurs_anywhere p s then (
           go true s;
           if not (local_uses_ok bd ~self_b:None ~self_name:None ~pindex:(-1) t)
           then bad := true)
         else go false s);
        go false t; go false x
      | _ -> if occurs_anywhere p e then bad := true
  in
  go false body;
  not !bad

(* may a let-binder be emitted `let x @ local`: every use across the rest
   of the let (later inits plus the body) must be a locally-safe position *)
let binder_local_ok (b : binder) (scope : expr list) : bool =
  List.for_all
    (fun e -> local_uses_ok b ~self_b:None ~self_name:None ~pindex:(-1) e)
    scope

(* per-global per-param escape flags, keyed "Ocaml_module.munged_name";
   filled from .lgi files and from analyzing the defining module *)
let global_escapes : (string, bool list) Hashtbl.t = Hashtbl.create 31

let arg_escapes callee =
  match callee.desc with
  | EGlobal (m, n, _) -> Hashtbl.find_opt global_escapes (m ^ "." ^ n)
  | _ -> None

let rec analyze_expr ~(region_ret : bool) (e : expr) : unit =
  (* [region_ret] = true when this position is the region's return path:
     the value escapes the region unless marked local. emode records the
     result: Local = the value here need only be local. *)
  e.emode <- (if region_ret then Shared else Local);
  (match e.desc with
   | EFun fn -> analyze_fn fn
   | ECall (ce, args) ->
     let escs = arg_escapes ce in
     let arg_esc i =
       match escs with
       | Some l -> (match List.nth_opt l i with Some e -> e | None -> true)
       | None ->
         (match ce.desc with
          | EBuiltin n ->
            (match Hashtbl.find_opt builtin_borrows n with
             | Some All -> false
             | Some (Only ix) -> not (List.mem i ix)
             | Some Lazy -> region_ret
             | None -> not (List.mem n arith_builtins))
          | EFun fn ->
            (* immediately-applied lambda: escapes iff the param does *)
            (match List.nth_opt (param_escapes fn) i with
             | Some e -> e
             | None -> true)
          | _ -> true)
     in
     analyze_expr ~region_ret:true ce;
     List.iteri (fun i a -> analyze_expr ~region_ret:(arg_esc i) a) args;
     (* an immediately-applied lambda's params may be annotated local_:
        mark each param whose uses are all borrow-safe *)
     (match ce.desc with
      | EFun fn ->
        List.iteri
          (fun i p ->
            if local_uses_ok p ~self_b:fn.fself ~self_name:fn.fname ~pindex:i fn.body
            then p.bmode <- Local)
          fn.params
      | _ -> ())
   | EIf (c, t, x) ->
     analyze_expr ~region_ret:true c;
     analyze_expr ~region_ret t;
     analyze_expr ~region_ret x
   | EDo es -> List.iteri (fun i a -> analyze_expr ~region_ret:(region_ret && i = List.length es - 1) a) es
   | ELet (pairs, body) ->
     List.iteri
       (fun i (b, init) ->
         let scope = List.map snd (List.filteri (fun j _ -> j > i) pairs) @ [ body ] in
         b.bmode <- (if binder_local_ok b scope then Local else Shared);
         analyze_expr ~region_ret:(b.bmode = Shared) init)
       pairs;
     analyze_expr ~region_ret body
   | EMatchOpt (src, b, t, x) ->
     b.bmode <- (if binder_local_ok b [ t ] then Local else Shared);
     analyze_expr ~region_ret:(b.bmode = Shared) src;
     analyze_expr ~region_ret t;
     analyze_expr ~region_ret x
   | EVariant (src, _, bs, t, x) ->
     List.iter
       (fun b -> b.bmode <- (if binder_local_ok b [ t ] then Local else Shared))
       bs;
     let esc = List.exists (fun b -> b.bmode = Shared) bs in
     analyze_expr ~region_ret:esc src;
     analyze_expr ~region_ret t;
     analyze_expr ~region_ret x
   | EDynVec (src, b, t, x) | EDynMap (src, b, t, x) ->
     b.bmode <- (if binder_local_ok b [ t ] then Local else Shared);
     analyze_expr ~region_ret:(b.bmode = Shared) src;
     analyze_expr ~region_ret t;
     analyze_expr ~region_ret x
   | EVecLit es | EListLit es | ESetLit es | ETuple es ->
     List.iter (fun a -> analyze_expr ~region_ret a) es
   | EMapLit kes -> List.iter (fun (k, v) -> analyze_expr ~region_ret k; analyze_expr ~region_ret v) kes
   | EBox a | EUnbox (a, _) | EUnboxOpt (a, _) -> analyze_expr ~region_ret:true a
   | EOpt (Some a) -> analyze_expr ~region_ret a
   | _ -> ())

and analyze_fn fn =
  analyze_expr ~region_ret:true fn.body;
  List.iteri
    (fun i p ->
      (* anonymous lambdas only get `local_` params at call sites (marked in
         the ECall/EFun arm below); named fns mark here *)
      p.bmode <-
        (if fn.fname <> None
            && local_uses_ok p ~self_b:fn.fself ~self_name:fn.fname ~pindex:i fn.body
         then Local
         else Shared))
    fn.params;
  fn.fescapes <- true

(* globals and local binders referenced as first-class values (outside a
   callee position) — such functions cannot carry `local_` params because
   higher-order consumers (Seq.map, Vec.map, ...) expect global-param
   callbacks. Names + binder ids tracked separately. *)
let value_ref_names : (string, unit) Hashtbl.t = Hashtbl.create 31
let value_ref_bids : (int, unit) Hashtbl.t = Hashtbl.create 31

let rec collect_value_refs e =
  match e.desc with
  | ELocal b -> Hashtbl.replace value_ref_bids b.bid ()
  | EGlobal (_, n, _) -> Hashtbl.replace value_ref_names n ()
  | EFun fn -> collect_value_refs fn.body
  | ECall (ce, args) ->
    (* the callee itself is a callee-position use; args are value uses *)
    (match ce.desc with EFun fn -> collect_value_refs fn.body | _ -> ());
    List.iter collect_value_refs args
  | EIf (c, t, x) -> collect_value_refs c; collect_value_refs t; collect_value_refs x
  | EDo es | EVecLit es | EListLit es | ESetLit es | ETuple es ->
    List.iter collect_value_refs es
  | EMapLit kes -> List.iter (fun (k, v) -> collect_value_refs k; collect_value_refs v) kes
  | ELet (pairs, b) ->
    List.iter (fun (_, i) -> collect_value_refs i) pairs;
    collect_value_refs b
  | EMatchOpt (s, _, t, x) | EDynVec (s, _, t, x) | EDynMap (s, _, t, x) ->
    collect_value_refs s; collect_value_refs t; collect_value_refs x
  | EVariant (s, _, _, t, x) -> collect_value_refs s; collect_value_refs t; collect_value_refs x
  | EBox e | EUnbox (e, _) | EUnboxOpt (e, _) -> collect_value_refs e
  | EOpt (Some e) -> collect_value_refs e
  | _ -> ()

let collect_value_refs_program (mods : modl list) =
  Hashtbl.reset value_ref_names;
  Hashtbl.reset value_ref_bids;
  List.iter
    (fun m ->
      List.iter
        (fun t ->
          match t with
          | TDef d -> collect_value_refs d.texpr
          | _ -> ())
        m.tops;
      List.iter collect_value_refs m.effects)
    mods

let record_escapes ocaml_mod (d : topdef) =
  match d.texpr.desc with
  | EFun fn ->
    Hashtbl.replace global_escapes (ocaml_mod ^ "." ^ Infer.munge d.tname) (param_escapes fn)
  | _ -> ()

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
  List.iter
    (function
     | TDef d ->
       analyze_topdef d;
       (* record this def's escape/local params before later tops are
          analyzed so their uses of it are classified correctly *)
       (match d.texpr.desc with
        | EFun fn ->
          Hashtbl.replace global_escapes
            (m.ocaml_name ^ "." ^ Infer.munge d.tname)
            (param_escapes fn);
          Hashtbl.replace global_local_params
            (m.ocaml_name ^ "." ^ Infer.munge d.tname)
            (List.map (fun p -> p.bmode = Local) fn.params)
        | _ -> ())
     | TEffect e -> analyze_expr ~region_ret:true e
     | _ -> ())
    m.tops;
  List.iter (analyze_expr ~region_ret:true) m.effects

(* ---- reporting ---- *)

let count_modes m =
  let local = ref 0 and owned = ref 0 and shared = ref 0 in
  let bump = function Local -> incr local | Owned -> incr owned | Shared -> incr shared in
  let rec walk e =
    if is_alloc e then bump e.emode;
    (match e.desc with
     | EFun fn -> walk fn.body
     | ECall (c, args) -> walk c; List.iter walk args
     | EIf (c, t, x) -> walk c; walk t; walk x
     | EDo es | EVecLit es | EListLit es | ESetLit es | ETuple es -> List.iter walk es
     | EMapLit kes -> List.iter (fun (k, v) -> walk k; walk v) kes
     | ELet (ps, b) -> List.iter (fun (_, i) -> walk i) ps; walk b
     | EMatchOpt (s, _, t, x) -> walk s; walk t; walk x
     | EVariant (s, _, _, t, x) -> walk s; walk t; walk x
     | EDynVec (s, _, t, x) | EDynMap (s, _, t, x) -> walk s; walk t; walk x
     | EBox a | EUnbox (a, _) | EUnboxOpt (a, _) | EOpt (Some a) -> walk a
     | _ -> ())
  in
  List.iter
    (function TDef d -> walk d.texpr | TEffect e -> walk e | _ -> ())
    m.tops;
  List.iter walk m.effects;
  (!local, !owned, !shared)
