(* OCaml emitter: typed AST -> OCaml source text.
   Runtime targets: Clj_core.{Vec,Map,Set,List,Atom,Keyword,Symbol} and the
   embedded Lg_rt prelude (printers + helpers). *)

open Ast
open Typ
open Infer

(* TImplicit is invisible downstream: binders, args and printers see
   the wrapped dictionary type *)
(* leftover free vars are emitted as `any` — dynamic at the OCaml
   boundary (printer falls back to str_dyn, call sites box literals) *)
let repr t = match Typ.dimp t with TVar _ -> TAny | u -> u

let uid_ctr = ref 0
let fresh_uid () = incr uid_ctr; !uid_ctr

(* when set, emit OxCaml mode annotations. The conservative lowering:
   `local_` is emitted on non-escaping params of primitive type — those
   are the only annotations OxCaml accepts against un-annotated libraries
   (local values cannot flow into global-parameter functions, and no
   clj-core API declares @ local params yet). `stack_`/`unique_` are kept
   as comments: stack_ only wraps direct allocation sites — never a call
   like Vec.of_list — and the persistent structures it would mark have no
   local-accepting consumers anyway; unique_ has no expression-level
   syntax in OxCaml 5.2 and persistent collections are inherently aliased
   rather than unique. *)
let oxcaml = ref false

(* primitive (unboxed-or-opaque-scalar) types whose values may safely be
   local_ — arithmetic/comparison externals accept local arguments *)
let is_prim_ty t =
  match Typ.repr t with
  | Typ.TInt | Typ.TFloat | Typ.TBool | Typ.TChar -> true
  | _ -> false

(* top-level defn names of the module being emitted — `local_` params
   annotate only these: any other EFun may flow into a higher-order call
   expecting global-param callbacks, and a nested `fn` could alias a
   defn's name *)
let topdef_names : (string, unit) Hashtbl.t = Hashtbl.create 31
let melange = ref false

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

(* declared signature of every emitted defn, keyed "Mod/munged_name" —
   emit_call consults it so conv boxes toward the callee's own boundary
   (free scheme vars -> dyn) instead of the call-site instantiation. *)
let sig_tbl : (string, ty) Hashtbl.t = Hashtbl.create 97

(* variant ctor lookup: "Mod.munged" -> ("Mod.Ctor", nfields) *)
let cur_v : (string, string * int) Hashtbl.t = Hashtbl.create 16

(* lg defvariant ctors plus ocaml.* ctors resolved from cmi signatures;
   an ocaml ctor's qualified name is "<unit>.<name>" — its real
   compilation unit *)
let find_ctor m n =
  match Hashtbl.find_opt cur_v (m ^ "/" ^ n) with
  | Some r -> Some r
  | None ->
    (match Hashtbl.find_opt Infer.ocaml_ctors (m ^ "/" ^ n) with
     | Some k -> Some (m ^ "." ^ n, k)
     | None -> None)

(* qualify a "Mod.Ctor" name: bare inside its own module *)
let ctor_qual q =
  let pfx = !cur_mod ^ "." in
  if String.length q > String.length pfx && String.sub q 0 (String.length pfx) = pfx
  then String.sub q (String.length pfx) (String.length q - String.length pfx)
  else q

(* `~local` marks a position whose value need only be local — borrow
   positions in calls, `let x @ local` inits, branch/scrutinee spines.
   Combined with e.emode = Local it licenses `stack_` on direct allocation
   sites and `*_local` collection twins on local arguments. *)

(* fbip accumulator state: a self-recursive fn can thread one collection
   param through `let rec` as a mutable builder (see the FBIP block below);
   these tables describe the fn being emitted, if any *)
let fbip_params : (int, [ `Vec | `Map | `Set ]) Hashtbl.t = Hashtbl.create 7
let fbip_self = ref (-1)   (* fself bid of the fbip fn currently emitted *)
let fbip_pidx = ref (-1)   (* its builder param's position *)
let fbip_pb : Ast.binder option ref = ref None

(* OCaml `# line "file"` directives give the emitted .ml a source map
   back to .lg locations: ocamlc/ocamlopt attribute type errors and
   warnings to the lg line that produced the code. A directive must
   appear at the start of a line — `line_dir` emits one (with its own
   newline) whenever the source line advances, so expressions inside
   parentheses are mapped too. `last_dir_line` dedupes same-line
   repeats; it is reset per module. *)
let last_dir_line = ref (-1)

let line_dir b (l : Syntax.loc) =
  if l.Syntax.line > 0 && l.Syntax.line <> !last_dir_line then begin
    last_dir_line := l.Syntax.line;
    buf_add b (Printf.sprintf "\n# %d \"%s\"\n" l.Syntax.line (String.escaped l.Syntax.file))
  end

let rec emit_expr ?(local = false) (b : Buffer.t) (e : expr) : unit =
  line_dir b e.loc;
  match e.desc with
  | EInt i -> buf_add b (if i < 0 then "(" ^ string_of_int i ^ ")" else string_of_int i)
  | EFloat x -> buf_add b (if x < 0. then "(" ^ ocaml_float x ^ ")" else ocaml_float x)
  | EBool x -> buf_add b (string_of_bool x)
  | EChar c -> buf_add b (ocaml_char c)
  | EStr s -> buf_add b (ocaml_str s)
  | EKeyword k -> buf_add b (kw_expr k)
  | ESymbol s -> buf_add b (sym_expr s)
  | ENil -> buf_add b (if is_any e.ety then "(Lg_rt.DUnit)" else "()")
  | ELocal bd ->
    (match Hashtbl.find_opt fbip_params bd.bid with
     | Some kind -> fbip_freeze b kind (sanitize bd.bname ^ "__" ^ string_of_int bd.bid)
     | None -> buf_add b (sanitize bd.bname ^ "__" ^ string_of_int bd.bid))
  | EGlobal (m, n, _) ->
    (match find_ctor m n with
     | Some (q, 0) -> buf_add b (ctor_qual q)
     | Some (q, k) ->
       let xs = List.init k (fun i -> "__x" ^ string_of_int i) in
       buf_add b ("(fun " ^ (if k = 1 then "__x0" else "(" ^ String.concat ", " xs ^ ")") ^ " -> " ^ ctor_qual q ^ " " ^ (if k = 1 then "__x0" else "(" ^ String.concat ", " xs ^ ")") ^ ")")
     | None -> if m = !cur_mod then buf_add b n else buf_add b (m ^ "." ^ n))
  | EBuiltin name -> buf_add b (emit_builtin_value name e.ety)
  | EFun fn ->
    (match fn.Ast.fself, (if !oxcaml then None else fbip_pick fn) with
     | Some sb, Some (pidx, kind) ->
       (* fbip accumulator: the let rec's param is a mutable builder;
          self-calls mutate it in place, results freeze it, and the fn
          value is a wrapper that converts the caller's collection in *)
       let pb = List.nth fn.Ast.params pidx in
       Hashtbl.replace fbip_params pb.Ast.bid kind;
       buf_add b ("(let rec " ^ sanitize sb.bname ^ "__" ^ string_of_int sb.bid ^ " = (fun ");
       List.iter
         (fun p -> buf_add b (sanitize p.Ast.bname ^ "__" ^ string_of_int p.Ast.bid ^ " "))
         fn.Ast.params;
       buf_add b "-> ";
       let saved_self, saved_pidx, saved_pb = !fbip_self, !fbip_pidx, !fbip_pb in
       fbip_self := sb.bid; fbip_pidx := pidx; fbip_pb := Some pb;
       (match repr e.ety with
        | TFun (_, r) -> buf_add b (conv r fn.body.ety (arg_str fn.body))
        | _ -> emit_expr b fn.body);
       fbip_self := saved_self; fbip_pidx := saved_pidx; fbip_pb := saved_pb;
       Hashtbl.remove fbip_params pb.Ast.bid;
       buf_add b ") in (fun ";
       List.iter
         (fun p -> buf_add b (sanitize p.Ast.bname ^ "__" ^ string_of_int p.Ast.bid ^ " "))
         fn.Ast.params;
       buf_add b ("-> " ^ sanitize sb.bname ^ "__" ^ string_of_int sb.bid);
       List.iteri
         (fun i p ->
           buf_add b " ";
           let nm = sanitize p.Ast.bname ^ "__" ^ string_of_int p.Ast.bid in
           if i = pidx then fbip_of b kind nm else buf_add b nm)
         fn.Ast.params;
       buf_add b "))"
     | _ ->
    let stk = local && e.emode = Ast.Local && !oxcaml && fn.Ast.fself = None in
    if stk then buf_add b "(stack_ ";
    (match fn.Ast.fself with
     | Some sb ->
       buf_add b ("(let rec " ^ sanitize sb.bname ^ "__" ^ string_of_int sb.bid ^ " = ")
     | None -> ());
    buf_add b "(fun ";
    let fn_may_local =
      match fn.Ast.fname with
      | Some n -> Hashtbl.mem topdef_names n && not (Hashtbl.mem Modes.value_ref_names n)
      | None -> true (* anonymous lambdas get bmode=Local only at call sites *)
    in
    let pesc =
      if !oxcaml && fn_may_local then
        List.map (fun p -> p.Ast.bmode = Ast.Local) fn.params
      else []
    in
    (match fn.Ast.fname with
     | Some n ->
       Hashtbl.replace Modes.global_local_params (!cur_mod ^ "." ^ munge n) pesc
     | None -> ());
    List.iteri
      (fun i p ->
        if i < List.length pesc && List.nth pesc i then buf_add b "(";
        buf_add b (sanitize p.bname ^ "__" ^ string_of_int p.bid);
        if i < List.length pesc && List.nth pesc i then buf_add b " @ local) " else buf_add b " ")
      fn.params;
    (match fn.variadic with Some p -> buf_add b (sanitize p.bname ^ "__" ^ string_of_int p.bid ^ " ") | None -> ());
    if fn.params = [] && fn.variadic = None then buf_add b "() ";
    buf_add b "-> ";
    (* a self-recursive fn's callers share the *binder's* return var
       (sb.bty), which may resolve differently from the EFun node's own
       ety ret (e.g. a match arm pinched it to unit while the body
       still emits dyn). Convert the body to what callers see — that is
       the sig emit_call consults via `sret`. *)
    let ret_ty =
      match fn.Ast.fself with
      | Some sb -> sb.Ast.bty
      | None -> e.ety
    in
    (match repr ret_ty with
     | TFun (_, r) -> buf_add b (conv r fn.body.ety (arg_str fn.body))
     | _ -> emit_expr b fn.body);
    buf_add b ")";
    if stk then buf_add b ")";
    (match fn.Ast.fself with
     | Some sb -> buf_add b (" in " ^ sanitize sb.bname ^ "__" ^ string_of_int sb.bid ^ ")")
     | None -> ()))
  | ECall (ce, args) -> emit_call b e ce args
  | EOCamlCall (ce, oargs) ->
    (* direct OCaml call: positional args first, then ~lbl:v — optional
       params supplied by value emit the same (~opt:v) *)
    buf_add b "(";
    emit_expr b ce;
    List.iter
      (fun oa ->
        match oa with
        | OPos (pty, a) ->
          buf_add b (" " ^ conv pty a.ety (arg_str ~local:false a))
        | OLbl (k, pty, a) | OOpt (k, pty, a) ->
          buf_add b (" ~" ^ k ^ ":(" ^ conv pty a.ety (arg_str ~local:false a) ^ ")"))
      oargs;
    buf_add b ")"
  | EIf (c, t, x) ->
    (* cond: bool passes through, `any` goes through dyn truthiness, and
       any other statically typed value is truthy but must still be
       evaluated for order *)
    (match repr c.ety with
     | TAny -> buf_add b "(if (Lg_rt.dyn_truthy "
     | TBool -> buf_add b "(if "
     | _ -> buf_add b "(if (let __ = ");
    emit_expr b c;
    (match repr c.ety with
     | TAny -> buf_add b ")"
     | TBool -> ()
     | _ -> buf_add b " in true)");
    buf_add b " then ";
    buf_add b (conv e.ety t.ety (arg_str ~local:(local && conv e.ety t.ety "x" = "x") t));
    buf_add b " else ";
    buf_add b (conv e.ety x.ety (arg_str ~local:(local && conv e.ety x.ety "x" = "x") x)); buf_add b ")"
  | EDo es ->
    (* every element but the last runs for effect only; the last is the
       do's value and must not be wrapped in ignore *)
    buf_add b "(";
    List.iteri (fun i a ->
        if i > 0 then buf_add b "; ";
        if i < List.length es - 1 then buf_add b "ignore (";
        emit_expr ~local:(local && i = List.length es - 1) b a;
        if i < List.length es - 1 then buf_add b ")")
      es;
    buf_add b ")"
  | ELet (pairs, body) -> emit_let_binds ~local b pairs body
  | ETuple es ->
    let stk = local && e.emode = Ast.Local && !oxcaml in
    let tys = match repr e.ety with TTuple ts -> ts | _ -> List.map (fun _ -> TAny) es in
    if stk then buf_add b "(stack_ ";
    buf_add b "("; List.iteri (fun i a -> if i > 0 then buf_add b ", "; buf_add b (conv (List.nth tys i) a.ety (arg_str ~local:(local && conv (List.nth tys i) a.ety "x" = "x") a))) es; buf_add b ")";
    if stk then buf_add b ")"
  | EVecLit es ->
    let el = match repr e.ety with TVec a -> a | _ -> TAny in
    let stk = local && e.emode = Ast.Local && !oxcaml in
    buf_add b (if stk then "(Clj_core.Vec.of_list_local (stack_ [" else "(Clj_core.Vec.of_list [");
    List.iteri (fun i x -> if i > 0 then buf_add b "; "; emit_elem b el x) es;
    buf_add b (if stk then "]))" else "])");
  | EListLit es ->
    let el = match repr e.ety with TList a -> a | _ -> TAny in
    let stk = local && e.emode = Ast.Local && !oxcaml && es <> [] in
    if stk then buf_add b "(stack_ ";
    buf_add b "[";
    List.iteri (fun i x -> if i > 0 then buf_add b "; "; emit_elem b el x) es;
    buf_add b "]";
    if stk then buf_add b ")"
  | EMapLit kes ->
    let kt, vt = match repr e.ety with TMap (k, v) -> (k, v) | _ -> (TAny, TAny) in
    (* Map.t carries a global comparator field — local maps cannot be
       built, so the spine is always a global list *)
    buf_add b "(Clj_core.Map.of_list [";
    List.iteri
      (fun i (k, v) ->
        if i > 0 then buf_add b "; ";
        buf_add b "("; emit_elem b kt k; buf_add b ", "; emit_elem b vt v; buf_add b ")")
      kes;
    buf_add b "])";
  | ESetLit es ->
    let el = match repr e.ety with TSet a -> a | _ -> TAny in
    buf_add b "(Clj_core.Set.of_list [";
    List.iteri (fun i x -> if i > 0 then buf_add b "; "; emit_elem b el x) es;
    buf_add b "])"
  | EDynVec (se', bd, t, x) ->
    buf_add b "(match "; emit_expr ~local:(se'.emode = Ast.Local) b se'; buf_add b (" with Lg_rt.DVec " ^ sanitize bd.bname ^ "__" ^ string_of_int bd.bid ^ " -> ");
    buf_add b (conv e.ety t.ety (arg_str ~local:(local && conv e.ety t.ety "x" = "x") t)); buf_add b " | _ -> "; buf_add b (conv e.ety x.ety (arg_str ~local:(local && conv e.ety x.ety "x" = "x") x)); buf_add b ")"
  | EDynMap (se', bd, t, x) ->
    buf_add b "(match "; emit_expr ~local:(se'.emode = Ast.Local) b se'; buf_add b (" with Lg_rt.DMap " ^ sanitize bd.bname ^ "__" ^ string_of_int bd.bid ^ " -> ");
    buf_add b (conv e.ety t.ety (arg_str ~local:(local && conv e.ety t.ety "x" = "x") t)); buf_add b " | _ -> "; buf_add b (conv e.ety x.ety (arg_str ~local:(local && conv e.ety x.ety "x" = "x") x)); buf_add b ")"
  | EVariant (se', cname, bs, t, x) ->
    let cq = ctor_qual cname in
    buf_add b "(match "; emit_expr ~local:(se'.emode = Ast.Local) b se';
    (match bs with
     | [] -> buf_add b (" with " ^ cq ^ " -> ")
     | [ b1 ] -> buf_add b (" with " ^ cq ^ " " ^ sanitize b1.bname ^ "__" ^ string_of_int b1.bid ^ " -> ")
     | _ -> buf_add b (" with " ^ cq ^ " (" ^ String.concat ", " (List.map (fun bb -> sanitize bb.bname ^ "__" ^ string_of_int bb.bid) bs) ^ ") -> "));
    buf_add b (conv e.ety t.ety (arg_str ~local:(local && conv e.ety t.ety "x" = "x") t)); buf_add b " | _ -> "; buf_add b (conv e.ety x.ety (arg_str ~local:(local && conv e.ety x.ety "x" = "x") x)); buf_add b ")"
  | ETry (b', catch, fin) -> emit_try b b' catch fin
  | EOpt (Some e) ->
    let stk = local && e.emode = Ast.Local && !oxcaml in
    buf_add b ((if stk then "(stack_ " else "") ^ "(Some " ^ arg_str ~local e ^ ")" ^ (if stk then ")" else ""))
  | EOpt None -> buf_add b "None"
  | EBox e -> buf_add b (box_deep e.ety (arg_str e))
  | EUnbox (e', t') -> buf_add b ("(" ^ unbox_fn t' ^ " " ^ arg_str e' ^ ")")
  | EUnboxOpt (e', t') ->
    buf_add b ("(match " ^ arg_str e' ^ " with Some d -> Some (" ^ unbox_fn t' ^ " d) | None -> None)")
  | EMatchOpt (src, bd, t, x) ->
    if is_any src.ety then begin
      buf_add b "(match "; emit_expr ~local:(src.emode = Ast.Local) b src; buf_add b " with Lg_rt.DOpt (Some ";
      buf_add b (sanitize bd.bname ^ "__" ^ string_of_int bd.bid);
      buf_add b ") -> "; buf_add b (conv e.ety t.ety (arg_str ~local:(local && conv e.ety t.ety "x" = "x") t)); buf_add b " | _ -> "; buf_add b (conv e.ety x.ety (arg_str ~local:(local && conv e.ety x.ety "x" = "x") x)); buf_add b ")"
    end else begin
      buf_add b "(match "; emit_expr ~local:(src.emode = Ast.Local) b src; buf_add b " with Some ";
      buf_add b (sanitize bd.bname ^ "__" ^ string_of_int bd.bid);
      buf_add b " -> "; buf_add b (conv e.ety t.ety (arg_str ~local:(local && conv e.ety t.ety "x" = "x") t)); buf_add b " | None -> "; buf_add b (conv e.ety x.ety (arg_str ~local:(local && conv e.ety x.ety "x" = "x") x)); buf_add b ")"
    end

and emit_try b b' catch fin =
  (* OCaml has no `finally` keyword: Fun.protect runs the cleanup on both
     success and exception, which is exactly finally semantics. catch only
     is a plain try..with; finally wraps the whole thing. *)
  let with_catch () =
    (match catch with
     | Some (bd, h) ->
       buf_add b "(try ";
       emit_expr b b';
       buf_add b " with ";
       buf_add b (sanitize bd.Ast.bname ^ "__" ^ string_of_int bd.Ast.bid);
       buf_add b " -> ";
       emit_expr b h;
       buf_add b ")"
     | None -> emit_expr b b')
  in
  (match fin with
   | Some f ->
     buf_add b "(Fun.protect ~finally:(fun () -> (ignore (";
     emit_expr b f;
     buf_add b "))) (fun () -> ";
     with_catch ();
     buf_add b "))"
   | None -> with_catch ())

and emit_args b es = List.iteri (fun i a -> if i > 0 then buf_add b "; "; emit_expr b a) es
and arg_str ?local e =
  let local = match local with Some l -> l | None -> e.emode = Ast.Local in
  let b = Buffer.create 16 in
  emit_expr ~local b e;
  Buffer.contents b
and emit_call b (e : expr) ce args =
  let ret = e.ety in
  let call_local = !oxcaml && e.emode = Ast.Local in
  let arg_local a =
    match a.desc with
    | Ast.ELocal b -> b.bmode = Ast.Local
    | Ast.EGlobal _ -> false
    | _ -> a.emode = Ast.Local
  in
  match ce.desc with
  | EBuiltin name -> emit_builtin_call ~call_local b ret name args
  | EGlobal (m, n, _) when find_ctor m n <> None ->
    let q, k = match find_ctor m n with Some r -> r | None -> assert false in
    (* variant constructor: a direct allocation site — stack_ when the
       result need only be local *)
    let call_local = call_local && k > 0 in
    (* ctor fields take the declared field type — a (seq t) argument
       into a (list t) field conv-realizes, a concrete arg into an
       'a field boxes just like fn params do *)
    let ftys =
      match repr ce.ety with TFun (ts, _) -> ts | _ -> []
    in
    let carg i a =
      let p = if i < List.length ftys then List.nth ftys i else TAny in
      conv p a.ety (arg_str ~local:(arg_local a) a)
    in
    if call_local then buf_add b "(stack_ ";
    buf_add b
      (match args with
       | [] -> "(" ^ ctor_qual q ^ ")"
       | [ a ] -> "(" ^ ctor_qual q ^ " " ^ carg 0 a ^ ")"
       | _ ->
         "(" ^ ctor_qual q ^ " (" ^
         String.concat ", " (List.mapi carg args) ^ "))");
    if call_local then buf_add b ")"
  | _ ->
    (* box args into dyn when the callee's formal param is `any`. For an
       EGlobal the conv must follow the callee's *stored* signature — its
       free scheme vars emit as `dyn` — not the call-site instantiation
       (which binds those vars to the argument's concrete type and would
       emit an identity where a box is needed). The same applies to the
       call's result: its runtime type is the stored return with vars at
       dyn, so wrap the call in conv from stored-ret to the expected type. *)
    (match ce.desc with
     | EGlobal (m, n, _) when Hashtbl.mem sig_tbl (m ^ "/" ^ n) ->
       let pts, sret =
         (match repr (Hashtbl.find sig_tbl (m ^ "/" ^ n)) with
          | TFun (ts, r) -> (ts, r)
          | _ -> ([], TAny))
       in
       let c = Buffer.create 64 in
       buf_add c "("; emit_expr c ce;
       if args = [] then buf_add c " ()";
       List.iteri
         (fun i a ->
           buf_add c " ";
           let p = if i < List.length pts then List.nth pts i else TAny in
           (* a converted (boxed/unboxed) arg cannot be stack_-allocated *)
           let ident = conv p a.ety "x" = "x" in
           (* stack_ an arg only when the callee borrows it: the
              callee's `(p @ local)` list, when recorded *)
           let pborrows =
             match Hashtbl.find_opt Modes.global_local_params (m ^ "." ^ munge n) with
             | Some ps -> i < List.length ps && List.nth ps i
             | None -> false
           in
           buf_add c (conv p a.ety (arg_str ~local:(ident && pborrows && arg_local a) a)))
         args;
       buf_add c ")";
       buf_add b (conv ret sret (Buffer.contents c))
     | ELocal lb when lb.bid = !fbip_self ->
       (* fbip self-call: the accumulator arg is an in-place update *)
       let pts = match repr ce.ety with TFun (ts, _) -> ts | _ -> [] in
       buf_add b "("; emit_expr b ce;
       if args = [] then buf_add b " ()";
       (match !fbip_pb with
        | Some pb ->
          List.iteri
            (fun i a ->
              buf_add b " ";
              if i = !fbip_pidx && Hashtbl.mem fbip_params pb.Ast.bid then
                fbip_rec_arg b (Hashtbl.find fbip_params pb.Ast.bid) pb a
              else
                let p = if i < List.length pts then List.nth pts i else TAny in
                buf_add b (conv p a.ety (arg_str ~local:false a)))
            args
        | None ->
          List.iteri
            (fun i a ->
              buf_add b " ";
              let p = if i < List.length pts then List.nth pts i else TAny in
              buf_add b (conv p a.ety (arg_str ~local:false a)))
            args);
       buf_add b ")"
     | _ ->
       let pts = match repr ce.ety with TFun (ts, _) -> ts | _ -> [] in
       buf_add b "("; emit_expr b ce;
       (* zero-argument application: OCaml takes unit *)
       if args = [] then buf_add b " ()";
       List.iteri
         (fun i a ->
           buf_add b " ";
           let p = if i < List.length pts then List.nth pts i else TAny in
           (* non-defn callees (vars, fields, closures) take global
              params — never stack_ an argument *)
           buf_add b (conv p a.ety (arg_str ~local:false a)))
         args;
       buf_add b ")");

(* variant ctor lookup: "Mod.munged" -> ("Mod.Ctor", nfields) *)
(* ---- printers for str/println/pr-str ---- *)
and printer_call t e =
  let es = arg_str e in
  match repr t with
  | TInt -> "(Lg_rt.str_int " ^ es ^ ")"
  | TFloat -> "(Lg_rt.str_float " ^ es ^ ")"
  | TBool -> "(Lg_rt.str_bool " ^ es ^ ")"
  | TChar -> "(Lg_rt.str_char " ^ es ^ ")"
  | TString -> "(Lg_rt.str_string " ^ es ^ ")"
  | TKeyword -> "(Lg_rt.str_kw " ^ es ^ ")"
  | TSymbol -> "(Lg_rt.str_sym " ^ es ^ ")"
  | TUnit -> "(Lg_rt.str_unit " ^ es ^ ")"
  | TList a -> "(Lg_rt.str_list " ^ gen_printer a ^ " " ^ es ^ ")"
  | TSeq a -> "(Lg_rt.str_seq " ^ gen_printer a ^ " " ^ es ^ ")"
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
    match repr t with
    | TInt -> "Lg_rt.str_int" | TFloat -> "Lg_rt.str_float" | TBool -> "Lg_rt.str_bool"
    | TChar -> "Lg_rt.str_char" | TString -> "Lg_rt.str_string" | TKeyword -> "Lg_rt.str_kw"
    | TSymbol -> "Lg_rt.str_sym" | TUnit -> "Lg_rt.str_unit"
    | TList a -> "(Lg_rt.str_list " ^ go a ^ ")"
    | TSeq a -> "(Lg_rt.str_seq " ^ go a ^ ")"
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
  match repr t with
  | TInt -> "DInt" | TFloat -> "DFloat" | TBool -> "DBool" | TChar -> "DChar"
  | TString -> "DStr" | TKeyword -> "DKw" | TSymbol -> "DSym" | TUnit -> "DUnit"
  | TOption _ -> "DOpt" | TList _ | TSeq _ -> "DList" | TVec _ -> "DVec"
  | TMap _ -> "DMap" | TSet _ -> "DSet"
  | _ -> "DStr"

and unbox_fn t =
  match repr t with
  | TInt -> "Lg_rt.as_int" | TFloat -> "Lg_rt.as_float" | TBool -> "Lg_rt.as_bool"
  | TChar -> "Lg_rt.as_char" | TString -> "Lg_rt.as_string" | TKeyword -> "Lg_rt.as_kw"
  | TSymbol -> "Lg_rt.as_sym" | TUnit -> "Lg_rt.as_unit" | TOption _ -> "Lg_rt.as_opt"
  | TList _ -> "Lg_rt.as_list" | TSeq _ -> "Lg_rt.as_seq" | TVec _ -> "Lg_rt.as_vec" | TMap _ -> "Lg_rt.as_map"
  | TSet _ -> "Lg_rt.as_set" | _ -> "Lg_rt.as_string"

(* deep box: a homogeneous collection crossed into `any` is re-boxed
   element-wise so the OCaml type is the closed Lg_rt.dyn *)
and box_deep ety es =
  match repr ety with
  | TVec el -> "(Lg_rt.DVec (Clj_core.Vec.map (fun x -> " ^ box_deep el "x" ^ ") " ^ es ^ "))"
  | TList el -> "(Lg_rt.DList (List.map (fun x -> " ^ box_deep el "x" ^ ") " ^ es ^ "))"
  | TSeq el -> "(Lg_rt.DList (List.map (fun x -> " ^ box_deep el "x" ^ ") (Clj_core.Seq.to_list " ^ es ^ ")))"
  | TSet el -> "(Lg_rt.DSet (Clj_core.Set.of_list (List.map (fun x -> " ^ box_deep el "x" ^ ") (Clj_core.Set.to_list " ^ es ^ "))))"
  | TMap _ -> "(Lg_rt.DMap " ^ flat_map_of ety es ^ ")"
  | TOption a -> "(Lg_rt.DOpt (match " ^ es ^ " with Some x -> Some (" ^ box_deep a "x" ^ ") | None -> None))"
  | TTuple ts ->
    let vs = List.mapi (fun i _ -> "t" ^ string_of_int i) ts in
    "(let (" ^ String.concat ", " vs ^ ") = " ^ es ^ " in Lg_rt.DVec (Clj_core.Vec.of_list ["
    ^ String.concat "; " (List.map2 (fun v ty -> box_deep ty v) vs ts) ^ "]))"
  | TFun _ -> "(ignore (" ^ es ^ "); Lg_rt.DStr \"<fn>\")"
  | TCon (n, _) when Hashtbl.mem Infer.all_vtypes n -> variant_box ety es
  | TAny -> es
  | TUnit -> "(ignore (" ^ es ^ "); Lg_rt.DUnit)"
  | _ -> "(Lg_rt." ^ dyn_ctor ety ^ " " ^ es ^ ")"

and box_of e = box_deep e.ety (arg_str e)

(* a seq-valued builtin whose declared result is a concrete collection
   is realized back to that collection kind; seq/any results stay lazy *)
and realize ret s =
  match repr ret with
  | TList _ -> "(Clj_core.Seq.to_list " ^ s ^ ")"
  | TVec _ -> "(Clj_core.Vec.of_list (Clj_core.Seq.to_list " ^ s ^ "))"
  | TSet _ -> "(Clj_core.Set.of_list (Clj_core.Seq.to_list " ^ s ^ "))"
  | _ -> s

(* box a user defvariant value into dyn: per-ctor match -> DVariant.
   Poly ('a) fields box as a literal marker — an OCaml 'a is not a dyn. *)
and variant_box ety es =
  let n = match repr ety with TCon (n, _) -> n | _ -> "" in
  let targs = match repr ety with TCon (_, ps) -> ps | _ -> [] in
  let ctors = try Hashtbl.find Infer.all_vtypes n with Not_found -> [] in
  let arm c =
    let vc = Hashtbl.find Infer.all_variants c in
    (* same-module ctor refs are unqualified *)
    let vc_ocaml =
      let pfx = !cur_mod ^ "." in
      if String.starts_with ~prefix:pfx vc.Infer.vc_ocaml then
        String.sub vc.Infer.vc_ocaml (String.length pfx)
          (String.length vc.Infer.vc_ocaml - String.length pfx)
      else vc.Infer.vc_ocaml
    in
    let ftys, retv =
      match repr vc.Infer.vc_scheme.Typ.sty with
      | Typ.TFun (fs, r) -> (fs, r)
      | r -> ([], r)
    in
    let tvars = match repr retv with Typ.TCon (_, vs) -> vs | _ -> [] in
    let box_f i t =
      let t =
        match repr t with
        | Typ.TVar _ as tv ->
          (match
             List.combine tvars targs
             |> List.find_opt (fun (tv2, _) -> Typ.dimp tv2 == tv)
           with
           | Some (_, a) -> a
           | None -> t)
        | _ -> t
      in
      match repr t with
      | Typ.TVar _ -> "Lg_rt.DStr \"<poly>\""
      | _ -> box_deep t ("f" ^ string_of_int i)
    in
    let pat =
      match ftys with
      | [] -> vc_ocaml
      | [ _ ] -> "(" ^ vc_ocaml ^ " f0)"
      | _ -> "(" ^ vc_ocaml ^ " (" ^ String.concat ", " (List.mapi (fun i _ -> "f" ^ string_of_int i) ftys) ^ "))"
    in
    "| " ^ pat ^ " -> Lg_rt.DVariant (\"" ^ c ^ "\", ["
    ^ String.concat "; " (List.mapi box_f ftys) ^ "])"
  in
  "(match " ^ es ^ " with " ^ String.concat " " (List.map arm ctors) ^ ")"

(* a statically-typed map re-built as a (dyn,dyn) map — the payload of
   Lg_rt.DMap; element-wise the flat analogue of nest_map_of *)
and flat_map_of ety es =
  match repr ety with
  | TMap (kty, vty) ->
    "(List.fold_left (fun m (k, v) -> Clj_core.Map.assoc m " ^ box_deep kty "k" ^ " " ^ box_deep vty "v"
    ^ ") (Clj_core.Map.of_list []) (List.of_seq (Clj_core.Map.seq " ^ es ^ ")))"
  | TAny -> "(match " ^ es ^ " with Lg_rt.DMap m -> m | _ -> Clj_core.Map.of_list [])"
  | _ -> "(Clj_core.Map.of_list [])"

(* a statically-typed map re-built as clj-core's (dyn, (dyn,dyn) nest) map —
   the shape Map.get_in / assoc_in / update_in / select_keys on dyn maps take. *)
and nest_map_of ety es =
  match repr ety with
  | TMap (k, v) ->
    "(List.fold_left (fun m (k, v) -> Clj_core.Map.assoc m " ^ box_deep k "k" ^ " " ^ box_nest v "v"
    ^ ") (Clj_core.Map.of_list []) (List.of_seq (Clj_core.Map.seq " ^ es ^ ")))"
  | TAny -> "(match " ^ es ^ " with Lg_rt.DMap m -> Lg_rt.nest_of_flat m | _ -> Clj_core.Map.of_list [])"
  | _ -> "(Clj_core.Map.of_list [])"

(* a map value in a nest map: sub-maps are Nest, leaves are Leaf dyn *)
and box_nest ety es =
  match repr ety with
  | TMap _ -> "(Clj_core.Map.Nest " ^ nest_map_of ety es ^ ")"
  | TAny -> "(match " ^ es ^ " with Lg_rt.DMap m -> Clj_core.Map.Nest (Lg_rt.nest_of_flat m) | d -> Clj_core.Map.Leaf d)"
  | _ -> "(Clj_core.Map.Leaf " ^ box_deep ety es ^ ")"

(* the nest-map arg of get-in / assoc-in / update-in / select-keys *)
and dyn_map_arg e = nest_map_of e.ety (arg_str e)

(* the flat (dyn,dyn) map held by a DMap value *)
and flat_map_arg e =
  match repr e.ety with
  | TAny -> "(Lg_rt.as_map " ^ arg_str e ^ ")"
  | _ -> arg_str e

(* `Some dyn` lookup on a (dyn,dyn) map, keyed by a dyn *)
and dyn_map_get mstr kdyn =
  "(Clj_core.Map.get " ^ mstr ^ " " ^ kdyn ^ ")"

(* unwrapped lookup with default *)
and dyn_map_get_or dstr mstr kdyn =
  "(Clj_core.Map.get_or " ^ dstr ^ " " ^ mstr ^ " " ^ kdyn ^ ")"
and is_any t = match repr t with TAny -> true | _ -> false
and as_dyn_list e =
  match repr e.ety with
  | TList el | TVec el | TSeq el | TSet el | TOption el ->
    if is_any el then as_list e
    else
      (match repr el with
       | TCon (n, _) when Hashtbl.mem Infer.all_vtypes n ->
         "(List.map (fun x -> " ^ variant_box el "x" ^ ") " ^ as_list e ^ ")"
       | _ -> "(List.map (fun x -> Lg_rt." ^ dyn_ctor el ^ " x) " ^ as_list e ^ ")")
  | _ -> as_list e

(* element conversion across the any boundary: a concrete value is boxed
   when the target type is `any`, a dyn is unboxed when the target type is
   concrete *)
and conv ty src s =
  let p = repr ty and a = repr src in
  (match p, a with
   | TFun (pts, pr), TFun (ats, ar) ->
     (* eta-wrap a function crossing a dyn boundary: contravariant params,
        covariant result *)
     let vs = List.mapi (fun i _ -> "cv" ^ string_of_int i ^ "_" ^ string_of_int (fresh_uid ())) pts in
     let args = List.mapi (fun i v ->
       let pt = List.nth pts i in
       let at = try List.nth ats i with _ -> TAny in
       conv at pt v) vs in
     "(fun " ^ (if vs = [] then "()" else String.concat " " vs) ^ " -> "
     ^ conv pr ar ("(" ^ s ^ (if args = [] then " ()" else " " ^ String.concat " " args) ^ ")") ^ ")"
   | TTuple ps, TTuple as_ when List.length ps = List.length as_ ->
     let vs = List.mapi (fun i _ -> "cv" ^ string_of_int i ^ "_" ^ string_of_int (fresh_uid ())) ps in
     "(let (" ^ String.concat ", " vs ^ ") = " ^ s ^ " in ("
     ^ String.concat ", " (List.map2 (fun v (pt, at) -> conv pt at v) vs (List.combine ps as_)) ^ "))"
   | TOption pe, TOption ae ->
     let f = conv pe ae "x" in
     if f = "x" then s else "(match " ^ s ^ " with Some x -> Some (" ^ f ^ ") | None -> None)"
   | TVec pe, TVec ae ->
     let f = conv pe ae "x" in
     if f = "x" then s else "(Clj_core.Vec.map (fun x -> " ^ f ^ ") " ^ s ^ ")"
   | TList pe, TList ae ->
     let f = conv pe ae "x" in
     if f = "x" then s else "(List.map (fun x -> " ^ f ^ ") " ^ s ^ ")"
   | TSeq pe, TSeq ae ->
     let f = conv pe ae "x" in
     if f = "x" then s else "(Clj_core.Seq.map (fun x -> " ^ f ^ ") " ^ s ^ ")"
   | TMap (pk, pv), TMap (ak, av) ->
     let fk = conv pk ak "k" and fv = conv pv av "v" in
     if fk = "k" && fv = "v" then s
     else "(Clj_core.Map.of_list (List.map (fun (k, v) -> (" ^ fk ^ ", " ^ fv ^ ")) (Clj_core.Map.to_list " ^ s ^ ")))"
   | TSet pe, TSet ae ->
     let f = conv pe ae "x" in
     if f = "x" then s else "(Clj_core.Set.of_list (List.map (fun x -> " ^ f ^ ") (Clj_core.Set.to_list " ^ s ^ ")))"
   (* seq is the universal collection interface: every concrete coll
      converts to a seq, and a seq realizes into a concrete coll *)
   | TSeq pe, TList ae ->
     let f = conv pe ae "x" in
     if f = "x" then "(Clj_core.Seq.of_list " ^ s ^ ")"
     else "(Clj_core.Seq.map (fun x -> " ^ f ^ ") (Clj_core.Seq.of_list " ^ s ^ "))"
   | TSeq pe, TVec ae ->
     let f = conv pe ae "x" in
     if f = "x" then "(Clj_core.Seq.of_vec " ^ s ^ ")"
     else "(Clj_core.Seq.map (fun x -> " ^ f ^ ") (Clj_core.Seq.of_vec " ^ s ^ "))"
   | TSeq pe, TSet ae ->
     let f = conv pe ae "x" in
     if f = "x" then "(Clj_core.Seq.of_set " ^ s ^ ")"
     else "(Clj_core.Seq.map (fun x -> " ^ f ^ ") (Clj_core.Seq.of_set " ^ s ^ "))"
   | TSeq pe, TMap (ak, av) ->
     let f = conv pe (TTuple [ ak; av ]) "x" in
     if f = "x" then "(Clj_core.Seq.of_map " ^ s ^ ")"
     else "(Clj_core.Seq.map (fun x -> " ^ f ^ ") (Clj_core.Seq.of_map " ^ s ^ "))"
   | TList pe, TSeq ae ->
     let f = conv pe ae "x" in
     if f = "x" then "(Clj_core.Seq.to_list " ^ s ^ ")"
     else "(List.map (fun x -> " ^ f ^ ") (Clj_core.Seq.to_list " ^ s ^ "))"
   | TVec pe, TSeq ae ->
     let f = conv pe ae "x" in
     if f = "x" then "(Clj_core.Vec.of_list (Clj_core.Seq.to_list " ^ s ^ "))"
     else "(Clj_core.Vec.of_list (List.map (fun x -> " ^ f ^ ") (Clj_core.Seq.to_list " ^ s ^ ")))"
   | TSet pe, TSeq ae ->
     let f = conv pe ae "x" in
     if f = "x" then "(Clj_core.Set.of_list (Clj_core.Seq.to_list " ^ s ^ "))"
     else "(Clj_core.Set.of_list (List.map (fun x -> " ^ f ^ ") (Clj_core.Seq.to_list " ^ s ^ ")))"
   | TMap (pk, pv), TSeq (TTuple [ ak; av ]) ->
     "(Clj_core.Map.of_list (List.map (fun x -> " ^ conv (TTuple [ pk; pv ]) (TTuple [ ak; av ]) "x" ^ ") (Clj_core.Seq.to_list " ^ s ^ ")))"
   | TMap (_, _), TSeq _ -> "(Clj_core.Map.of_list (Clj_core.Seq.to_list " ^ s ^ "))"
   (* unbox a dyn into a structured target: element-wise conversion *)
   | TTuple ps, TAny ->
     "(match " ^ s ^ " with Lg_rt.DVec v -> ("
     ^ String.concat ", " (List.mapi (fun i pt ->
        conv pt TAny ("(match Clj_core.Vec.nth_opt v " ^ string_of_int i
        ^ " with Some x -> x | None -> Lg_rt.DUnit)")) ps)
     ^ ") | _ -> (failwith \"dyn is not a tuple\"))"
   | TOption pe, TAny -> "(match " ^ s ^ " with Lg_rt.DOpt o -> (match o with Some x -> Some (" ^ conv pe TAny "x" ^ ") | None -> None) | _ -> (failwith \"dyn is not an option\"))"
   | TVec pe, TAny -> "(Clj_core.Vec.map (fun x -> " ^ conv pe TAny "x" ^ ") (Lg_rt.as_vec " ^ s ^ "))"
   | TList pe, TAny -> "(List.map (fun x -> " ^ conv pe TAny "x" ^ ") (Lg_rt.as_list " ^ s ^ "))"
   | TSeq pe, TAny -> "(Clj_core.Seq.map (fun x -> " ^ conv pe TAny "x" ^ ") (Lg_rt.as_seq " ^ s ^ "))"
   | TSet pe, TAny -> "(Clj_core.Set.of_list (List.map (fun x -> " ^ conv pe TAny "x" ^ ") (Clj_core.Set.to_list (Lg_rt.as_set " ^ s ^ "))))"
   | TMap (pk, pv), TAny ->
     "(Clj_core.Map.of_list (List.map (fun (k, v) -> (" ^ conv pk TAny "k" ^ ", " ^ conv pv TAny "v" ^ ")) (Clj_core.Map.to_list (Lg_rt.as_map " ^ s ^ "))))"
   | _ ->
     if is_any ty && not (is_any src) then box_deep src s
     else if (not (is_any ty)) && is_any src then "(" ^ unbox_fn ty ^ " " ^ s ^ ")"
     else s)

(* emit an element expr, converting it to the joined element type —
   dyn boxing plus coll<->seq realization *)
and emit_elem b elem_ty e =
  let ident = conv elem_ty e.ety "x" = "x" in
  buf_add b (conv elem_ty e.ety (arg_str ~local:(ident && e.emode = Ast.Local) e))

(* coll dispatch by static type *)
and coll_kind t =
  match repr t with
  | TVec _ -> `Vec | TList _ -> `List | TSet _ -> `Set | TMap _ -> `Map | TString -> `Str | TSeq _ -> `Seq | _ -> `List

(* the collection arg as an OCaml list expr *)
and as_list e =
  let a = arg_str e in
  let loc = !oxcaml && e.emode = Ast.Local in
  match repr e.ety with
  | TAny -> "(Lg_rt.dyn_to_list " ^ a ^ ")"
  | _ ->
    (match coll_kind e.ety with
     | `Vec -> if loc then "(Clj_core.Vec.to_list_local " ^ a ^ ")" else "(Clj_core.Vec.to_list " ^ a ^ ")"
     | `Set -> "(Clj_core.Set.to_list " ^ a ^ ")"
     | `Map -> if loc then "(Clj_core.Map.to_list_local " ^ a ^ ")" else "(List.of_seq (Clj_core.Map.seq " ^ a ^ "))"
     | `Str -> "(Lg_rt.string_chars " ^ a ^ ")"
     | `Seq -> "(Clj_core.Seq.to_list " ^ a ^ ")"
     | `List -> a)

(* the collection arg as a lazy OCaml seq — when the seq need only be
   local arguments never reach here — modes rejects them upstream
   (lazy seq producers cannot accept local values). *)
and as_seq e =
  let a = arg_str e in
  match repr e.ety with
  | TAny -> "(Lg_rt.dyn_to_seq " ^ a ^ ")"
  | TOption u ->
    let inner =
      match coll_kind u with
      | `Vec -> "Clj_core.Seq.of_vec"
      | `Set -> "Clj_core.Seq.of_set"
      | `Map -> "Clj_core.Seq.of_map"
      | `Str -> "Clj_core.Seq.of_string"
      | `List -> "Clj_core.Seq.of_list"
      | `Seq -> "(fun s -> s)"
    in
    "(match " ^ a ^ " with None -> Clj_core.Seq.empty | Some s -> " ^ inner ^ " s)"
  | _ ->
    (match coll_kind e.ety with
     | `Vec -> "(Clj_core.Seq.of_vec " ^ a ^ ")"
     | `Set -> "(Clj_core.Seq.of_set " ^ a ^ ")"
     | `Map -> "(Clj_core.Seq.of_map " ^ a ^ ")"
     | `Str -> "(Clj_core.Seq.of_string " ^ a ^ ")"
     | `Seq -> a
     | `List -> "(Clj_core.Seq.of_list " ^ a ^ ")")

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

(* update ops contributed by one call `n c args...` on a collection of
   type ety — shared by chain_step (literal/once-used roots) and
   fbip_chain (self-recursive accumulator params) *)
and step_ops n (ety : ty) (args : expr list) : cop list option =
  match n, args with
  | "conj", _ :: xs when xs <> [] ->
    (match ety with
     | TVec _ -> Some (List.map (fun x -> CPush x) xs)
     | TMap _ -> Some (List.map (fun x -> CPair x) xs)
     | TSet _ -> Some (List.map (fun x -> CAdd x) xs)
     | _ -> None)
  | "assoc", _ :: i :: x :: rest ->
    (match ety with
     | TVec _ when rest = [] -> Some [ CSet (i, x) ]
     | TMap _ when List.length rest mod 2 = 0 ->
       let rec ps = function a :: b :: t -> (a, b) :: ps t | [] -> [] | _ -> [] in
       Some (List.map (fun (k, v) -> CPut (k, v)) ((i, x) :: ps rest))
     | _ -> None)
  | "dissoc", _ :: ks when ks <> [] ->
    (match ety with TMap _ -> Some (List.map (fun k -> CDrop k) ks) | _ -> None)
  | "pop", [ _ ] -> (match ety with TVec _ -> Some [ CPop ] | _ -> None)
  | "update", [ _; i; f ] ->
    (match ety with TVec _ -> Some [ CUpd (i, f) ] | TMap _ -> Some [ CUpdMap (i, f) ] | _ -> None)
  | "into", [ _; xs ] ->
    (match repr xs.ety with
     | TMap _ -> (match ety with TMap _ -> Some [ CMExt xs ] | _ -> None)
     | TVec _ | TList _ | TSet _ ->
       (match ety with TVec _ -> Some [ CExt xs ] | TSet _ -> Some [ CSExt xs ] | _ -> None)
     | _ -> None)
  | "disj", _ :: xs when xs <> [] ->
    (match ety with TSet _ -> Some (List.map (fun x -> CDel x) xs) | _ -> None)
  | _ -> None

and chain_step n args : (expr * cop list) option =
  match n, args with
  | _, c :: _ ->
    let root_ops =
      match coll_spine c with
      | Some _ as r -> r
      | None -> if owned_root c then Some (c, []) else None
    in
    (match root_ops, step_ops n (repr c.ety) args with
     | Some (r, ops), Some more -> Some (r, ops @ more)
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
  | CPair kv ->
    let ke = ax kv in
    (match repr kv.ety with
     | TTuple [ tk; tv ] ->
       buf_add b ("Lg_rt.mb_assoc " ^ bn ^ " " ^ conv kt tk ("(fst " ^ ke ^ ")") ^ " " ^ conv vt tv ("(snd " ^ ke ^ ")") ^ "; ")
     | TMap _ ->
       buf_add b ("Lg_rt.mb_extend_map " ^ bn ^ " " ^ ke ^ "; ")
     | TAny ->
       buf_add b ("(match Lg_rt.dyn_to_list " ^ ke ^ " with [k; v] -> Lg_rt.mb_assoc " ^ bn ^ " "
                  ^ conv kt TAny "k" ^ " " ^ conv vt TAny "v" ^ " | _ -> failwith \"conj: map entry must be [k v]\"); ")
     | _ ->
       let pe =
         (match repr kv.ety with
          | TVec el | TSeq el | TList el -> el
          | _ -> TAny)
       in
       buf_add b ("(match " ^ as_list kv ^ " with [k; v] -> Lg_rt.mb_assoc " ^ bn ^ " "
                  ^ conv kt pe "k" ^ " " ^ conv vt pe "v" ^ " | _ -> failwith \"conj: map entry must be [k v]\"); "))
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

(* ---- linear let-chains: (let [v2 (conj v1 x) v3 (assoc v2 k y)] ...)
   where every intermediate binder's only use is the next step (bused=1)
   collapses into ONE mutable builder + one freeze. The root is owned
   the same way owned chains are (literal or once-used concrete local —
   vb_of_vec copies, so value semantics hold regardless). Intermediate
   binders get no OCaml binding at all; only the run's last binder is
   materialized (frozen). Oxcaml keeps the persistent path, like fbip. *)

and lin_root e =
  match e.desc with
  | EVecLit _ | EMapLit _ | ESetLit _ -> true
  | ELocal bd -> bd.bused <= 1 && conc_ty bd.bty
  | _ -> false

and lin_chain_step e : (expr * cop list) option =
  match e.desc with
  | ECall ({ desc = EBuiltin n; _ }, args) ->
    (match n, args with
     | _, c :: _ ->
       let root_ops =
         match lin_chain_step c with
         | Some _ as r -> r
         | None -> if lin_root c then Some (c, []) else None
       in
       (match root_ops, step_ops n (repr c.ety) args with
        | Some (r, ops), Some more -> Some (r, ops @ more)
        | _ -> None)
     | _ -> None)
  | _ -> None

and emit_let_binds ~(local : bool) b (pairs : (Ast.binder * expr) list) body =
  let bind_one (bd : Ast.binder) init =
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
    buf_add b (sanitize bd.bname ^ "__" ^ string_of_int bd.bid);
    let loc = !oxcaml && bd.bmode = Ast.Local in
    if loc then buf_add b " @ local";
    buf_add b " = ";
    (match bd.bmode, !oxcaml with
     | Ast.Owned, true -> buf_add b "(* unique *) "
     | _ -> ());
    emit_expr ~local:loc b init;
    buf_add b " in "
  in
  let step_on prev init =
    match init.desc with
    | ECall ({ desc = EBuiltin n; _ }, args) ->
      (match args with
       | ({ desc = ELocal p; _ } as c) :: _ when p.bid = prev.Ast.bid && conc_ty c.ety ->
         step_ops n (repr c.ety) args
       | _ -> None)
    | _ -> None
  in
  let emit_run root ops lastb =
    let bn pre = pre ^ "__" ^ string_of_int (fresh_uid ()) in
    (match repr root.ety with
     | TVec el ->
       let n = bn "vb" in
       buf_add b ("(let " ^ n ^ " = "); vroot b root;
       buf_add b " in (begin ";
       List.iter (emit_vop b n el) ops;
       buf_add b ("() end); (let " ^ sanitize lastb.Ast.bname ^ "__" ^ string_of_int lastb.bid
                  ^ " = (Lg_rt.vb_freeze " ^ n ^ ") in ")
     | TMap (kt, vt) ->
       let n = bn "mb" in
       buf_add b ("(let " ^ n ^ " = "); mroot b root kt vt;
       buf_add b " in (begin ";
       List.iter (emit_mop b n kt vt) ops;
       buf_add b ("() end); (let " ^ sanitize lastb.Ast.bname ^ "__" ^ string_of_int lastb.bid
                  ^ " = (Lg_rt.mb_freeze " ^ n ^ ") in ")
     | TSet el ->
       let n = bn "sb" in
       buf_add b ("(let " ^ n ^ " = "); sroot b root;
       buf_add b " in (begin ";
       List.iter (emit_sop b n el) ops;
       buf_add b ("() end); (let " ^ sanitize lastb.Ast.bname ^ "__" ^ string_of_int lastb.bid
                  ^ " = (Lg_rt.sb_freeze " ^ n ^ ") in ")
     | _ -> ())
  in
  let rec go pairs closes =
    match pairs with
    | [] -> emit_expr ~local b body; List.iter (fun _ -> buf_add b ")") (List.init closes (fun _ -> ()))
    | (bd, init) :: rest ->
      (match (if !oxcaml then None else lin_chain_step init) with
       | Some (root, ops0) ->
         let rec gather ops prev acc rs =
           match rs with
           | (bd2, i2) :: tl when prev.bused <= 1 ->
             (match step_on prev i2 with
              | Some more -> gather (ops @ more) bd2 (bd2 :: acc) tl
              | None -> (ops, List.rev acc, rs))
           | _ -> (ops, List.rev acc, rs)
         in
         let ops, run, rest' = gather ops0 bd [] rest in
         (match run with
          | _ :: _ ->
            (match repr root.ety with
             | TVec _ | TMap (_, _) | TSet _ ->
               let lastb = List.nth run (List.length run - 1) in
               emit_run root ops lastb; go rest' (closes + 2)
             | _ -> bind_one bd init; go rest (closes + 1))
          | [] ->
            (match repr root.ety with
             | TVec el when List.length ops >= 2 ->
               buf_add b ("(let " ^ sanitize bd.bname ^ "__" ^ string_of_int bd.bid ^ " = ");
               emit_vbuilder b root el ops; buf_add b " in "; go rest' (closes + 1)
             | TMap (kt, vt) when List.length ops >= 2 ->
               buf_add b ("(let " ^ sanitize bd.bname ^ "__" ^ string_of_int bd.bid ^ " = ");
               emit_mbuilder b root kt vt ops; buf_add b " in "; go rest' (closes + 1)
             | TSet el when List.length ops >= 2 ->
               buf_add b ("(let " ^ sanitize bd.bname ^ "__" ^ string_of_int bd.bid ^ " = ");
               emit_sbuilder b root el ops; buf_add b " in "; go rest' (closes + 1)
             | _ -> bind_one bd init; go rest' (closes + 1)))
       | None -> bind_one bd init; go rest (closes + 1))
  in
  go pairs 0

(* ---- FBIP: self-recursive accumulator params as mutable builders ----
   In `(fn f [.. p ..] body)` where collection param p is only ever (a) the
   root of an update chain in every self-call's p-position, or (b) a bare
   result, p can run as a mutable builder: self-calls mutate in place and
   pass it along, results freeze it. The emitted value wraps the inner
   `let rec` in `(fun .. -> f' .. (vb_of_vec p) ..)` so callers still see a
   plain `vec -> r` — the transform is invisible outside the fn. *)

and occurs_bid bid e =
  match e.desc with
  | ELocal q -> q.bid = bid
  | EInt _ | EFloat _ | EBool _ | EChar _ | EStr _ | EKeyword _ | ESymbol _
  | ENil | EGlobal _ | EBuiltin _ -> false
  | EFun fn -> occurs_bid bid fn.body
  | ECall (c, xs) -> List.exists (occurs_bid bid) (c :: xs)
  | EOCamlCall (c, oas) ->
    List.exists (occurs_bid bid) (c :: List.map oarg_expr oas)
  | EIf (a, x, y) -> List.exists (occurs_bid bid) [ a; x; y ]
  | EDo xs | ETuple xs | EVecLit xs | EListLit xs | ESetLit xs ->
    List.exists (occurs_bid bid) xs
  | ELet (bs, x) ->
    List.exists (fun (_, ex) -> occurs_bid bid ex) bs || occurs_bid bid x
  | EMapLit ps ->
    List.exists (fun (k, v) -> occurs_bid bid k || occurs_bid bid v) ps
  | EMatchOpt (a, _, x, y) | EDynVec (a, _, x, y) | EDynMap (a, _, x, y)
  | EVariant (a, _, _, x, y) -> List.exists (occurs_bid bid) [ a; x; y ]
  | ETry (b', c, f) ->
    List.exists (occurs_bid bid)
      (b' :: (match c with Some (_, h) -> [ h ] | None -> [])
         @ (match f with Some fe -> [ fe ] | None -> []))
  | EUnbox (a, _) | EUnboxOpt (a, _) | EBox a -> occurs_bid bid a
  | EOpt None -> false
  | EOpt (Some a) -> occurs_bid bid a

(* exprs carried by one builder op — the accumulator must not appear in
   them (that would read the builder while it's being threaded) *)
and cop_exprs = function
  | CPush x -> [ x ] | CSet (i, x) -> [ i; x ] | CUpd (i, f) -> [ i; f ]
  | CPut (k, v) -> [ k; v ] | CDrop k -> [ k ] | CPair kv -> [ kv ]
  | CUpdMap (k, f) -> [ k; f ] | CMExt m -> [ m ] | CExt x -> [ x ]
  | CSExt x -> [ x ] | CAdd x -> [ x ] | CDel x -> [ x ] | CPop -> []

(* chain of update calls rooted at a bare ELocal p (fbip accumulator) *)
and fbip_chain p e : cop list option =
  match e.desc with
  | ELocal q -> if q.bid = p.Ast.bid then Some [] else None
  | ECall ({ desc = EBuiltin n; _ }, (c :: _ as args)) ->
    (match fbip_chain p c, step_ops n (repr c.ety) args with
     | Some ops, Some more -> Some (ops @ more)
     | _ -> None)
  | _ -> None

(* does body contain a self-call to sb at all — otherwise the transform
   buys nothing *)
and fbip_has_self_call sb e =
  match e.desc with
  | ECall (ce, _) -> (match ce.desc with ELocal q -> q.bid = sb.Ast.bid | _ -> occurs_bid sb.Ast.bid e)
  | _ -> occurs_bid sb.Ast.bid e

(* every use of param p inside a self-recursive body stays fbip-safe:
   - bare ELocal p in a result position -> frozen at emit
   - p-th arg of a self-call -> must be an update chain rooted at p, and
     neither p nor the self name may occur inside the op's operands
   - p anywhere else (other call args, let inits, literals, closures,
     scrutinees, conditions) -> escapes or can't run on a builder: reject *)
and fbip_flow p pidx sb e : bool =
  let free x = not (occurs_bid p.Ast.bid x || occurs_bid sb.Ast.bid x) in
  match e.desc with
  | ELocal q -> q.bid <> sb.Ast.bid (* bare p allowed; bare self-name is not *)
  | ECall (ce, args) ->
    (match ce.desc with
     | ELocal f' when f'.bid = sb.Ast.bid ->
       List.for_all
         (fun (j, a) ->
           if j = pidx then
             match fbip_chain p a with
             | Some ops ->
               List.for_all
                 (fun op -> List.for_all free (cop_exprs op))
                 ops
             | None -> false
           else free a)
         (List.mapi (fun j a -> (j, a)) args)
     | _ -> free e)
  | EIf (c, t, f) -> free c && fbip_flow p pidx sb t && fbip_flow p pidx sb f
  | EDo es ->
    (match List.rev es with
     | last :: rest -> List.for_all free rest && fbip_flow p pidx sb last
     | [] -> true)
  | ELet (bs, body) ->
    List.for_all (fun (_, x) -> free x) bs && fbip_flow p pidx sb body
  | EMatchOpt (a, _, x, y) | EDynVec (a, _, x, y) | EDynMap (a, _, x, y)
  | EVariant (a, _, _, x, y) ->
    free a && fbip_flow p pidx sb x && fbip_flow p pidx sb y
  | _ -> free e

(* a fully concrete type: no unresolved tvars anywhere. TVar args are
   the one case where `repr` lies — it maps them to TAny, which would
   emit dyn-keyed builders while infer instantiates the fn's use site
   with a concrete type (the emitted builder then disagrees). *)
and conc_ty t =
  match Typ.dimp t with
  | TVar _ -> false
  | TVec x | TSet x | TList x | TSeq x | TOption x -> conc_ty x
  | TMap (k, v) -> conc_ty k && conc_ty v
  | TTuple ts -> List.for_all conc_ty ts
  | _ -> true

(* pick a param that can run as a builder, or None *)
and fbip_pick fn : (int * [ `Vec | `Map | `Set ]) option =
  match fn.Ast.fself, fn.Ast.variadic with
  | Some sb, None when fbip_has_self_call sb fn.body ->
    List.find_map
      (fun (i, p) ->
        match repr p.Ast.bty with
        | TVec _ when conc_ty p.Ast.bty && fbip_flow p i sb fn.body -> Some (i, `Vec)
        | TMap _ when conc_ty p.Ast.bty && fbip_flow p i sb fn.body -> Some (i, `Map)
        | TSet _ when conc_ty p.Ast.bty && fbip_flow p i sb fn.body -> Some (i, `Set)
        | _ -> None)
      (List.mapi (fun i p -> (i, p)) fn.params)
  | _ -> None

and fbip_of b kind nm =
  buf_add b (match kind with `Vec -> "(Lg_rt.vb_of_vec " | `Map -> "(Lg_rt.mb_of_map " | `Set -> "(Lg_rt.sb_of_set ");
  buf_add b nm; buf_add b ")"
and fbip_freeze b kind nm =
  buf_add b (match kind with `Vec -> "(Lg_rt.vb_freeze " | `Map -> "(Lg_rt.mb_freeze " | `Set -> "(Lg_rt.sb_freeze ");
  buf_add b nm; buf_add b ")"

(* emit one self-call's builder-arg update as `begin ops; b end` *)
and fbip_rec_arg b kind p a =
  match fbip_chain p a with
  | None -> fbip_of b kind (arg_str a)   (* defensive — flow proved a chain *)
  | Some ops ->
    let bn = sanitize p.Ast.bname ^ "__" ^ string_of_int p.Ast.bid in
    let el =
      match repr p.Ast.bty with
      | TVec t | TMap (_, t) | TSet t -> t
      | _ -> TAny
    in
    buf_add b "(begin ";
    List.iter
      (fun op ->
        match kind with
        | `Vec -> emit_vop b bn el op
        | `Map -> (match repr p.Ast.bty with TMap (kt, vt) -> emit_mop b bn kt vt op | _ -> ())
        | `Set -> emit_sop b bn el op)
      ops;
    buf_add b (bn ^ " end)")

and emit_builtin_call ?(call_local = false) b ret name args =
  if not (emit_owned_chain b name args) then begin
  let t n = (List.nth args n).ety in
  let call_local = call_local && !oxcaml in
  (* strict seq readers take `xs @ local` in the ox build; lazy seq
     producers have no local form — modes rejects local args there *)
  let sloc i =
    let a = List.nth args i in
    !oxcaml
    && (match a.desc with
        | Ast.ELocal b -> b.bmode = Ast.Local
        | Ast.EGlobal _ -> false
        | _ -> a.emode = Ast.Local)
  in
  (* an arg may only be stack_-allocated when the callee borrows that
     position. The clj-core `_local` signatures borrow only collection
     args — callback params are global, so fn (or fn-carrying) args must
     never be marked local even when their own emode is Local. *)
  let a n =
    let e = List.nth args n in
    arg_str ~local:(sloc n && (match repr (t n) with TVec _ | TList _ | TSet _ | TMap _ | TSeq _ | TString -> true | _ -> false)) e
  in
  let sconsi i g l = if sloc i then l else g in
  let sfn n = "Clj_core.Seq." ^ munge n in
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
     if is_any (t 0) || is_any (t 1) then
       (* dyn ordering: dyn_cmp handles int/float mixes and fails loudly
          on non-comparable payloads *)
       buf_add b ("(Lg_rt.dyn_cmp " ^ conv TAny (t 0) (a 0) ^ " " ^ conv TAny (t 1) (a 1) ^ " " ^ op ^ " 0)")
     else
       buf_add b ("(" ^ a 0 ^ " " ^ op ^ " " ^ a 1 ^ ")")
   | "=" | "not=" ->
     (* structural equality: clj maps/sets carry a compare fn inside, so
        polymorphic compare crashes on them — go through the clj-core
        `equal` functions instead *)
     let rec deep_any t =
       match repr t with
       | TAny -> true
       | TVec x | TList x | TSeq x | TSet x | TOption x -> deep_any x
       | TMap (k, v) -> deep_any k || deep_any v
       | TTuple ts -> List.exists deep_any ts
       | _ -> false
     in
     let inner =
       if deep_any (t 0) || deep_any (t 1) || repr (t 0) <> repr (t 1) then
         (* differing representations still unify through TAny — box both
            sides and compare as dyn *)
         "(Lg_rt.dyn_eq " ^ conv TAny (t 0) (a 0) ^ " " ^ conv TAny (t 1) (a 1) ^ ")"
       else
         match repr (t 0) with
         | TVec _ -> "(Clj_core.Vec.equal " ^ a 0 ^ " " ^ a 1 ^ ")"
         | TSet _ -> "(Clj_core.Set.equal " ^ a 0 ^ " " ^ a 1 ^ ")"
         | TMap _ -> "(Clj_core.Map.equal " ^ a 0 ^ " " ^ a 1 ^ ")"
         | TSeq _ -> "(Clj_core.Seq.to_list " ^ a 0 ^ " = Clj_core.Seq.to_list " ^ a 1 ^ ")"
         | _ -> "(" ^ a 0 ^ " = " ^ a 1 ^ ")"
     in
     buf_add b (if name = "=" then inner else "(not " ^ inner ^ ")")
   | "not" ->
     buf_add b
       (match repr (t 0) with
        | TAny -> "(not (Lg_rt.dyn_truthy " ^ a 0 ^ "))"
        | TBool -> "(not " ^ a 0 ^ ")"
        | _ -> "(not (let __ = " ^ a 0 ^ " in true))")
   | "inc" -> buf_add b ("(" ^ conv TInt (t 0) (a 0) ^ " + 1)")
   | "dec" -> buf_add b ("(" ^ conv TInt (t 0) (a 0) ^ " - 1)")
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
        | TAny -> "(Lg_rt.as_float " ^ a 0 ^ ")"
        | _ -> a 0)
   | "int" ->
     buf_add b
       (match repr (t 0) with
        | TFloat -> "(int_of_float " ^ a 0 ^ ")"
        | TChar -> "(Char.code " ^ a 0 ^ ")"
        | TString -> "(int_of_string " ^ a 0 ^ ")"
        | TAny -> "(Lg_rt.as_int " ^ a 0 ^ ")"
        | _ -> a 0)
   | "name" ->
     buf_add b
       (match repr (t 0) with
        | TKeyword -> "(Clj_core.Keyword.name " ^ a 0 ^ ")"
        | TSymbol -> "(Clj_core.Symbol.name " ^ a 0 ^ ")"
        | TAny -> "(Lg_rt.as_name " ^ a 0 ^ ")"
        | _ -> a 0)
   | "keyword" -> buf_add b ("(Clj_core.Keyword.of_string " ^ conv TString (t 0) (a 0) ^ ")")
   | "symbol" -> buf_add b ("(Clj_core.Symbol.of_string " ^ conv TString (t 0) (a 0) ^ ")")
   | "str" | "pr-str" ->
     let parts = List.map (fun e -> printer_call e.ety e) args in
     buf_add b ("(" ^ String.concat " ^ " (if parts = [] then [ "\"\"" ] else parts) ^ ")")
   | "println" | "print" ->
     let parts = List.map (fun e -> printer_call e.ety e) args in
     let joined = String.concat " ^ \" \" ^ " (if parts = [] then [ "\"\"" ] else parts) in
     buf_add b ("(" ^ (if name = "println" then "print_endline" else "print_string") ^ " (" ^ joined ^ "))")
   | "cons" ->
     let el = match repr ret with TSeq e -> e | _ -> TAny in
     let hd = conv el (t 0) (a 0) in
     buf_add b ("(" ^ sfn "cons" ^ " " ^ hd ^ " " ^ seq_elem_conv el (t 1) (as_seq (List.nth args 1)) ^ ")")
   | "list" ->
     buf_add b
       ((if call_local then "(stack_ [" else "[")
        ^ String.concat "; " (List.map arg_str args)
        ^ (if call_local then "])" else "]"))
   | "first" -> buf_add b ("(" ^ "Clj_core.Seq.first" ^ " " ^ as_seq (List.nth args 0) ^ ")")
   | "next" -> buf_add b ("(" ^ sfn "next" ^ " " ^ as_seq (List.nth args 0) ^ ")")
   | "rest" -> buf_add b ("(" ^ sfn "rest" ^ " " ^ as_seq (List.nth args 0) ^ ")")
   | "seq" -> buf_add b ("(let s = " ^ as_seq (List.nth args 0) ^ " in if " ^ "Clj_core.Seq.is_empty" ^ " s then None else " ^ (if call_local then "(stack_ (Some s))" else "Some s") ^ ")")
   | "exit" -> buf_add b ("(Stdlib.exit " ^ conv TInt (t 0) (a 0) ^ ")")
   | "exn" -> buf_add b ("(Stdlib.Failure " ^ conv TString (t 0) (a 0) ^ ")")
   | "exn-message" -> buf_add b ("(Printexc.to_string " ^ a 0 ^ ")")
   | "throw" -> buf_add b ("(raise " ^ a 0 ^ ")")
   (* io / system builtins: native emits inline channel/Sys/Unix code;
      melange routes through the emitted Lg_node JS bridge *)
   | "slurp" ->
     buf_add b
       (if !melange then "(Lg_node.slurp " ^ conv TString (t 0) (a 0) ^ ")"
        else "(let ic__ = open_in_bin " ^ conv TString (t 0) (a 0) ^ " in "
             ^ "let s__ = really_input_string ic__ (in_channel_length ic__) in close_in ic__; s__)")
   | "spit" ->
     buf_add b
       (if !melange then "(Lg_node.spit " ^ conv TString (t 0) (a 0) ^ " " ^ conv TString (t 1) (a 1) ^ ")"
        else "(let oc__ = open_out_bin " ^ conv TString (t 0) (a 0) ^ " in "
             ^ "output_string oc__ " ^ conv TString (t 1) (a 1) ^ "; close_out oc__)")
   | "read-line" ->
     buf_add b
       (if !melange then "(Lg_node.read_line ())"
        else "(try Some (Stdlib.read_line ()) with End_of_file -> None)")
   | "argv" ->
     buf_add b
       (if !melange then "(Array.to_list (Lg_node.argv ()))"
        else "(List.tl (Array.to_list Sys.argv))")
   | "env" ->
     buf_add b
       (if !melange then "(Lg_node.env_opt " ^ conv TString (t 0) (a 0) ^ ")"
        else "(Sys.getenv_opt " ^ conv TString (t 0) (a 0) ^ ")")
   | "file-exists?" ->
     buf_add b
       (if !melange then "(Lg_node.file_exists " ^ conv TString (t 0) (a 0) ^ ")"
        else "(Sys.file_exists " ^ conv TString (t 0) (a 0) ^ ")")
   | "sh" ->
     buf_add b
       (if !melange then "(Lg_node.sh " ^ conv TString (t 0) (a 0) ^ ")"
        else
          "(let ic__ = Unix.open_process_in " ^ conv TString (t 0) (a 0) ^ " in "
          ^ "let b__ = Buffer.create 64 in "
          ^ "(try while true do Buffer.add_string b__ (input_line ic__); Buffer.add_char b__ '\\n' done "
          ^ "with End_of_file -> ()); "
          ^ "Stdlib.ignore (Unix.close_process_in ic__); Buffer.contents b__)")
   | "now-ms" ->
     buf_add b
       (if !melange then "(Lg_node.now_ms ())"
        else "(int_of_float (Unix.gettimeofday () *. 1000.))")
   (* string library *)
   | "subs" ->
     if List.length args = 3 then
       buf_add b ("(String.sub " ^ conv TString (t 0) (a 0) ^ " " ^ conv TInt (t 1) (a 1)
                  ^ " (" ^ conv TInt (t 2) (a 2) ^ " - " ^ a 1 ^ "))")
     else
       buf_add b ("(String.sub " ^ conv TString (t 0) (a 0) ^ " " ^ conv TInt (t 1) (a 1)
                  ^ " (String.length " ^ a 0 ^ " - " ^ a 1 ^ "))")
   | "split" -> buf_add b ("(Lg_rt.split_on " ^ conv TString (t 1) (a 1) ^ " " ^ conv TString (t 0) (a 0) ^ ")")
   | "join" ->
     (* each element is coerced with its own printer, like str *)
     let sep_s, cidx =
       if List.length args = 2 then (conv TString (t 0) (a 0), 1) else ("\"\"", 0)
     in
     let el =
       match repr (t cidx) with
       | TList x | TVec x | TSet x | TSeq x -> x
       | TMap (k, v) -> TTuple [ k; v ]
       | TString -> TChar
       | _ -> TAny
     in
     buf_add b ("(String.concat " ^ sep_s ^ " (List.map " ^ gen_printer el
                ^ " " ^ as_list (List.nth args cidx) ^ "))")
   | "trim" -> buf_add b ("(String.trim " ^ conv TString (t 0) (a 0) ^ ")")
   | "triml" -> buf_add b ("(Lg_rt.triml " ^ conv TString (t 0) (a 0) ^ ")")
   | "trimr" -> buf_add b ("(Lg_rt.trimr " ^ conv TString (t 0) (a 0) ^ ")")
   | "upper-case" -> buf_add b ("(String.uppercase_ascii " ^ conv TString (t 0) (a 0) ^ ")")
   | "lower-case" -> buf_add b ("(String.lowercase_ascii " ^ conv TString (t 0) (a 0) ^ ")")
   | "blank?" -> buf_add b ("(Lg_rt.str_blank " ^ conv TString (t 0) (a 0) ^ ")")
   | "includes?" -> buf_add b ("(Lg_rt.str_contains " ^ conv TString (t 0) (a 0) ^ " " ^ conv TString (t 1) (a 1) ^ ")")
   | "starts-with?" -> buf_add b ("(String.starts_with ~prefix:" ^ conv TString (t 1) (a 1) ^ " " ^ conv TString (t 0) (a 0) ^ ")")
   | "ends-with?" -> buf_add b ("(String.ends_with ~suffix:" ^ conv TString (t 1) (a 1) ^ " " ^ conv TString (t 0) (a 0) ^ ")")
   | "replace" -> buf_add b ("(Lg_rt.str_replace_lit " ^ conv TString (t 1) (a 1) ^ " " ^ conv TString (t 2) (a 2) ^ " " ^ conv TString (t 0) (a 0) ^ ")")
   (* regex-lite: Str on native, JS RegExp (Lg_node) on melange *)
   | "re-find" ->
     buf_add b
       (if !melange then "(Lg_node.re_find " ^ conv TString (t 0) (a 0) ^ " " ^ conv TString (t 1) (a 1) ^ ")"
        else "(try Stdlib.ignore (Str.search_forward (Str.regexp " ^ conv TString (t 0) (a 0) ^ ") "
             ^ conv TString (t 1) (a 1) ^ " 0); Some (Str.matched_string " ^ a 1 ^ ") with Not_found -> None)")
   | "re-matches" ->
     buf_add b
       (if !melange then "(Lg_node.re_matches " ^ conv TString (t 0) (a 0) ^ " " ^ conv TString (t 1) (a 1) ^ ")"
        else "(if Str.string_match (Str.regexp " ^ conv TString (t 0) (a 0) ^ ") " ^ conv TString (t 1) (a 1)
             ^ " 0 && Str.match_end () = String.length " ^ a 1 ^ " then Some " ^ a 1 ^ " else None)")
   | "re-seq" ->
     buf_add b
       (if !melange then "(Lg_node.re_seq " ^ conv TString (t 0) (a 0) ^ " " ^ conv TString (t 1) (a 1) ^ ")"
        else "(let re__ = Str.regexp " ^ conv TString (t 0) (a 0) ^ " in let rec go__ i acc = "
             ^ "match (try Some (Str.search_forward re__ " ^ conv TString (t 1) (a 1) ^ " i) with Not_found -> None) "
             ^ "with Some _ -> go__ (Str.match_end ()) (Str.matched_string " ^ a 1 ^ " :: acc) "
             ^ "| None -> List.rev acc in go__ 0 [])")
   | "re-split" ->
     buf_add b
       (if !melange then "(Lg_node.re_split " ^ conv TString (t 0) (a 0) ^ " " ^ conv TString (t 1) (a 1) ^ ")"
        else "(Str.split (Str.regexp " ^ conv TString (t 0) (a 0) ^ ") " ^ conv TString (t 1) (a 1) ^ ")")
   | "re-replace" ->
     buf_add b
       (if !melange then "(Lg_node.re_replace " ^ conv TString (t 0) (a 0) ^ " " ^ conv TString (t 1) (a 1) ^ " " ^ conv TString (t 2) (a 2) ^ ")"
        else "(Str.global_replace (Str.regexp " ^ conv TString (t 0) (a 0) ^ ") "
             ^ conv TString (t 2) (a 2) ^ " " ^ conv TString (t 1) (a 1) ^ ")")
   | "count" ->
     (match coll with
      | `Vec -> buf_add b ("(Clj_core.Vec.count " ^ a 0 ^ ")")
      | `List -> buf_add b ("(List.length " ^ a 0 ^ ")")
      | `Set -> buf_add b ("(Clj_core.Set.count " ^ a 0 ^ ")")
      | `Map -> buf_add b ("(Clj_core.Map.count " ^ a 0 ^ ")")
      | `Seq -> buf_add b ("(" ^ "Clj_core.Seq.count" ^ " " ^ a 0 ^ ")")
      | `Str -> buf_add b ("(String.length " ^ a 0 ^ ")"))
   | "empty?" ->
     (match coll with
      | `Vec -> buf_add b ("(Clj_core.Vec.is_empty " ^ a 0 ^ ")")
      | `List -> buf_add b ("(" ^ a 0 ^ " = [])")
      | `Set -> buf_add b ("(Clj_core.Set.is_empty " ^ a 0 ^ ")")
      | `Map -> buf_add b ("(Clj_core.Map.is_empty " ^ a 0 ^ ")")
      | `Seq -> buf_add b ("(" ^ "Clj_core.Seq.is_empty" ^ " " ^ a 0 ^ ")")
      | `Str -> buf_add b ("(String.length " ^ a 0 ^ " = 0)"))
   | "map?" ->
     (match repr (t 0) with
      | TMap _ -> buf_add b "true"
      | TAny -> buf_add b ("(match " ^ a 0 ^ " with Lg_rt.DMap _ -> true | _ -> false)")
      | _ -> buf_add b "false")
   | "contains?" ->
     (match coll with
      | `Vec -> buf_add b ("(Clj_core.Vec.contains_ " ^ a 0 ^ " " ^ a 1 ^ ")")
      | `List -> buf_add b ("(List.mem " ^ a 1 ^ " " ^ a 0 ^ ")")
      | `Set -> buf_add b ("(Clj_core.Set.contains_ " ^ a 0 ^ " " ^ a 1 ^ ")")
      | `Map -> buf_add b ("(Clj_core.Map.contains_ " ^ a 0 ^ " " ^ a 1 ^ ")")
      | `Seq -> buf_add b ("(" ^ "Clj_core.Seq.mem" ^ " " ^ a 1 ^ " " ^ a 0 ^ ")")
      | `Str -> buf_add b "(failwith \"contains? on string\")")
   | "get" when (match repr (t 0) with TAny -> true | _ -> false) ->
     let mstr = flat_map_arg (List.nth args 0) in
     let kd = box_of (List.nth args 1) in
     if List.length args = 3 then buf_add b (dyn_map_get_or (box_of (List.nth args 2)) mstr kd)
     else buf_add b (dyn_map_get mstr kd)
   | "get" ->
     (match coll with
      | `Vec ->
        if List.length args = 3 then
          let el = match repr (t 0) with TVec e -> e | _ -> TUnit in
          let d = if is_any el then box_of (List.nth args 2) else a 2 in
          buf_add b ("(match " ^ sconsi 0 "Clj_core.Vec.nth_opt" "Clj_core.Vec.nth_opt_local" ^ " " ^ a 0 ^ " " ^ a 1 ^ " with Some v -> v | None -> " ^ d ^ ")")
        else buf_add b ("(" ^ sconsi 0 "Clj_core.Vec.get" "Clj_core.Vec.get_local" ^ " " ^ a 0 ^ " " ^ a 1 ^ ")")
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
           if List.length args = 3 then
             let vt = match repr (t 0) with TMap (_, v) -> v | _ -> TAny in
             let dv = if is_any vt then box_of (List.nth args 2) else a 2 in
             buf_add b ("(Clj_core.Map.get_or " ^ dv ^ " " ^ a 0 ^ " " ^ a 1 ^ ")")
           else buf_add b ("(Clj_core.Map.get " ^ a 0 ^ " " ^ a 1 ^ ")"))
      | `Seq ->
        if List.length args = 3 then
          buf_add b ("(match Clj_core.Seq.nth_opt " ^ a 0 ^ " " ^ a 1 ^ " with Some v -> v | None -> " ^ a 2 ^ ")")
        else buf_add b ("(Clj_core.Seq.nth_opt " ^ a 0 ^ " " ^ a 1 ^ ")")
      | `Str -> buf_add b "(failwith \"get on string\")")
   | "nth" ->
     (match repr (t 0) with
      | TTuple ts ->
        let idx = match (List.nth args 1).desc with EInt i -> i | _ -> 0 in
        let names = List.mapi (fun i _ -> "__t" ^ string_of_int i) ts in
        buf_add b ("(let (" ^ String.concat "," names ^ ") = " ^ a 0 ^ " in " ^ List.nth names idx ^ ")")
      | _ ->
      (match coll with
      | `Vec ->
        if List.length args = 3 then buf_add b ("(match " ^ sconsi 0 "Clj_core.Vec.nth_opt" "Clj_core.Vec.nth_opt_local" ^ " " ^ a 0 ^ " " ^ a 1 ^ " with Some v -> v | None -> " ^ a 2 ^ ")")
        else buf_add b ("(" ^ sconsi 0 "Clj_core.Vec.nth" "Clj_core.Vec.nth_local" ^ " " ^ a 0 ^ " " ^ a 1 ^ ")")
      | `List ->
        if List.length args = 3 then buf_add b ("(match List.nth_opt " ^ a 0 ^ " " ^ a 1 ^ " with Some v -> v | None -> " ^ a 2 ^ ")")
        else buf_add b ("(List.nth " ^ a 0 ^ " " ^ a 1 ^ ")")
      | `Str ->
        if List.length args = 3 then buf_add b ("(if " ^ a 1 ^ " < String.length " ^ a 0 ^ " then " ^ a 0 ^ ".[" ^ a 1 ^ "] else " ^ a 2 ^ ")")
        else buf_add b ("(" ^ a 0 ^ ".[" ^ a 1 ^ "])")
      | `Seq ->
        if List.length args = 3 then buf_add b ("(match " ^ "Clj_core.Seq.nth_opt" ^ " " ^ a 0 ^ " " ^ a 1 ^ " with Some v -> v | None -> " ^ a 2 ^ ")")
        else buf_add b ("(" ^ "Clj_core.Seq.nth" ^ " " ^ a 0 ^ " " ^ a 1 ^ ")")
      | _ -> buf_add b "(failwith \"nth\")"))
   | "conj" ->
     let elem_ty = match repr (t 0) with TVec el -> el | TList el -> el | TSet el -> el | _ -> TUnit in
     let arg i = conv elem_ty (t i) (a i) in
     if is_any (t 0) then
       (* dyn destination: keep the collection's own tag at runtime *)
       buf_add b
         (List.fold_left
            (fun acc i -> "(Lg_rt.dyn_conj " ^ acc ^ " " ^ conv TAny (t i) (a i) ^ ")")
            (a 0) (List.init (List.length args - 1) (fun i -> i + 1)))
     else
     (match coll with
      | `Vec ->
        buf_add b (List.fold_left (fun acc i -> "(Clj_core.Vec.conj " ^ acc ^ " " ^ arg i ^ ")") (a 0) (List.init (List.length args - 1) (fun i -> i + 1)))
      | `List ->
        buf_add b (List.fold_left (fun acc i -> "(" ^ arg i ^ " :: " ^ acc ^ ")") (a 0) (List.init (List.length args - 1) (fun i -> List.length args - 1 - i)))
      | `Set ->
        buf_add b (List.fold_left (fun acc i -> "(Clj_core.Set.conj " ^ acc ^ " " ^ arg i ^ ")") (a 0) (List.init (List.length args - 1) (fun i -> i + 1)))
      | `Map ->
        (* a map entry is a (k, v) tuple — the OCaml pair `Map.conj`
           takes directly; dyn/vec entries destructure first *)
        let kt, vt = match repr (t 0) with TMap (k, v) -> (k, v) | _ -> (TAny, TAny) in
        let one acc i =
          let e = a i in
          match repr (t i) with
          | TTuple [ tk; tv ] ->
            "(Clj_core.Map.conj " ^ acc ^ " (" ^ conv kt tk ("(fst " ^ e ^ ")") ^ ", " ^ conv vt tv ("(snd " ^ e ^ ")") ^ "))"
          | TAny ->
            "(match Lg_rt.dyn_to_list " ^ e ^ " with [k; v] -> Clj_core.Map.conj " ^ acc ^ " (" ^ conv kt TAny "k" ^ ", " ^ conv vt TAny "v" ^ ") | _ -> failwith \"conj: map entry must be [k v]\")"
          | TMap _ -> "(Clj_core.Map.merge " ^ acc ^ " " ^ e ^ ")"
          | _ ->
            let pe =
              (match repr (List.nth args i).ety with
               | TVec el | TSeq el | TList el -> el
               | _ -> TAny)
            in
            "(match " ^ as_list (List.nth args i) ^ " with [k; v] -> Clj_core.Map.conj " ^ acc ^ " (" ^ conv kt pe "k" ^ ", " ^ conv vt pe "v" ^ ") | _ -> failwith \"conj: map entry must be [k v]\")"
        in
        buf_add b (List.fold_left one (a 0) (List.init (List.length args - 1) (fun i -> i + 1)))
      | `Seq ->
        buf_add b (List.fold_left (fun acc i -> "(Clj_core.Seq.cons " ^ arg i ^ " " ^ acc ^ ")") (a 0) (List.init (List.length args - 1) (fun i -> i + 1)))
      | `Str -> buf_add b "(failwith \"conj on string\")")
   | "assoc" ->
     if is_any (t 0) then
       (* dyn destination: dispatch on the collection tag at runtime *)
       let cv i = let e = List.nth args i in conv TAny e.ety (arg_str e) in
       let rec go acc i =
         if i + 1 >= List.length args then acc
         else go ("(Lg_rt.dyn_assoc " ^ acc ^ " " ^ cv i ^ " " ^ cv (i + 1) ^ ")") (i + 2)
       in
       buf_add b (go (a 0) 1)
     else
     (match coll with
      | `Vec ->
        let el = match repr (t 0) with TVec e -> e | _ -> TUnit in
        let e = List.nth args 2 in
        let v = conv el e.ety (arg_str e) in
        buf_add b ("(Clj_core.Vec.assoc " ^ a 0 ^ " " ^ a 1 ^ " " ^ v ^ ")")
      | `Map ->
        let kt, vt = match repr (t 0) with TMap (k, v) -> (k, v) | _ -> (TUnit, TUnit) in
        let cv t i = let e = List.nth args i in conv t e.ety (arg_str e) in
        let rec go acc i =
          if i + 1 >= List.length args then acc
          else go ("(Clj_core.Map.assoc " ^ acc ^ " " ^ cv kt i ^ " " ^ cv vt (i + 1) ^ ")") (i + 2)
        in
        buf_add b (go (a 0) 1)
      | _ -> buf_add b "(failwith \"assoc\")")
   | "dissoc" ->
     buf_add b (List.fold_left (fun acc i -> "(Clj_core.Map.dissoc " ^ acc ^ " " ^ a i ^ ")") (a 0) (List.init (List.length args - 1) (fun i -> i + 1)))
   | "keys" ->
     buf_add b
       (if is_any (t 0) then "(List.of_seq (Clj_core.Map.keys (Lg_rt.as_map " ^ a 0 ^ ")))"
        else "(List.of_seq (" ^ "Clj_core.Map.keys" ^ " " ^ a 0 ^ "))")
   | "vals" ->
     buf_add b
       (if is_any (t 0) then "(Lg_rt.dyn_vals (Lg_rt.as_map " ^ a 0 ^ "))"
        else "(List.of_seq (" ^ "Clj_core.Map.vals" ^ " " ^ a 0 ^ "))")
   | "merge" ->
     buf_add b
       (if is_any (t 0) then
          (* every operand is converted to a flat (dyn,dyn) map: `any`
             args unwrap via as_map, concrete maps box element-wise *)
          let cm i = conv (TMap (TAny, TAny)) (t i) (a i) in
          "(Lg_rt.flat_merge " ^ cm 0
          ^ " [" ^ String.concat "; " (List.map cm (List.init (List.length args - 1) (fun i -> i + 1))) ^ "])"
        else
          List.fold_left (fun acc i -> "(Clj_core.Map.merge " ^ acc ^ " " ^ a i ^ ")") (a 0)
            (List.init (List.length args - 1) (fun i -> i + 1)))
   | "kw-get" ->
     let kd = "(Lg_rt.DKw " ^ a 0 ^ ")" in
     (match repr (t 1) with
      | TMap (k, _) when is_any k ->
        if List.length args = 3 then buf_add b (dyn_map_get_or (box_of (List.nth args 2)) (a 1) kd)
        else buf_add b (dyn_map_get (a 1) kd)
      | TAny ->
        let mstr = flat_map_arg (List.nth args 1) in
        if List.length args = 3 then buf_add b (dyn_map_get_or (box_of (List.nth args 2)) mstr kd)
        else buf_add b (dyn_map_get mstr kd)
      | _ ->
        if List.length args = 3 then buf_add b ("(Clj_core.Map.get_or " ^ a 2 ^ " " ^ a 1 ^ " " ^ a 0 ^ ")")
        else buf_add b ("(Clj_core.Map.get " ^ a 1 ^ " " ^ a 0 ^ ")"))
   | "vec" ->
     let flows =
       match repr (List.nth args 0).ety with
       | TVec _ | TList _ | TMap _ -> true
       | _ -> false
     in
     let vl = if flows && sloc 0 then "Clj_core.Vec.of_list_local" else "Clj_core.Vec.of_list" in
     buf_add b ("(" ^ vl ^ " " ^ as_list (List.nth args 0) ^ ")")
   | "peek" ->
     let el = match repr ret with TOption e -> e | _ -> TAny in
     buf_add b ("(" ^ (if !oxcaml && sloc 0 then "Clj_core.Vec.peek_local" else "Clj_core.Vec.peek") ^ " " ^ conv (TVec el) (t 0) (a 0) ^ ")")
   | "pop" ->
     let el = match repr ret with TVec e -> e | _ -> TAny in
     buf_add b ("(Clj_core.Vec.pop " ^ conv (TVec el) (t 0) (a 0) ^ ")")
   | "set" -> buf_add b ("(Clj_core.Set.of_list " ^ as_list (List.nth args 0) ^ ")")
   | "disj" ->
     if is_any (t 0) then
       buf_add b
         (List.fold_left
            (fun acc i -> "(Clj_core.Set.disj " ^ acc ^ " " ^ conv TAny (t i) (a i) ^ ")")
            ("(Lg_rt.as_set " ^ a 0 ^ ")") (List.init (List.length args - 1) (fun i -> i + 1)))
     else
       buf_add b (List.fold_left (fun acc i -> "(Clj_core.Set.disj " ^ acc ^ " " ^ a i ^ ")") (a 0) (List.init (List.length args - 1) (fun i -> i + 1)))
   | "union" ->
     if is_any (t 0) || is_any (t 1) then
       buf_add b ("(Clj_core.Set.union " ^ conv (TSet TAny) (t 0) (a 0) ^ " " ^ conv (TSet TAny) (t 1) (a 1) ^ ")")
     else buf_add b ("(Clj_core.Set.union " ^ a 0 ^ " " ^ a 1 ^ ")")
   | "map" ->
     (* printer builtins passed as fns adapt to the element type *)
     let f = (match (List.nth args 0).desc, repr (t 1) with
              | EBuiltin ("println" | "print"), (TSeq el | TVec el | TList el | TSet el) -> "(fun x -> print_endline (" ^ gen_printer el ^ " x))"
              | EBuiltin ("str" | "pr-str"), (TSeq el | TVec el | TList el | TSet el) -> "(fun x -> (" ^ gen_printer el ^ " x))"
              | _ -> a 0) in
     buf_add b (realize ret ("(" ^ sfn "map" ^ " " ^ f ^ " " ^ as_seq (List.nth args 1) ^ ")"))
   | "filter" -> buf_add b (realize ret ("(" ^ sfn "filter" ^ " " ^ a 0 ^ " " ^ as_seq (List.nth args 1) ^ ")"))
   | "remove" -> buf_add b (realize ret ("(" ^ sfn "remove" ^ " " ^ a 0 ^ " " ^ as_seq (List.nth args 1) ^ ")"))
   | "reduce" ->
     (* bind the collection once: emitting `a 2` both as a match scrutinee
        and inside the fold call would duplicate its effects *)
     let cn = "rc__" ^ string_of_int (fresh_uid ()) in
     buf_add b ("(let " ^ cn ^ " = " ^ a 2 ^ " in "
                ^ (match coll_kind (t 2) with
                   | `Vec -> sconsi 2 "Clj_core.Vec.reduce" "Clj_core.Vec.reduce_local" ^ " " ^ a 0 ^ " " ^ a 1 ^ " " ^ cn
                   | `Set -> sconsi 2 "Clj_core.Set.fold" "Clj_core.Set.fold_local" ^ " " ^ a 0 ^ " " ^ a 1 ^ " " ^ cn
                   | `Map -> sconsi 2 "Clj_core.Map.fold" "Clj_core.Map.fold_local" ^ " (fun acc k v -> " ^ a 0 ^ " acc (k, v)) " ^ a 1 ^ " " ^ cn
                   | `Str -> "List.fold_left " ^ a 0 ^ " " ^ a 1 ^ " (Lg_rt.string_chars " ^ cn ^ ")"
                   | `Seq -> "Clj_core.Seq.reduce " ^ a 0 ^ " " ^ a 1 ^ " " ^ cn
                   | `List -> "List.fold_left " ^ a 0 ^ " " ^ a 1 ^ " " ^ cn)
                ^ ")")
   | "mapv" ->
     (match coll_kind (t 1) with
      | `Vec -> buf_add b ("(" ^ sconsi 1 "Clj_core.Vec.map" "Clj_core.Vec.map_local" ^ " " ^ a 0 ^ " " ^ a 1 ^ ")")
      | _ -> buf_add b ("(Clj_core.Vec.of_list (List.map " ^ a 0 ^ " " ^ as_list (List.nth args 1) ^ "))"))
   | "filterv" ->
     (match coll_kind (t 1) with
      | `Vec -> buf_add b ("(" ^ sconsi 1 "Clj_core.Vec.filter" "Clj_core.Vec.filterv_local" ^ " " ^ a 0 ^ " " ^ a 1 ^ ")")
      | _ -> buf_add b ("(Clj_core.Vec.of_list (List.filter " ^ a 0 ^ " " ^ as_list (List.nth args 1) ^ "))"))
   | "into" ->
     let src_items = as_list (List.nth args 1) in
     let src_el =
       match repr (t 1) with
       | TVec x | TList x | TSeq x | TSet x -> x | TMap (k, v) -> TTuple [ k; v ] | TString -> TChar | _ -> TAny
     in
     let items_for dst_el =
       if is_any dst_el && not (is_any src_el) then "(List.map (fun e -> " ^ box_deep src_el "e" ^ ") " ^ src_items ^ ")"
       else if (not (is_any dst_el)) && is_any src_el then "(List.map " ^ unbox_fn dst_el ^ " " ^ src_items ^ ")"
       else src_items
     in
     (match coll with
      | `Vec ->
        let de = match repr (t 0) with TVec x -> x | _ -> TAny in
        buf_add b ("(List.fold_left Clj_core.Vec.conj " ^ a 0 ^ " " ^ items_for de ^ ")")
      | `Set ->
        let de = match repr (t 0) with TSet x -> x | _ -> TAny in
        buf_add b ("(List.fold_left Clj_core.Set.conj " ^ a 0 ^ " " ^ items_for de ^ ")")
      | `Map ->
        (* elements arrive as (k, v) tuples (map src), or as [k v]
           pair-vecs/pair-lists that must be destructured first; each
           component crosses the any boundary via conv *)
        let kt, vt = match repr (t 0) with TMap (k, v) -> (k, v) | _ -> (TAny, TAny) in
        let body =
          (match repr (t 1) with
           | TMap (sk, sv) -> "Clj_core.Map.conj m (" ^ conv kt sk "(fst e)" ^ ", " ^ conv vt sv "(snd e)" ^ ")"
           | TVec x | TList x | TSet x ->
             (match repr x with
              | TTuple [ tk; sv ] -> "Clj_core.Map.conj m (" ^ conv kt tk "(fst e)" ^ ", " ^ conv vt sv "(snd e)" ^ ")"
              | TList sv -> "(match e with [k; v] -> Clj_core.Map.conj m (" ^ conv kt sv "k" ^ ", " ^ conv vt sv "v" ^ ") | _ -> m)"
              | TAny -> "(match Lg_rt.dyn_to_list e with [k; v] -> Clj_core.Map.conj m (" ^ conv kt TAny "k" ^ ", " ^ conv vt TAny "v" ^ ") | _ -> m)"
              | TVec c -> "(match Clj_core.Vec.to_list e with [k; v] -> Clj_core.Map.conj m (" ^ conv kt c "k" ^ ", " ^ conv vt c "v" ^ ") | _ -> m)"
              | TSet c -> "(match Clj_core.Set.to_list e with [k; v] -> Clj_core.Map.conj m (" ^ conv kt c "k" ^ ", " ^ conv vt c "v" ^ ") | _ -> m)"
              | _ -> "Clj_core.Map.conj m e")
           | _ -> "Clj_core.Map.conj m e")
        in
        buf_add b ("(List.fold_left (fun m e -> " ^ body ^ ") " ^ a 0 ^ " " ^ src_items ^ ")")
      | `List ->
        let de = match repr (t 0) with TList x -> x | _ -> TAny in
        buf_add b ("(" ^ items_for de ^ " @ " ^ a 0 ^ ")")
      | `Seq ->
        (match repr (t 0) with
        | TSeq de -> buf_add b ("(Clj_core.Seq.fold_left (fun acc x -> Clj_core.Seq.cons x acc) " ^ a 0 ^ " " ^ seq_elem_conv de (t 1) (as_seq (List.nth args 1)) ^ ")")
        | _ -> buf_add b ("(Clj_core.Seq.fold_left (fun acc x -> Clj_core.Seq.cons x acc) " ^ a 0 ^ " " ^ as_seq (List.nth args 1) ^ ")"))
      | `Str -> buf_add b "(failwith \"into string\")")
   | "int?" | "float?" | "bool?" | "char?" | "string?" | "keyword?" | "symbol?"
   | "unit?" | "list?" | "vec?" | "set?" | "coll?" | "seq?" | "number?" | "fn?" ->
     (* tag check on dyn; constant-folded when the static type already
        answers the question *)
     let tags =
       match name with
       | "int?" -> [ "DInt" ] | "float?" -> [ "DFloat" ] | "bool?" -> [ "DBool" ]
       | "char?" -> [ "DChar" ] | "string?" -> [ "DStr" ] | "keyword?" -> [ "DKw" ]
       | "symbol?" -> [ "DSym" ] | "list?" -> [ "DList" ] | "vec?" -> [ "DVec" ]
       | "set?" -> [ "DSet" ] | "seq?" -> [ "DList" ]
       | "coll?" -> [ "DVec"; "DList"; "DMap"; "DSet" ]
       | "number?" -> [ "DInt"; "DFloat" ] | _ -> []
     in
     (match repr (t 0) with
      | TAny ->
        if name = "unit?" then
          buf_add b ("(match " ^ a 0 ^ " with Lg_rt.DUnit -> true | _ -> false)")
        else if name = "fn?" then buf_add b "false"  (* fns are never boxed *)
        else buf_add b ("(match " ^ a 0 ^ " with "
                        ^ String.concat " | " (List.map (fun tg -> "Lg_rt." ^ tg ^ " _") tags)
                        ^ " -> true | _ -> false)")
      | rep ->
        let answer =
          match name, rep with
          | "unit?", TUnit -> Some true
          | "unit?", _ -> Some false
          | "fn?", TFun _ -> Some true
          | "fn?", _ -> Some false
          | "coll?", (TVec _ | TList _ | TMap _ | TSet _) -> Some true
          | "coll?", _ -> Some false
          | "number?", (TInt | TFloat) -> Some true
          | "number?", _ -> Some false
          | "seq?", (TList _ | TSeq _) -> Some true
          | "seq?", _ -> Some false
          | "int?", TInt | "float?", TFloat | "bool?", TBool | "char?", TChar
          | "string?", TString | "keyword?", TKeyword | "symbol?", TSymbol
          | "list?", TList _ | "vec?", TVec _ | "set?", TSet _ -> Some true
          | _ -> Some false
        in
        (match answer with
         | Some b' -> buf_add b (string_of_bool b')
         | None -> buf_add b ("(match " ^ a 0 ^ " with None -> true | _ -> false)")))
   | "zero?" | "pos?" | "neg?" | "even?" | "odd?" ->
     let unb = if is_any (t 0) then "(Lg_rt.as_int " ^ a 0 ^ ")" else a 0 in
     (match name with
      | "zero?" -> buf_add b ("(" ^ unb ^ " = 0)")
      | "pos?" -> buf_add b ("(" ^ unb ^ " > 0)")
      | "neg?" -> buf_add b ("(" ^ unb ^ " < 0)")
      | "even?" -> buf_add b ("(" ^ unb ^ " mod 2 = 0)")
      | _ -> buf_add b ("(" ^ unb ^ " mod 2 <> 0)"))
   | "take" -> buf_add b (realize ret ("(" ^ sfn "take" ^ " " ^ a 0 ^ " " ^ as_seq (List.nth args 1) ^ ")"))
   | "drop" -> buf_add b (realize ret ("(" ^ sfn "drop" ^ " " ^ a 0 ^ " " ^ as_seq (List.nth args 1) ^ ")"))
   | "take-while" -> buf_add b ("(" ^ sfn "take-while" ^ " " ^ a 0 ^ " " ^ as_seq (List.nth args 1) ^ ")")
   | "drop-while" -> buf_add b ("(" ^ sfn "drop-while" ^ " " ^ a 0 ^ " " ^ as_seq (List.nth args 1) ^ ")")
   | "range" ->
     (match List.length args with
      | 0 -> buf_add b ("(" ^ sfn "ints" ^ " ())")
      | 1 -> buf_add b ("(" ^ sfn "range" ^ " " ^ a 0 ^ ")")
      | 2 -> buf_add b ("(" ^ sfn "range" ^ " ~start:" ^ a 0 ^ " " ^ a 1 ^ ")")
      | _ -> buf_add b ("(" ^ sfn "range" ^ " ~start:" ^ a 0 ^ " ~step:" ^ a 2 ^ " " ^ a 1 ^ ")"))
   | "iterate" -> buf_add b ("(" ^ sfn "iterate" ^ " " ^ a 0 ^ " " ^ a 1 ^ ")")
   | "repeat" ->
     if List.length args = 1 then buf_add b ("(" ^ sfn "repeat" ^ " " ^ a 0 ^ ")")
     else buf_add b ("(" ^ sfn "take" ^ " " ^ a 0 ^ " (" ^ sfn "repeat" ^ " " ^ a 1 ^ "))")
   | "repeatedly" ->
     if List.length args = 1 then buf_add b ("(" ^ sfn "repeatedly" ^ " (fun () -> " ^ a 0 ^ " ())")
     else buf_add b ("(" ^ sfn "take" ^ " " ^ a 0 ^ " (" ^ sfn "repeatedly" ^ " (fun () -> " ^ a 1 ^ " ())))")
   | "cycle" -> buf_add b ("(" ^ sfn "cycle" ^ " " ^ as_seq (List.nth args 0) ^ ")")
   | "interleave" -> buf_add b (realize ret ("(" ^ sfn "interleave" ^ " " ^ as_seq (List.nth args 0) ^ " " ^ as_seq (List.nth args 1) ^ ")"))
   | "map-indexed" -> buf_add b ("(" ^ sfn "map-indexed" ^ " " ^ a 0 ^ " " ^ as_seq (List.nth args 1) ^ ")")
   | "keep" | "filter-map" -> buf_add b (realize ret ("(" ^ sfn "filter-map" ^ " " ^ a 0 ^ " " ^ as_seq (List.nth args 1) ^ ")"))
   | "take-nth" -> buf_add b ("(" ^ sfn "take-nth" ^ " " ^ a 0 ^ " " ^ as_seq (List.nth args 1) ^ ")")
   | "partition" -> buf_add b (realize ret ("(" ^ sfn "partition" ^ " " ^ a 0 ^ " " ^ as_seq (List.nth args 1) ^ ")"))
   | "partition-all" -> buf_add b ("(" ^ sfn "partition-all" ^ " " ^ a 0 ^ " " ^ as_seq (List.nth args 1) ^ ")")
   | "nthrest" -> buf_add b ("(" ^ sfn "nthrest" ^ " " ^ as_seq (List.nth args 0) ^ " " ^ a 1 ^ ")")
   | "drop-last" -> buf_add b ("(" ^ sfn "drop-last" ^ " " ^ a 0 ^ " " ^ as_seq (List.nth args 1) ^ ")")
   | "take-last" -> buf_add b ("(Clj_core.Seq.of_list (Clj_core.Seq.take_last " ^ a 0 ^ " " ^ as_seq (List.nth args 1) ^ "))")
   | "split-at" -> buf_add b ("(let (x, y) = (Clj_core.Seq.split_at " ^ a 0 ^ " " ^ as_seq (List.nth args 1) ^ ") in (Clj_core.Vec.of_list [x; y]))")
   | "split-with" -> buf_add b ("(let (x, y) = (Clj_core.Seq.split_with " ^ a 0 ^ " " ^ as_seq (List.nth args 1) ^ ") in (Clj_core.Vec.of_list [x; y]))")
   | "reductions" -> buf_add b ("(" ^ sfn "reductions" ^ " " ^ a 0 ^ " " ^ a 1 ^ " " ^ as_seq (List.nth args 2) ^ ")")
   | "dedupe" -> buf_add b (realize ret ("(" ^ sfn "dedupe" ^ " " ^ as_seq (List.nth args 0) ^ ")"))
   | "not-empty" -> buf_add b ("(let s = " ^ as_seq (List.nth args 0) ^ " in if " ^ "Clj_core.Seq.is_empty" ^ " s then None else " ^ (if call_local then "(stack_ (Some s))" else "Some s") ^ ")")
   | "lazy-seq" -> buf_add b ("(" ^ sfn "lazy-seq" ^ " (fun () -> " ^ as_seq (List.nth args 0) ^ "))")
   | "doall" -> buf_add b (as_list (List.nth args 0))
   | "dorun" -> buf_add b ("(" ^ "Clj_core.Seq.iter" ^ " (fun _ -> ()) " ^ as_seq (List.nth args 0) ^ ")")
   | "concat" -> buf_add b (realize ret ("(" ^ sfn "concat" ^ " (Clj_core.Seq.of_list [" ^ String.concat "; " (List.map as_seq args) ^ "]))"))
   | "apply" -> buf_add b (emit_apply args)
   | "atom" ->
     if is_any ret then buf_add b ("(Clj_core.Atom.atom " ^ box_of (List.nth args 0) ^ ")")
     else (match repr ret with TAtom p when is_any p -> buf_add b ("(Clj_core.Atom.atom " ^ box_of (List.nth args 0) ^ ")") | _ -> buf_add b ("(Clj_core.Atom.atom " ^ a 0 ^ ")"))
   | "deref" -> buf_add b ("(Clj_core.Atom.deref " ^ a 0 ^ ")")
   | "reset!" ->
     let av = match repr (t 0) with TAtom p -> p | _ -> TAny in
     buf_add b ("(Clj_core.Atom.reset_bang " ^ a 0 ^ " " ^ conv av (t 1) (a 1) ^ ")")
   | "no-match" -> buf_add b "(Lg_rt.no_match ())"
   | "dyn-eq" -> buf_add b ("(Lg_rt.dyn_eq " ^ a 0 ^ " " ^ box_of (List.nth args 1) ^ ")")
   | "select-keys" ->
     let dyned = match repr (t 0) with TMap (k, _) -> is_any k | TAny -> true | _ -> false in
     if dyned then
       (* dyn-keyed map: convert to nest for select_keys, back to flat *)
       buf_add b ("(Lg_rt.flat_of_nest (Clj_core.Map.select_keys " ^ dyn_map_arg (List.nth args 0)
                  ^ " (List.map (fun k -> Lg_rt.DKw k) " ^ as_list (List.nth args 1) ^ ")))")
     else
       buf_add b ("(Clj_core.Map.select_keys " ^ a 0 ^ " " ^ as_list (List.nth args 1) ^ ")")
   | "update" ->
     (* flat_map_arg covers both the `any` map (as_map unwrap) and an
        open-coll map (already a flat (dyn,dyn) map); the result is a map
        type in both cases, so no DMap wrap *)
     let kt, vt = match repr (t 0) with TMap (k, v) -> (k, v) | _ -> (TAny, TAny) in
     let mstr = flat_map_arg (List.nth args 0) in
     let kd = conv kt (t 1) (a 1) in
     let pf, rf = match repr (t 2) with TFun ([ p ], r) -> (p, r) | _ -> (TAny, TAny) in
     let uv = conv pf vt "uv__" in
     let res = conv vt rf ("(" ^ a 2 ^ " " ^ uv ^ ")") in
     let miss =
       if List.length args = 4 then conv vt (t 3) (a 3)
       else "failwith \"update: missing key\""
     in
     buf_add b ("(Clj_core.Map.assoc " ^ mstr ^ " " ^ kd
                ^ " (match Clj_core.Map.get " ^ mstr ^ " " ^ kd
                ^ " with Some uv__ -> " ^ res ^ " | None -> " ^ miss ^ "))")
   | "get-in" | "assoc-in" | "update-in" ->
     let ks_arg = List.nth args 1 in
     (* clj-core's get_in/assoc_in walk 'k keys of the nest map — dyn here —
        so keyword paths are boxed to DKw and dyn paths pass through *)
     let kw_list =
       match repr ks_arg.ety with
       | TList el | TVec el when is_any el -> as_list ks_arg
       | _ -> "(List.map (fun k -> Lg_rt.DKw k) " ^ as_list ks_arg ^ ")"
     in
     if name = "get-in" then
       if List.length args = 3 then
         buf_add b ("(match Clj_core.Map.get_in " ^ dyn_map_arg (List.nth args 0) ^ " " ^ kw_list
                    ^ " with Some n -> (match n with Clj_core.Map.Leaf d -> d | Clj_core.Map.Nest s -> Lg_rt.DMap (Lg_rt.flat_of_nest s)) | None -> " ^ box_of (List.nth args 2) ^ ")")
       else
         buf_add b ("(match Clj_core.Map.get_in " ^ dyn_map_arg (List.nth args 0) ^ " " ^ kw_list
                    ^ " with Some n -> (match n with Clj_core.Map.Leaf d -> Some d | Clj_core.Map.Nest s -> Some (Lg_rt.DMap (Lg_rt.flat_of_nest s))) | None -> None)")
     else if name = "update-in" then
       let miss =
         if List.length args = 4 then box_of (List.nth args 3)
         else "failwith \"update-in: missing key\""
       in
       let pf, rf = match repr (t 2) with TFun ([ p ], r) -> (p, r) | _ -> (TAny, TAny) in
       let uv = conv pf TAny "uv__" in
       let res = conv TAny rf ("(" ^ a 2 ^ " " ^ uv ^ ")") in
       buf_add b
         ("(let um__ = " ^ dyn_map_arg (List.nth args 0) ^ " and uks__ = " ^ kw_list ^ " in "
          ^ "Lg_rt.dyn_map_of_nest_map (Clj_core.Map.assoc_in um__ uks__ (Clj_core.Map.Leaf "
          ^ "(match Clj_core.Map.get_in um__ uks__ with Some (Clj_core.Map.Leaf d) -> (match d with uv__ -> "
          ^ res ^ ") | Some (Clj_core.Map.Nest s) -> (match Lg_rt.DMap (Lg_rt.flat_of_nest s) with uv__ -> " ^ res
          ^ ") | None -> (match " ^ miss ^ " with uv__ -> " ^ res ^ ")))))")
     else
       let v_arg = List.nth args 2 in
       let boxed = if is_any v_arg.ety then arg_str v_arg else box_of v_arg in
       buf_add b ("(Lg_rt.dyn_map_of_nest_map (Clj_core.Map.assoc_in " ^ dyn_map_arg (List.nth args 0)
                  ^ " " ^ kw_list ^ " (Clj_core.Map.Leaf " ^ boxed ^ ")))")
   | "comp" -> buf_add b ("(fun x__ -> " ^ a 0 ^ " (" ^ a 1 ^ " x__))")
   | "juxt" ->
     (* each branch result needs boxing when juxt's vec element is `any`
        (hetero juxt like (juxt inc str)) *)
     let elem = match repr ret with TFun (_, TVec e) -> e | _ -> TAny in
     let res i = match repr (t i) with TFun (_, r) -> r | _ -> TAny in
     let call i =
       let e = a i ^ " x__" in
       if is_any elem && not (is_any (res i)) then box_deep (res i) e else e
     in
     buf_add b ("(fun x__ -> (Clj_core.Vec.of_list [" ^ call 0 ^ "; " ^ call 1 ^ "]))")
   | "partial" ->
     buf_add b ("(fun x__ -> (" ^ a 0 ^ String.concat "" (List.init (List.length args - 1) (fun i -> " " ^ a (i + 1))) ^ " x__))")
   | "mapcat" ->
     let coerce =
       match repr (t 0) with
       | TFun (_, r) ->
         (match repr r with
          | TSeq _ -> "(fun s -> s)"
          | TVec _ -> if call_local then "Clj_core.Seq.of_vec_local" else "Clj_core.Seq.of_vec"
          | TSet _ -> if call_local then "Clj_core.Seq.of_set_local" else "Clj_core.Seq.of_set"
          | TMap _ -> if call_local then "Clj_core.Seq.of_map_local" else "Clj_core.Seq.of_map"
          | TString -> if call_local then "Clj_core.Seq.of_string_local" else "Clj_core.Seq.of_string"
          | TAny -> "Lg_rt.dyn_to_seq"
          | _ -> "Clj_core.Seq.of_list")
       | _ -> "Clj_core.Seq.of_list"
     in
     buf_add b (realize ret ("(" ^ sfn "mapcat" ^ " (fun x -> " ^ coerce ^ " (" ^ a 0 ^ " x)) " ^ as_seq (List.nth args 1) ^ ")"))
   | "interpose" -> buf_add b (realize ret ("(" ^ sfn "interpose" ^ " " ^ a 0 ^ " " ^ as_seq (List.nth args 1) ^ ")"))
   | "reverse" -> buf_add b (realize ret ("(" ^ "Clj_core.Seq.reverse" ^ " " ^ as_seq (List.nth args 0) ^ ")"))
   | "distinct" -> buf_add b (realize ret ("(" ^ sfn "distinct" ^ " " ^ as_seq (List.nth args 0) ^ ")"))
   | "second" -> buf_add b ("(" ^ "Clj_core.Seq.second" ^ " " ^ as_seq (List.nth args 0) ^ ")")
   | "last" -> buf_add b ("(" ^ "Clj_core.Seq.last" ^ " " ^ as_seq (List.nth args 0) ^ ")")
   | "butlast" -> buf_add b (realize ret ("(" ^ "Clj_core.Seq.drop_last" ^ " 1 " ^ as_seq (List.nth args 0) ^ ")"))
   | "min" ->
     buf_add b
       (if is_any (t 0) || is_any (t 1) then
          conv ret TAny ("(Lg_rt.dyn_min " ^ conv TAny (t 0) (a 0) ^ " " ^ conv TAny (t 1) (a 1) ^ ")")
        else "(Stdlib.min " ^ a 0 ^ " " ^ a 1 ^ ")")
   | "max" ->
     buf_add b
       (if is_any (t 0) || is_any (t 1) then
          conv ret TAny ("(Lg_rt.dyn_max " ^ conv TAny (t 0) (a 0) ^ " " ^ conv TAny (t 1) (a 1) ^ ")")
        else "(Stdlib.max " ^ a 0 ^ " " ^ a 1 ^ ")")
   | "every?" -> buf_add b ("(" ^ "Clj_core.Seq.every_" ^ " " ^ a 0 ^ " " ^ as_seq (List.nth args 1) ^ ")")
   | "some" -> buf_add b ("(" ^ "Clj_core.Seq.exists" ^ " " ^ a 0 ^ " " ^ as_seq (List.nth args 1) ^ ")")
   | "zipmap" -> buf_add b ("(Clj_core.Map.of_list (List.combine " ^ as_list (List.nth args 0) ^ " " ^ as_list (List.nth args 1) ^ "))")
   | "sort" ->
     if List.length args = 2 then buf_add b ("(Clj_core.Seq.sort ~cmp:" ^ a 0 ^ " " ^ as_seq (List.nth args 1) ^ ")")
     else buf_add b ("(Clj_core.Seq.sort " ^ as_seq (List.nth args 0) ^ ")")
   | "sort-by" -> buf_add b ("(" ^ "Clj_core.Seq.sort" ^ " ~cmp:(fun x y -> Stdlib.compare (" ^ a 0 ^ " x) (" ^ a 0 ^ " y)) " ^ as_seq (List.nth args 1) ^ ")")
   | "group-by" -> buf_add b ("(Lg_rt.group_by " ^ a 0 ^ " " ^ as_list (List.nth args 1) ^ ")")
   | "frequencies" -> buf_add b ("(Lg_rt.frequencies " ^ as_list (List.nth args 0) ^ ")")
   | "swap!" -> buf_add b ("(Clj_core.Atom.swap_bang " ^ a 0 ^ " " ^ a 1 ^ ")")
   | "some?" ->
     buf_add b
       (if is_any (t 0) then "(match " ^ a 0 ^ " with Lg_rt.DUnit | Lg_rt.DOpt None -> false | _ -> true)"
        else "(" ^ a 0 ^ " <> None)")
   | "none?" ->
     buf_add b
       (if is_any (t 0) then "(match " ^ a 0 ^ " with Lg_rt.DUnit | Lg_rt.DOpt None -> true | _ -> false)"
        else "(" ^ a 0 ^ " = None)")
   | _ -> buf_add b ("(failwith \"unhandled builtin " ^ name ^ "\")"))

  end

and seq_elem_conv dst_el src_ty es =
  let src_el = match repr src_ty with
    | TVec x | TList x | TSeq x | TSet x -> x | TMap (k, v) -> TTuple [ k; v ]
    | TString -> TChar | _ -> TAny in
  if is_any dst_el && not (is_any src_el) then
    "(" ^ "Clj_core.Seq.map" ^ " (fun x -> " ^ box_deep src_el "x" ^ ") " ^ es ^ ")"
  else if (not (is_any dst_el)) && is_any src_el then
    "(" ^ "Clj_core.Seq.map" ^ " " ^ unbox_fn dst_el ^ " " ^ es ^ ")"
  else es

and emit_apply args =
  let f = arg_str (List.nth args 0) in
  let xs =
    (match repr (List.nth args 1).ety with
     | TVec _ | TSet _ | TMap _ -> as_list (List.nth args 1)
     | TSeq _ -> "(Clj_core.Seq.to_list " ^ arg_str (List.nth args 1) ^ ")"
     | _ -> arg_str (List.nth args 1))
  in
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
    let elem_t =
      (match repr (List.nth args 1).ety with
       | TVec x | TList x | TSeq x | TSet x -> x | _ -> TAny) in
    (* adapt each destructured item to the callee's parameter type:
       box into dyn when the param is `any`, unbox when the collection
       element is `any` and the param is concrete *)
    let conv i t =
      let ai = "a" ^ string_of_int i in
      if is_any t && not (is_any elem_t) then box_deep elem_t ai
      else if not (is_any t) && is_any elem_t then "(" ^ unbox_fn t ^ " " ^ ai ^ ")"
      else ai
    in
    let last_is_list = match repr (List.nth ts (n - 1)) with TList _ -> true | _ -> false in
    if last_is_list && n >= 2 then
      let rest_el = match repr (List.nth ts (n - 1)) with TList a -> a | _ -> TAny in
      let rest =
        if is_any rest_el && not (is_any elem_t) then "(List.map (fun x -> " ^ box_deep elem_t "x" ^ ") rest)"
        else if not (is_any rest_el) && is_any elem_t then "(List.map (fun x -> " ^ unbox_fn rest_el ^ " x) rest)"
        else "rest"
      in
      "(match " ^ xs ^ " with "
      ^ String.concat "" (List.init (n - 1) (fun i -> Printf.sprintf "a%d :: " i))
      ^ "rest -> " ^ f ^ " "
      ^ String.concat " " (List.init (n - 1) (fun i -> conv i (List.nth ts i)))
      ^ " " ^ rest ^ " | _ -> failwith \"apply: arity\")"
    else
      "(match " ^ xs ^ " with ["
      ^ String.concat "; " (List.init n (fun i -> Printf.sprintf "a%d" i))
      ^ "] -> " ^ f ^ " "
      ^ String.concat " " (List.init n (fun i -> conv i (List.nth ts i)))
      ^ " | _ -> failwith \"apply: arity\")"
  | _ -> "(failwith \"apply\")")

and seq_of_ty t : string =
  match repr t with
  | TVec _ -> "Clj_core.Seq.of_vec"
  | TList _ -> "Clj_core.Seq.of_list"
  | TSet _ -> "Clj_core.Seq.of_set"
  | TMap _ -> "Clj_core.Seq.of_map"
  | TString -> "Clj_core.Seq.of_string"
  | TSeq _ -> "(fun s -> s)"
  | _ -> "Lg_rt.dyn_to_seq"

and list_of_ty t : string =
  match repr t with
  | TVec _ -> "Clj_core.Vec.to_list"
  | TList _ -> "(fun l -> l)"
  | TSet _ -> "Clj_core.Set.to_list"
  | TMap _ -> "(fun m -> List.of_seq (Clj_core.Map.seq m))"
  | TSeq _ -> "Clj_core.Seq.to_list"
  | TString -> "Lg_rt.string_chars"
  | _ -> "Lg_rt.dyn_to_list"

and emit_builtin_value name ty =
  let ats =
    match repr ty with TFun (a, _) -> a | _ -> []
  in
  let arg i = try List.nth ats i with _ -> TAny in
  let sq i = seq_of_ty (arg i) in
  let ls i = list_of_ty (arg i) in
  match name with
  | "+" -> "( + )" | "+." -> "( +. )" | "-" -> "( - )" | "-." -> "( -. )"
  | "*" -> "( * )" | "*." -> "( *. )" | "/" -> "( / )" | "/." -> "( /. )"
  | "=" -> "( = )" | "not=" -> "( <> )" | "<" -> "( < )" | "<=" -> "( <= )"
  | ">" -> "( > )" | ">=" -> "( >= )" | "not" -> "not" | "identity" -> "(fun x -> x)"
  | "inc" -> "(fun x -> x + 1)" | "dec" -> "(fun x -> x - 1)" | "abs" -> "abs"
  | "mod" -> "(fun a b -> a mod b)" | "constantly" -> "(fun x _ -> x)"
  | "cons" -> "(fun x c -> Clj_core.Seq.cons x (" ^ sq 1 ^ " c))"
  | "first" -> "(fun c -> Clj_core.Seq.first (" ^ sq 0 ^ " c))"
  | "rest" -> "(fun c -> Clj_core.Seq.rest (" ^ sq 0 ^ " c))"
  | "map" -> "(fun f c -> Clj_core.Seq.map f (" ^ sq 1 ^ " c))"
  | "filter" -> "(fun f c -> Clj_core.Seq.filter f (" ^ sq 1 ^ " c))"
  | "reduce" | "fold" -> "(fun f i c -> Clj_core.Seq.reduce f i (" ^ sq 2 ^ " c))"
  | "vec" -> "(fun c -> Clj_core.Vec.of_list (" ^ ls 0 ^ " c))"
  | "count" -> "(fun c -> Clj_core.Seq.count (" ^ sq 0 ^ " c))"
  | "empty?" -> "(fun c -> Clj_core.Seq.is_empty (" ^ sq 0 ^ " c))"
  | "str" | "pr-str" -> gen_printer (arg 0)
  | "println" -> "(fun x -> print_endline (" ^ gen_printer (arg 0) ^ " x))"
  | "print" -> "(fun x -> print_string (" ^ gen_printer (arg 0) ^ " x))"
  | "exit" -> "Stdlib.exit"
  | "exn" -> "(fun s -> Stdlib.Failure s)"
  | "exn-message" -> "Printexc.to_string"
  | "throw" -> "(fun e -> raise e)"
  | "atom" -> "Clj_core.Atom.atom" | "deref" -> "Clj_core.Atom.deref"
  | "reset!" -> "Clj_core.Atom.reset_bang" | "swap!" -> "Clj_core.Atom.swap_bang"
  | "comp" -> "(fun f g x -> f (g x))"
  | "juxt" ->
    let fr = match repr (arg 0) with TFun (_, r) -> r | _ -> TAny
    and gr = match repr (arg 1) with TFun (_, r) -> r | _ -> TAny in
    let rec final_ret t = match repr t with TFun (_, r) -> final_ret r | t -> t in
    let el = match repr (final_ret ty) with TVec e -> e | _ -> TAny in
    "(fun f g x -> (Clj_core.Vec.of_list [" ^ conv el fr "(f x)" ^ "; " ^ conv el gr "(g x)" ^ "]))"
  | "mapcat" -> "(fun f c -> Clj_core.Seq.mapcat f (" ^ sq 1 ^ " c))"
  | "reverse" -> "(fun c -> Clj_core.Seq.reverse (" ^ sq 0 ^ " c))"
  | "sort" -> "(fun c -> Clj_core.Seq.sort (" ^ sq 0 ^ " c))"
  | "sort-by" -> "(fun kf c -> Clj_core.Seq.sort ~cmp:(fun x y -> Stdlib.compare (kf x) (kf y)) (" ^ sq 1 ^ " c))"
  | "take" -> "(fun n c -> Clj_core.Seq.take n (" ^ sq 1 ^ " c))"
  | "drop" -> "(fun n c -> Clj_core.Seq.drop n (" ^ sq 1 ^ " c))"
  | "take-while" -> "(fun p c -> Clj_core.Seq.take_while p (" ^ sq 1 ^ " c))"
  | "drop-while" -> "(fun p c -> Clj_core.Seq.drop_while p (" ^ sq 1 ^ " c))"
  | "interpose" -> "(fun sep c -> Clj_core.Seq.interpose sep (" ^ sq 1 ^ " c))"
  | "distinct" -> "(fun c -> Clj_core.Seq.distinct (" ^ sq 0 ^ " c))"
  | "iterate" -> "(fun f x -> Clj_core.Seq.iterate f x)"
  | "repeat" -> "(fun x -> Clj_core.Seq.repeat x)"
  | "cycle" -> "(fun c -> Clj_core.Seq.cycle (" ^ sq 0 ^ " c))"
  | "interleave" -> "(fun a b -> Clj_core.Seq.interleave (" ^ sq 0 ^ " a) (" ^ sq 1 ^ " b))"
  | "take-nth" -> "(fun n c -> Clj_core.Seq.take_nth n (" ^ sq 1 ^ " c))"
  | "dedupe" -> "(fun c -> Clj_core.Seq.dedupe (" ^ sq 0 ^ " c))"
  | "remove" -> "(fun f c -> Clj_core.Seq.remove f (" ^ sq 1 ^ " c))"
  | "doall" -> "(fun s -> Clj_core.Seq.of_list (Clj_core.Seq.to_list s))"
  | "dorun" -> "(fun c -> Clj_core.Seq.dorun (" ^ sq 0 ^ " c))"
  | "reductions" -> "(fun f i c -> Clj_core.Seq.reductions f i (" ^ sq 2 ^ " c))"
  | "every?" -> "(fun p c -> Clj_core.Seq.every_ p (" ^ sq 1 ^ " c))"
  | "some" -> "(fun p c -> Clj_core.Seq.exists p (" ^ sq 1 ^ " c))"
  | "min" -> "Stdlib.min" | "max" -> "Stdlib.max"
  | "map-indexed" -> "(fun f c -> Clj_core.Seq.mapi f (" ^ sq 1 ^ " c))"
  | "keep" | "filter-map" -> "(fun f c -> Clj_core.Seq.filter_map f (" ^ sq 1 ^ " c))"
  | "next" -> "(fun c -> Clj_core.Seq.next (" ^ sq 0 ^ " c))"
  | "second" -> "(fun c -> Clj_core.Seq.second (" ^ sq 0 ^ " c))"
  | "seq" -> "(fun c -> Clj_core.Seq.seq (" ^ sq 0 ^ " c))"
  | "nth" -> "(fun c i -> Clj_core.Seq.nth (" ^ sq 0 ^ " c) i)"
  | "nthrest" -> "(fun c n -> Clj_core.Seq.nthrest (" ^ sq 0 ^ " c) n)"
  | "group-by" -> "(fun f c -> Lg_rt.group_by f (" ^ ls 1 ^ " c))"
  | "frequencies" -> "(fun c -> Lg_rt.frequencies (" ^ ls 0 ^ " c))"
  | "zipmap" -> "(fun ks vs -> Clj_core.Map.of_list (List.combine (" ^ ls 0 ^ " ks) (" ^ ls 1 ^ " vs)))"
  | "split-at" -> "(fun n c -> (let (x, y) = Clj_core.Seq.split_at n (" ^ sq 1 ^ " c) in Clj_core.Vec.of_list [x; y]))"
  | "split-with" -> "(fun p c -> (let (x, y) = Clj_core.Seq.split_with p (" ^ sq 1 ^ " c) in Clj_core.Vec.of_list [x; y]))"
  | "slurp" -> "(fun p -> let ic = open_in_bin p in let s = really_input_string ic (in_channel_length ic) in close_in ic; s)"
  | "file-exists?" -> "Sys.file_exists"
  | "trim" -> "String.trim" | "triml" -> "Lg_rt.triml" | "trimr" -> "Lg_rt.trimr"
  | "upper-case" -> "String.uppercase_ascii" | "lower-case" -> "String.lowercase_ascii"
  | "blank?" -> "Lg_rt.str_blank"
  | "split" -> "(fun s sep -> Lg_rt.split_on sep s)"
  | "includes?" -> "Lg_rt.str_contains" | "replace" -> "(fun s m r -> Lg_rt.str_replace_lit m r s)"
  | "zero?" -> "(fun x -> x = 0)" | "pos?" -> "(fun x -> x > 0)" | "neg?" -> "(fun x -> x < 0)"
  | "even?" -> "(fun x -> x mod 2 = 0)" | "odd?" -> "(fun x -> x mod 2 <> 0)"
  | "int?" -> "(fun x -> match x with Lg_rt.DInt _ -> true | _ -> false)"
  | "float?" -> "(fun x -> match x with Lg_rt.DFloat _ -> true | _ -> false)"
  | "bool?" -> "(fun x -> match x with Lg_rt.DBool _ -> true | _ -> false)"
  | "char?" -> "(fun x -> match x with Lg_rt.DChar _ -> true | _ -> false)"
  | "string?" -> "(fun x -> match x with Lg_rt.DStr _ -> true | _ -> false)"
  | "keyword?" -> "(fun x -> match x with Lg_rt.DKw _ -> true | _ -> false)"
  | "symbol?" -> "(fun x -> match x with Lg_rt.DSym _ -> true | _ -> false)"
  | "list?" -> "(fun x -> match x with Lg_rt.DList _ -> true | _ -> false)"
  | "vec?" -> "(fun x -> match x with Lg_rt.DVec _ -> true | _ -> false)"
  | "set?" -> "(fun x -> match x with Lg_rt.DSet _ -> true | _ -> false)"
  | "map?" -> "(fun x -> match x with Lg_rt.DMap _ -> true | _ -> false)"
  | "seq?" -> "(fun x -> match x with Lg_rt.DList _ -> true | _ -> false)"
  | "coll?" -> "(fun x -> match x with Lg_rt.DVec _ | Lg_rt.DList _ | Lg_rt.DMap _ | Lg_rt.DSet _ -> true | _ -> false)"
  | "number?" -> "(fun x -> match x with Lg_rt.DInt _ | Lg_rt.DFloat _ -> true | _ -> false)"
  | "unit?" -> "(fun x -> match x with Lg_rt.DUnit -> true | _ -> false)"
  | "some?" -> "(fun x -> match x with Some _ -> true | _ -> false)"
  | "none?" -> "(fun x -> match x with None -> true | _ -> false)"
  | "fn?" -> "(fun _ -> false)"
  | "keys" -> "(fun m -> List.of_seq (Clj_core.Map.keys m))" | "vals" -> "(fun m -> List.of_seq (Clj_core.Map.vals m))"
  | "conj" ->
    (match repr (arg 0) with
     | TVec _ -> "(fun c x -> Clj_core.Vec.conj c x)"
     | TList _ -> "(fun c x -> x :: c)"
     | TSet _ -> "(fun c x -> Clj_core.Set.conj c x)"
     | TSeq _ -> "(fun c x -> Clj_core.Seq.cons x c)"
     | _ -> "(fun _ -> failwith \"conj: unsupported collection\")")
  | _ -> "(fun _ -> failwith \"builtin as value: " ^ name ^ "\")"

(* OCaml-side type spelling for `external` declarations (:ocaml). *)
let rec ocaml_ty t =
  match Typ.dimp t with
  | TInt -> "int" | TFloat -> "float" | TBool -> "bool" | TChar -> "char"
  | TString -> "string" | TUnit -> "unit" | TKeyword -> "Clj_core.Keyword.t"
  | TSymbol -> "Clj_core.Symbol.t"
  | TOption u -> paren_ty (ocaml_ty u) ^ " option"
  | TVec u -> paren_ty (ocaml_ty u) ^ " Clj_core.Vec.t"
  | TList u -> paren_ty (ocaml_ty u) ^ " list"
  | TSeq u -> paren_ty (ocaml_ty u) ^ " Clj_core.Seq.t"
  | TSet u -> paren_ty (ocaml_ty u) ^ " Clj_core.Set.t"
  | TMap (k, v) -> "(" ^ ocaml_ty k ^ ", " ^ ocaml_ty v ^ ") Clj_core.Map.t"
  | TAtom u -> paren_ty (ocaml_ty u) ^ " Clj_core.Atom.t"
  | TCon (n, []) -> tcon_name n
  | TCon (n, ts) -> "(" ^ String.concat ", " (List.map ocaml_ty ts) ^ ") " ^ tcon_name n
  | TVar v -> "'a" ^ string_of_int v.id
  | TFun (a, r) ->
    let dom = match a with [] -> [ "unit" ] | _ -> List.map ocaml_ty a in
    "(" ^ String.concat " -> " (dom @ [ ocaml_ty r ]) ^ ")"
  | t -> failwith ("emit: type has no OCaml FFI mapping: " ^ Typ.string_of_lg_ty t)

and tcon_name n =
  match Hashtbl.find_opt Infer.all_type_mods n with
  | Some m when m <> !cur_mod -> m ^ "." ^ munge n
  | _ ->
    (* ocaml.* ctor result types carry a real OCaml path
       ("Unix.sockaddr") — emit it verbatim *)
    if String.contains n '.' then n else munge n

and paren_ty s = if String.contains s ' ' then "(" ^ s ^ ")" else s

(* ctypes type spelling for :native bindings. *)
let ctypes_ty t =
  match Typ.dimp t with
  | TInt -> "Ctypes.int" | TFloat -> "Ctypes.double" | TBool -> "Ctypes.bool"
  | TChar -> "Ctypes.char" | TString -> "Ctypes.string"
  | TUnit -> "Ctypes.void"
  | TOption TString -> "Ctypes.string_opt"
  | TOption (TCon _) -> "Ctypes.(ptr_opt void)"
  | TCon (_, []) -> "Ctypes.(ptr void)"
  | t -> failwith ("emit: type has no ctypes mapping: " ^ Typ.string_of_lg_ty t)

let emit_ffi b l name args ret sel lib =
  match sel with
  | FJs sp ->
    if not !melange then
      raise (Typ.Type_error (l, "ffi :js requires --backend=melange"));
    let dom = match args with [] -> "unit" | _ -> String.concat " -> " (List.map ocaml_ty args) in
    let attrs =
      (match sp.jkind with
       | JCall -> [] | JNew -> [ "mel.new" ] | JSend -> [ "mel.send" ]
       | JGet -> [ "mel.get" ] | JSet -> [ "mel.set" ])
      @ (match sp.jmodule with None -> [] | Some m -> [ Printf.sprintf "mel.module %S" m ])
      @ (match sp.jscope with
         | [] -> []
         | [ s ] -> [ Printf.sprintf "mel.scope %S" s ]
         | ss -> [ "mel.scope (" ^ String.concat ", " (List.map (Printf.sprintf "%S") ss) ^ ")" ])
      @ (match sp.jret with
         | JDirect -> []
         | JUndefined -> [ "mel.return undefined_to_opt" ]
         | JNull -> [ "mel.return null_to_opt" ]
         | JNullable -> [ "mel.return nullable" ])
    in
    let attr_s = String.concat "" (List.map (fun a -> " [@@" ^ a ^ "]") attrs) in
    buf_add b (Printf.sprintf "external %s : %s -> %s = %S%s
" (munge name) dom (ocaml_ty ret) sp.jsym attr_s)
  | (FOcaml _ | FNative _) when !melange ->
    raise (Typ.Type_error (l, "ffi :ocaml/:native are not supported on melange — use :js"))
  | FOcaml stub ->
    let dom = match args with [] -> "unit" | _ -> String.concat " -> " (List.map ocaml_ty args) in
    buf_add b (Printf.sprintf "external %s : %s -> %s = %S
" (munge name) dom (ocaml_ty ret) stub)
  | FNative sym ->
    let sig_s = String.concat " @-> " (List.map ctypes_ty args @ [ "Ctypes.returning " ^ ctypes_ty ret ]) in
    let call = Printf.sprintf "Foreign.foreign %S (Ctypes.(%s))" sym sig_s in
    let rhs =
      match lib with
      | None -> call
      | Some p -> Printf.sprintf "let lib = Dl.dlopen ~filename:%S ~flags:Dl.[RTLD_NOW] in Foreign.foreign ~from:lib %S (Ctypes.(%s))" p sym sig_s
    in
    buf_add b (Printf.sprintf "let %s = %s
" (munge name) rhs)

(* a bare compilation unit rejects weak type variables where a module
   struct tolerates them (e.g. `(atom (Map.of_list []))`); ascribing the
   closed scheme pins the type *)
let closed_asc d =
  if d.tis_fn then None
  else
    (try
       let s = ocaml_ty d.tsch.sty in
       if String.contains s '\'' then None else Some s
     with _ -> None)

let emit_topdef b (d : topdef) =
  line_dir b d.tloc;
  buf_add b "let ";
  (match d.tmode with Local -> buf_add b "(* @local *) " | Owned -> buf_add b "(* @owned *) " | Shared -> ());
  let rec_flag = match d.texpr.desc with EFun _ -> "rec " | _ -> "" in
  buf_add b rec_flag;
  buf_add b (munge d.tname);
  buf_add b " = ";
  (match closed_asc d with
   | Some t -> buf_add b "("; emit_expr b d.texpr; buf_add b (" : " ^ t ^ ")")
   | None -> emit_expr b d.texpr);
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
  | [ `Def d ] -> emit_topdef b d
  | [ `Extern (_l, n) ] -> line_dir b _l; buf_add b ("type " ^ munge n ^ "
")
  | [ `Ffi (_l, n, a, r, sel, lib) ] -> line_dir b _l; emit_ffi b _l n a r sel lib
  | [ `Eff e ] ->
    (* interleaved effect — runs in source position, between defs *)
    line_dir b e.loc;
    buf_add b "let () = (ignore (";
    emit_expr b e;
    buf_add b "))
"
  | [ `Variant (_l, n, ps, cs) ] ->
    line_dir b _l;
    let pfx =
      match ps with
      | [] -> ""
      | [ v ] -> ocaml_ty v ^ " "
      | vs -> "(" ^ String.concat ", " (List.map ocaml_ty vs) ^ ") "
    in
    buf_add b ("type " ^ pfx ^ munge n ^ " = ");
    buf_add b
      (String.concat " | "
         (List.map
            (fun (c, flds) ->
              let cn = String.capitalize_ascii (munge c) in
              (match flds with
               | [] -> cn
               | _ -> cn ^ " of " ^ String.concat " * " (List.map (fun (_, t) -> ocaml_ty t) flds)))
            cs));
    buf_add b "
";
    List.iter
      (fun (c, flds) ->
        Hashtbl.replace cur_v
          (!cur_mod ^ "/" ^ munge c)
          (!cur_mod ^ "." ^ String.capitalize_ascii (munge c), List.length flds))
      cs
  | ds ->
    let all_fn = List.for_all (function `Def d -> d.tis_fn | _ -> false) ds in
    buf_add b (if all_fn then "let rec " else "let ");
    List.iteri
      (fun i d ->
        match d with
        | `Def d | `Nonrec d ->
          if i > 0 then buf_add b " and ";
          buf_add b (munge d.tname);
          buf_add b " = ";
          (match closed_asc d with
           | Some t -> buf_add b "("; emit_expr b d.texpr; buf_add b (" : " ^ t ^ ")")
           | None -> emit_expr b d.texpr)
        | _ -> assert false)
      ds;
    buf_add b "\n"

let rec refs_in acc e =
  let acc =
    match e.desc with
    | EGlobal (mp, _n, lgn) -> if mp = !cur_mod then lgn :: acc else acc
    | _ -> acc
  in
  match e.desc with
  | EInt _ | EFloat _ | EBool _ | EChar _ | EStr _ | EKeyword _ | ESymbol _
  | ENil | ELocal _ | EGlobal _ | EBuiltin _ -> acc
  | EFun fn -> refs_in acc fn.body
  | ECall (c, xs) -> List.fold_left refs_in (refs_in acc c) xs
  | EOCamlCall (c, oas) ->
    List.fold_left (fun a oa -> refs_in a (oarg_expr oa)) (refs_in acc c) oas
  | EIf (a, x, y) -> refs_in (refs_in (refs_in acc a) x) y
  | EDo xs -> List.fold_left refs_in acc xs
  | ELet (bs, x) -> List.fold_left (fun a (_, ex) -> refs_in a ex) (refs_in acc x) bs
  | ETuple xs | EVecLit xs | EListLit xs | ESetLit xs -> List.fold_left refs_in acc xs
  | EMapLit ps -> List.fold_left (fun a (k, v) -> refs_in (refs_in a k) v) acc ps
  | EMatchOpt (a, _, x, y) | EDynVec (a, _, x, y) | EDynMap (a, _, x, y) ->
    refs_in (refs_in (refs_in acc a) x) y
  | EUnbox (a, _) | EUnboxOpt (a, _) | EBox a -> refs_in acc a
  | EOpt (Some a) -> refs_in acc a
  | EOpt None -> acc
  | EVariant (a, _, _, x, y) -> refs_in (refs_in (refs_in acc a) x) y
  | ETry (b', c, f) ->
    let acc = refs_in acc b' in
    let acc = (match c with Some (_, h) -> refs_in acc h | None -> acc) in
    (match f with Some fe -> refs_in acc fe | None -> acc)

(* Split a run of fn defs into binding groups: only defs that reach each
   other transitively (a real recursion cycle, self-loops included) need one
   `let rec .. and ..`; everything else is emitted as plain `let`, which is
   what keeps the emitted OCaml polymorphic across the module *)
let fn_groups (ds : topdef list) : (bool * topdef list) list =
  let names = List.map (fun d -> d.tname) ds in
  let tbl = Hashtbl.create 16 in
  List.iter (fun d -> Hashtbl.replace tbl d.tname (refs_in [] d.texpr)) ds;
  (* transitive refs of n, restricted to names in this run. Plain DFS —
     a shared visited set per call; no memo (a memoized result would be
     poisoned by whichever ancestors happened to be on the DFS path). *)
  let reach n =
    let seen = Hashtbl.create 16 in
    let rec go acc n =
      match Hashtbl.find_opt tbl n with
      | None -> acc
      | Some direct ->
        List.fold_left
          (fun acc m ->
            if List.mem m names && not (Hashtbl.mem seen m) then (
              Hashtbl.replace seen m ();
              go (m :: acc) m)
            else acc)
          acc direct
    in
    go [] n
  in
  let assigned = Hashtbl.create 16 in
  let sccs =
    List.fold_left
      (fun acc d ->
        if Hashtbl.mem assigned d.tname then acc
        else
          let dr = reach d.tname in
          let scc =
            List.filter
              (fun o ->
                o.tname = d.tname
                || (List.mem o.tname dr && List.mem d.tname (reach o.tname)))
              ds
          in
          List.iter (fun o -> Hashtbl.replace assigned o.tname ()) scc;
          let self_loop = List.mem d.tname dr in
          acc @ [ (List.length scc > 1 || self_loop, scc) ])
      [] ds
  in
  (* stable topological order over the run: a group that references a name
     owned by a later group is emitted after it — this covers one-way
     forward refs (a `declare` without mutual recursion) where a cycle is
     absent but source order would still emit the callee too late *)
  let owner = Hashtbl.create 16 in
  List.iteri (fun i (_r, scc) -> List.iter (fun d -> Hashtbl.replace owner d.tname i) scc) sccs;
  let emitted = Hashtbl.create 16 in
  let rec take acc rest =
    match rest with
    | [] -> acc
    | _ ->
      let ready, pending =
        List.partition
          (fun (_r, scc) ->
            List.for_all
              (fun n -> not (Hashtbl.mem owner n) || Hashtbl.mem emitted n)
              (List.concat_map (fun d -> Hashtbl.find tbl d.tname) scc))
          rest
      in
      (match ready with
       | [] -> acc @ rest (* cycle across groups; shouldn't happen *)
       | r ->
         List.iter
           (fun (_x, scc) -> List.iter (fun d -> Hashtbl.replace emitted d.tname ()) scc)
           r;
         take (acc @ r) pending)
  in
  take [] sccs

let emit_module_body b (m : modl) =
  cur_mod := m.ocaml_name;
  last_dir_line := -1;
  let rec groups acc = function
    | [] -> List.rev acc
    | TDef d :: rest when d.tis_fn ->
      (* consecutive fn defs form one `let rec .. and ..` group — this is
         what makes `(declare g)` mutual recursion emit correctly *)
      let rec take acc2 = function
        | TDef d2 :: tl when d2.tis_fn -> take (d2 :: acc2) tl
        | tl -> (List.rev acc2, tl)
      in
      let same, rest' = take [ d ] rest in
      (* only true recursion cycles (incl. self-loops) share a `let rec`
         group; non-cyclic fns emit as plain `let` to keep them polymorphic *)
      let gs =
        List.map
          (fun (rec_, scc) ->
            if rec_ then List.map (fun x -> `Def x) scc
            else List.map (fun x -> `Nonrec x) scc)
          (fn_groups same)
      in
      groups (List.rev_append gs acc) rest'
    | TDef d :: rest -> groups ([ `Nonrec d ] :: acc) rest
    | TVariant (_l, n, ps, cs, _) :: rest -> groups ([ `Variant (_l, n, ps, cs) ] :: acc) rest
    | TExtern (_l, n) :: rest -> groups ([ `Extern (_l, n) ] :: acc) rest
    | TFfi (_l, n, a, r, sel, lib) :: rest -> groups ([ `Ffi (_l, n, a, r, sel, lib) ] :: acc) rest
    | TEffect e :: rest -> groups ([ `Eff e ] :: acc) rest
  in
  Hashtbl.reset topdef_names;
  List.iter
    (function TDef d -> Hashtbl.replace topdef_names d.tname () | _ -> ())
    m.tops;
  List.iter (emit_def_group b) (groups [] m.tops);
  List.iter (fun e -> line_dir b e.loc; buf_add b "let () = (ignore ("; emit_expr b e; buf_add b "))\n") m.effects

let emit_module b (m : modl) =
  buf_add b ("module " ^ m.ocaml_name ^ " = struct\n");
  emit_module_body b m;
  buf_add b "end\n\n"

(* Melange-only node bridge: Node APIs are touched lazily (require() is
   only evaluated when an io builtin is actually called), so browser
   bundles load fine and only fail if io is invoked without Node. *)
let lg_node_src = {|
module Lg_node = struct
  let slurp : string -> string = [%mel.raw
    "function(p) { if (typeof require !== 'function') throw new Error('slurp requires Node.js'); return require('fs').readFileSync(p, 'utf8') }"]

  let spit : string -> string -> unit = [%mel.raw
    "function(p, s) { if (typeof require !== 'function') throw new Error('spit requires Node.js'); require('fs').writeFileSync(p, s, 'utf8') }"]

  let file_exists : string -> bool = [%mel.raw
    "function(p) { if (typeof require !== 'function') return false; try { return require('fs').existsSync(p) } catch (e) { return false } }"]

  let argv : unit -> string array = [%mel.raw
    "function() { if (typeof process === 'undefined' || !process.argv) return []; return process.argv.slice(2) }"]

  let env_raw : string -> string Js.Undefined.t = [%mel.raw
    "function(k) { if (typeof process === 'undefined' || !process.env) return undefined; return process.env[k] }"]

  let env_opt k = Js.Undefined.toOption (env_raw k)

  let sh : string -> string = [%mel.raw
    "function(c) { if (typeof require !== 'function') throw new Error('sh requires Node.js'); return require('child_process').execSync(c, {encoding: 'utf8'}) }"]

  let read_stdin_all : unit -> string Js.Nullable.t = [%mel.raw
    "function() { if (typeof require !== 'function') return null; try { return require('fs').readFileSync(0, 'utf8') } catch (e) { return null } }"]

  let stdin_lines = ref None
  let read_line () =
    let lines =
      match !stdin_lines with
      | Some ls -> ls
      | None ->
        let l =
          (match Js.Nullable.toOption (read_stdin_all ()) with
           | Some s -> String.split_on_char '\n' s
           | None -> [])
        in
        stdin_lines := Some l; l
    in
    (match lines with
     | h :: t -> stdin_lines := Some t; Some h
     | [] -> stdin_lines := Some []; None)

  let now_ms () = int_of_float (Js.Date.now ())

  (* regex-lite over JS RegExp — available in every JS environment *)
  let re_find pat s =
    match Js.Re.exec (Js.Re.fromString pat) ~str:s with
    | Some r ->
      let cs = Js.Re.captures r in
      if Array.length cs > 0 then Js.Nullable.toOption cs.(0) else None
    | None -> None

  let re_matches pat s =
    if Js.Re.test (Js.Re.fromString ("^(?:" ^ pat ^ ")$")) ~str:s then Some s else None

  let re_seq pat s =
    let re = Js.Re.fromStringWithFlags pat ~flags:"g" in
    let rec go acc =
      match Js.Re.exec re ~str:s with
      | Some r ->
        let cs = Js.Re.captures r in
        (match (if Array.length cs > 0 then Js.Nullable.toOption cs.(0) else None) with
         | Some m ->
           if m = "" then Js.Re.setLastIndex re (Js.Re.lastIndex re + 1);
           go (m :: acc)
         | None -> go acc)
      | None -> List.rev acc
    in
    go []

  let re_split pat s =
    List.filter_map Fun.id (Array.to_list (Js.String.splitByRe ~regexp:(Js.Re.fromString pat) s))

  let re_replace pat s rep =
    Js.String.replaceByRe ~regexp:(Js.Re.fromStringWithFlags pat ~flags:"g") ~replacement:rep s
end
|}

let emit_program (mods : modl list) : string =
  (match List.find_opt (fun m -> m.iface_only) mods with
   | Some m ->
     failwith ("module " ^ m.mname ^ " has only an .lgi interface — provide a .lg to emit/build")
   | None -> ());
  let b = Buffer.create 8192 in
  List.iter
    (fun m ->
      List.iter
        (function
          | TDef d ->
            Hashtbl.replace sig_tbl (m.ocaml_name ^ "/" ^ munge d.tname) d.tsch.sty
          | _ -> ())
        m.tops)
    mods;
  Modes.collect_value_refs_program mods;
  buf_add b "(* generated by lg — do not edit *)\n";
  buf_add b ("module Lg_rt = struct\n" ^ Embedded_runtime.lg_rt_src ^ "\nend\n");
  if !melange then buf_add b lg_node_src;
  List.iter (emit_module b) mods;
  Buffer.contents b

(* per-module compilation units for incremental builds: each lg module is
   emitted as a bare OCaml unit file — cross-module references like
   `Test.foo` resolve to the Test.cmi of the unit compiled before it.
   Returns (unit file basename, source, dep unit basenames) in dependency
   order; the first entry is always the Lg_rt runtime unit. *)
let emit_units (mods : modl list) : (string * string * string list) list =
  (match List.find_opt (fun m -> m.iface_only) mods with
   | Some m ->
     failwith ("module " ^ m.mname ^ " has only an .lgi interface — provide a .lg to emit/build")
   | None -> ());
  List.iter
    (fun m ->
      List.iter
        (function
          | TDef d ->
            Hashtbl.replace sig_tbl (m.ocaml_name ^ "/" ^ munge d.tname) d.tsch.sty
          | _ -> ())
        m.tops)
    mods;
  Modes.collect_value_refs_program mods;
  let unit_of = Hashtbl.create 16 in
  List.iter (fun m -> Hashtbl.replace unit_of m.mname (String.lowercase_ascii m.ocaml_name)) mods;
  ("lg_rt", Embedded_runtime.lg_rt_src, [])
  :: List.map
    (fun m ->
      let b = Buffer.create 8192 in
      emit_module_body b m;
      let deps =
        (* every unit needs lg_rt's cmi, and a runtime change must
           invalidate every stamp — keep it an explicit dep *)
        "lg_rt"
        :: List.filter_map
             (fun (_, rn) -> Hashtbl.find_opt unit_of rn)
             m.requires
      in
      (String.lowercase_ascii m.ocaml_name, Buffer.contents b, deps))
    mods
