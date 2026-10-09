(* Types: Hindley-Milner with mutable unification variables and let-generalization. *)

type ty =
  | TInt
  | TFloat
  | TBool
  | TChar
  | TString
  | TKeyword
  | TSymbol
  | TUnit
  | TList of ty
  | TVec of ty
  | TMap of ty * ty
  | TSet of ty
  | TAtom of ty
  | TOption of ty
  | TTuple of ty list
  | TFun of ty list * ty
  | TVar of tvar
  | TCon of string * ty list  (* user-defined named type, e.g. records *)
  | TAny                     (* unchecked dynamic boundary; only via explicit ^any *)

and tvar = { id : int; mutable link : ty option; mutable level : int; mutable rigid : bool }

exception Type_error of Syntax.loc * string

let type_error loc msg = raise (Type_error (loc, msg))

let next_id = ref 0
let fresh_var ?(level = 0) () = incr next_id; TVar { id = !next_id; link = None; level; rigid = false }
let fresh_rigid ?(level = 0) () = incr next_id; TVar { id = !next_id; link = None; level; rigid = true }

let rec repr t =
  match t with
  | TVar ({ link = Some t'; _ } as v) ->
    let r = repr t' in
    if r != t' then v.link <- Some r;
    r
  | _ -> t

let rec occurs v t =
  match repr t with
  | TVar v' -> v.id = v'.id
  | TList t | TVec t | TSet t | TAtom t | TOption t -> occurs v t
  | TMap (k, x) -> occurs v k || occurs v x
  | TTuple ts | TCon (_, ts) -> List.exists (occurs v) ts
  | TFun (ts, r) -> List.exists (occurs v) ts || occurs v r
  | _ -> false

let rec unify loc a b =
  let a = repr a and b = repr b in
  if a == b then ()
  else
    match (a, b) with
    | TVar v, t | t, TVar v ->
      if v.rigid then
        type_error loc "rigid type variable cannot be unified with a concrete type";
      if occurs v t then type_error loc "occurs check failed (infinite type)";
      v.link <- Some t
    | TAny, _ | _, TAny -> ()
    | TInt, TInt | TFloat, TFloat | TBool, TBool | TChar, TChar | TString, TString
    | TKeyword, TKeyword | TSymbol, TSymbol | TUnit, TUnit -> ()
    | TList a, TList b | TVec a, TVec b | TSet a, TSet b | TAtom a, TAtom b | TOption a, TOption b -> unify loc a b
    | TMap (k1, v1), TMap (k2, v2) -> unify loc k1 k2; unify loc v1 v2
    | TTuple xs, TTuple ys when List.length xs = List.length ys -> List.iter2 (unify loc) xs ys
    | TFun (xs, r1), TFun (ys, r2) when List.length xs = List.length ys ->
      List.iter2 (unify loc) xs ys; unify loc r1 r2
    | TCon (n1, xs), TCon (n2, ys) when n1 = n2 && List.length xs = List.length ys ->
      List.iter2 (unify loc) xs ys
    | _ ->
      type_error loc
        (Printf.sprintf "type mismatch: %s vs %s" (string_of_ty a) (string_of_ty b))

and string_of_ty t =
  match repr t with
  | TInt -> "int" | TFloat -> "float" | TBool -> "bool" | TChar -> "char"
  | TString -> "string" | TKeyword -> "keyword" | TSymbol -> "symbol" | TUnit -> "unit"
  | TAny -> "any"
  | TList t -> "(" ^ string_of_ty t ^ " list)"
  | TVec t -> "(vec " ^ string_of_ty t ^ ")"
  | TMap (k, v) -> "(map " ^ string_of_ty k ^ " " ^ string_of_ty v ^ ")"
  | TSet t -> "(set " ^ string_of_ty t ^ ")"
  | TAtom t -> "(atom " ^ string_of_ty t ^ ")"
  | TOption t -> "(option " ^ string_of_ty t ^ ")"
  | TTuple ts -> "(tuple " ^ String.concat " " (List.map string_of_ty ts) ^ ")"
  | TFun (ts, r) ->
    "(fn [" ^ String.concat " " (List.map string_of_ty ts) ^ "] -> " ^ string_of_ty r ^ ")"
  | TCon (n, ts) ->
    if ts = [] then n else "(" ^ n ^ " " ^ String.concat " " (List.map string_of_ty ts) ^ ")"
  | TVar v -> "'a" ^ string_of_int v.id

(* ---- schemes ---- *)

type scheme = { svars : int list; sty : ty }

let mono t = { svars = []; sty = t }

let free_tvars t acc =
  let rec go acc t =
    match repr t with
    | TVar v -> if List.mem v.id acc then acc else v.id :: acc
    | TList t | TVec t | TSet t | TAtom t | TOption t -> go acc t
    | TMap (k, v) -> go (go acc k) v
    | TTuple ts | TCon (_, ts) -> List.fold_left go acc ts
    | TFun (ts, r) -> go (List.fold_left go acc ts) r
    | _ -> acc
  in
  go acc t

(* Generalize: quantify vars not free in env schemes and above no level bound.
   lg2 v0: generalize all vars not free in env (no ref-cell polymorphism issue
   because atoms are explicit constructors). *)
let generalize env t =
  let env_free =
    List.fold_left (fun acc (_, s) -> free_tvars s.sty acc) [] env
  in
  let svars = List.filter (fun id -> not (List.mem id env_free)) (free_tvars t []) in
  { svars; sty = t }

let instantiate sch =
  let subst = List.map (fun id -> (id, fresh_var ())) sch.svars in
  let rec go t =
    match repr t with
    | TVar v -> (match List.assoc_opt v.id subst with Some t -> t | None -> t)
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
  go sch.sty
