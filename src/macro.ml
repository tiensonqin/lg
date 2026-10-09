(* Hygienic defmacro: a compile-time evaluator over reader forms.

   - `defmacro` registers a macro function `mfn` under "<ns>/<name>".
   - Macro arguments are the raw (unevaluated) argument forms.
   - `syntax-quote` (backquote) walks a template; `~`/`~@` splice evaluated
     values in; every symbol inside the template is renamed with a fresh
     mark `__h<N>` and recorded in [marks] so the analyzer can resolve the
     original name for globals/builtins/special forms while binders stay
     capture-free (hygiene). *)

open Syntax

type mval =
  | MForm of form
  | MFn of mfn
  | MBuiltin of string

and mfn = {
  mname : string;
  mparams : string list;
  mrest : string option;
  mbody : form list;
  menv : (string, mval) Hashtbl.t;
}

exception Macro_error of loc * string

let macros : (string, mfn) Hashtbl.t = Hashtbl.create 32
(* unqualified lookup for same-module calls inside macro bodies *)
let macro_by_name : (string, mfn) Hashtbl.t = Hashtbl.create 32

let is_macro ns name = Hashtbl.mem macros (ns ^ "/" ^ name)
let find_macro ns name = Hashtbl.find_opt macros (ns ^ "/" ^ name)

let register_macro ns name fn =
  Hashtbl.replace macros (ns ^ "/" ^ name) fn;
  Hashtbl.replace macro_by_name name fn

(* resolve a callee symbol to a macro: "ns/name" uses the qualified table;
   a bare name falls back to the last macro registered under that name *)
let macro_of_sym s =
  match String.index_opt s '/' with
  | Some i ->
    let ns = String.sub s 0 i and name = String.sub s (i + 1) (String.length s - i - 1) in
    (match find_macro ns name with Some fn -> Some fn | None -> Hashtbl.find_opt macro_by_name s)
  | None -> Hashtbl.find_opt macro_by_name s

(* hygiene marks: renamed template symbol -> original name *)
let marks : (string, string) Hashtbl.t = Hashtbl.create 256
let mark_ctr = ref 0
let gensym_ctr = ref 0

let unmark s = match Hashtbl.find_opt marks s with Some o -> o | None -> s

let form_error l fmt = Printf.ksprintf (fun s -> raise (Macro_error (l, s))) fmt

let gensym prefix =
  incr gensym_ctr;
  Atom (no_loc, Symbol (prefix ^ "__g" ^ string_of_int !gensym_ctr))

let sym s = Atom (no_loc, Symbol s)

(* ---- structural equality on forms (for `=` in macro bodies) ---- *)
let rec form_eq a b =
  match a, b with
  | Atom (_, x), Atom (_, y) -> x = y
  | List (_, xs), List (_, ys) ->
    List.length xs = List.length ys && List.for_all2 form_eq xs ys
  | Vector (_, xs), Vector (_, ys) ->
    Array.length xs = Array.length ys
    && List.for_all2 form_eq (Array.to_list xs) (Array.to_list ys)
  | Map (_, xs), Map (_, ys) ->
    List.length xs = List.length ys
    && List.for_all2 (fun (k1, v1) (k2, v2) -> form_eq k1 k2 && form_eq v1 v2) xs ys
  | Set (_, xs), Set (_, ys) ->
    List.length xs = List.length ys && List.for_all2 form_eq xs ys
  | Quote (_, x), Quote (_, y) -> form_eq x y
  | Meta (_, m1, x), Meta (_, m2, y) -> form_eq m1 m2 && form_eq x y
  | _ -> false

let truthy = function
  | MForm (Atom (_, Nil)) | MForm (Atom (_, Bool false)) -> false
  | MForm (List (_, [])) -> false
  | MForm (Vector (_, [||])) -> false
  | _ -> true

(* ---- evaluator ---- *)

let rec eval_builtin_apply l name args =
  let loc = l in
  let arg_forms =
    List.map
      (function
        | MForm f -> f
        | _ -> form_error loc "macro builtin %s: expected form argument" name)
      args
  in
  let list_form xs = List (loc, xs) in
  match name with
  | "list" -> MForm (list_form arg_forms)
  | "cons" ->
    (match arg_forms with
     | [ x; List (_, xs) ] -> MForm (list_form (x :: xs))
     | [ x; Vector (_, xs) ] -> MForm (list_form (x :: Array.to_list xs))
     | [ x; Atom (_, Nil) ] -> MForm (list_form [ x ])
     | _ -> form_error loc "cons: second argument must be a list or vector")
  | "first" ->
    (match arg_forms with
     | [ List (_, x :: _) ] -> MForm x
     | [ Vector (_, xs) ] when Array.length xs > 0 -> MForm xs.(0)
     | [ Atom (_, Nil) ] | [ List (_, []) ] | [ Vector (_, [||]) ] -> MForm (Atom (loc, Nil))
     | _ -> form_error loc "first: not a sequence")
  | "rest" ->
    (match arg_forms with
     | [ List (_, _ :: xs) ] -> MForm (list_form xs)
     | [ Vector (_, xs) ] when Array.length xs > 0 -> MForm (list_form (Array.to_list (Array.sub xs 1 (Array.length xs - 1))))
     | [ Atom (_, Nil) ] | [ List (_, []) ] | [ Vector (_, [||]) ] -> MForm (list_form [])
     | _ -> form_error loc "rest: not a sequence")
  | "next" ->
    (match arg_forms with
     | [ List (_, _ :: xs) ] -> MForm (list_form xs)
     | [ Vector (_, xs) ] when Array.length xs > 0 -> MForm (list_form (Array.to_list (Array.sub xs 1 (Array.length xs - 1))))
     | [ Atom (_, Nil) ] | [ List (_, []) ] | [ Vector (_, [||]) ] -> MForm (Atom (loc, Nil))
     | _ -> form_error loc "next: not a sequence")
  | "last" ->
    (match arg_forms with
     | [ List (_, xs) ] -> MForm (match List.rev xs with x :: _ -> x | [] -> Atom (loc, Nil))
     | [ Vector (_, xs) ] -> MForm (if Array.length xs = 0 then Atom (loc, Nil) else xs.(Array.length xs - 1))
     | _ -> form_error loc "last: not a sequence")
  | "concat" ->
    let flatten = function
      | List (_, xs) -> xs
      | Vector (_, xs) -> Array.to_list xs
      | Atom (_, Nil) -> []
      | f -> [ f ]
    in
    MForm (list_form (List.concat_map flatten arg_forms))
  | "conj" ->
    (match arg_forms with
     | List (_, xs) :: rest -> MForm (list_form (rest @ xs))
     | Vector (_, xs) :: rest -> MForm (Vector (loc, Array.of_list (Array.to_list xs @ rest)))
     | _ -> form_error loc "conj: first argument must be a collection")
  | "seq" ->
    (match arg_forms with
     | [ List (_, xs) ] -> MForm (list_form xs)
     | [ Vector (_, xs) ] -> MForm (list_form (Array.to_list xs))
     | [ Atom (_, Nil) ] -> MForm (Atom (loc, Nil))
     | _ -> form_error loc "seq: not a sequence")
  | "count" ->
    (match arg_forms with
     | [ List (_, xs) ] -> MForm (Atom (loc, Int (List.length xs)))
     | [ Vector (_, xs) ] -> MForm (Atom (loc, Int (Array.length xs)))
     | [ Atom (_, Str s) ] -> MForm (Atom (loc, Int (String.length s)))
     | _ -> MForm (Atom (loc, Int 0)))
  | "empty?" ->
    (match arg_forms with
     | [ List (_, []) ] | [ Vector (_, [||]) ] | [ Atom (_, Nil) ] -> MForm (Atom (loc, Bool true))
     | _ -> MForm (Atom (loc, Bool false)))
  | "nth" ->
    (match arg_forms with
     | [ List (_, xs); Atom (_, Int i) ] ->
       if i >= 0 && i < List.length xs then MForm (List.nth xs i)
       else form_error loc "nth: index out of bounds"
     | [ Vector (_, xs); Atom (_, Int i) ] ->
       if i >= 0 && i < Array.length xs then MForm xs.(i)
       else form_error loc "nth: index out of bounds"
     | _ -> form_error loc "nth: bad arguments")
  | "take" ->
    (match arg_forms with
     | [ Atom (_, Int n); List (_, xs) ] -> MForm (list_form (List.filteri (fun i _ -> i < n) xs))
     | [ Atom (_, Int n); Vector (_, xs) ] -> MForm (list_form (List.filteri (fun i _ -> i < n) (Array.to_list xs)))
     | _ -> form_error loc "take: bad arguments")
  | "drop" ->
    (match arg_forms with
     | [ Atom (_, Int n); List (_, xs) ] -> MForm (list_form (List.filteri (fun i _ -> i >= n) xs))
     | [ Atom (_, Int n); Vector (_, xs) ] -> MForm (list_form (List.filteri (fun i _ -> i >= n) (Array.to_list xs)))
     | _ -> form_error loc "drop: bad arguments")
  | "vector" -> MForm (Vector (loc, Array.of_list arg_forms))
  | "quote" -> (match arg_forms with [ f ] -> MForm f | _ -> form_error loc "quote: 1 arg")
  | "symbol" ->
    (match arg_forms with
     | [ Atom (_, Symbol s) ] | [ Atom (_, Str s) ] -> MForm (sym s)
     | _ -> form_error loc "symbol: expected symbol or string")
  | "keyword" ->
    (match arg_forms with
     | [ Atom (_, Keyword k) ] | [ Atom (_, Str k) ] -> MForm (Atom (loc, Keyword k))
     | _ -> form_error loc "keyword: expected keyword or string")
  | "name" ->
    (match arg_forms with
     | [ Atom (_, Symbol s) ] | [ Atom (_, Keyword s) ] | [ Atom (_, Str s) ] -> MForm (Atom (loc, Str s))
     | _ -> form_error loc "name: expected symbol or keyword")
  | "str" ->
    let bare = function
      | Atom (_, Str s) -> s | Atom (_, Symbol s) -> s | Atom (_, Keyword k) -> ":" ^ k
      | Atom (_, Int i) -> string_of_int i
      | Atom (_, Bool b) -> string_of_bool b
      | Atom (_, Nil) -> "nil"
      | f -> form_to_string f
    in
    MForm (Atom (loc, Str (String.concat "" (List.map bare arg_forms))))
  | "=" ->
    (match arg_forms with
     | [ a; b ] -> MForm (Atom (loc, Bool (form_eq a b)))
     | _ -> MForm (Atom (loc, Bool false)))
  | "gensym" ->
    (match arg_forms with
     | [ Atom (_, Str p) ] | [ Atom (_, Symbol p) ] -> MForm (gensym p)
     | [] -> MForm (gensym "g")
     | _ -> form_error loc "gensym: expected string or symbol prefix")
  | "println" ->
    List.iter (fun f -> Printf.printf "[macro] %s\n" (form_to_string f)) arg_forms;
    MForm (Atom (loc, Nil))
  | _ -> form_error loc "unknown macro builtin %s" name

and form_to_string (f : form) : string =
  match f with
  | Atom (_, a) ->
    (match a with
     | Int i -> string_of_int i
     | Float x -> string_of_float x
     | Bool b -> string_of_bool b
     | Char c -> String.make 1 c
     | Str s -> Printf.sprintf "%S" s
     | Keyword k -> ":" ^ k
     | Symbol s -> s
     | Nil -> "nil")
  | List (_, xs) -> "(" ^ String.concat " " (List.map form_to_string xs) ^ ")"
  | Vector (_, xs) -> "[" ^ String.concat " " (List.map form_to_string (Array.to_list xs)) ^ "]"
  | Map (_, xs) ->
    "{" ^ String.concat " " (List.map (fun (k, v) -> form_to_string k ^ " " ^ form_to_string v) xs) ^ "}"
  | Set (_, xs) -> "#{" ^ String.concat " " (List.map form_to_string xs) ^ "}"
  | Quote (_, x) -> "'" ^ form_to_string x
  | Meta (_, m, x) -> "^" ^ form_to_string m ^ " " ^ form_to_string x

let macro_builtins =
  [ "list"; "cons"; "first"; "rest"; "next"; "last"; "concat"; "conj"; "seq";
    "count"; "empty?"; "nth"; "take"; "drop"; "vector"; "quote"; "symbol";
    "keyword"; "name"; "str"; "="; "gensym"; "println"; "map"; "filter";
    "apply"; "meta"; "with-meta"; "mapv"; "reduce" ]

let is_eval_builtin name = List.mem name macro_builtins

(* ---- syntax-quote expansion ---- *)

let rec squote (env : (string, mval) Hashtbl.t) (mark : int) (f : form) : form =
  let tag = "__h" ^ string_of_int mark in
  match f with
  | List (_, [ Atom (_, Symbol "unquote"); arg ]) ->
    (match eval env arg with
     | MForm f' -> f'
     | _ -> form_error (atom_loc f) "unquote of a non-form value")
  | List (l, items) ->
    let rec splice acc = function
      | [] -> List.rev acc
      | List (_, [ Atom (_, Symbol "unquote"); arg ]) :: rest ->
        (match eval env arg with
         | MForm f' -> splice (f' :: acc) rest
         | _ -> form_error l "unquote of a non-form value")
      | List (_, [ Atom (_, Symbol "unquote-splicing"); arg ]) :: rest ->
        (match eval env arg with
         | MForm (List (_, xs)) -> splice (List.rev xs @ acc) rest
         | MForm (Vector (_, xs)) -> splice (List.rev (Array.to_list xs) @ acc) rest
         | MForm (Atom (_, Nil)) -> splice acc rest
         | _ -> form_error l "unquote-splicing of a non-sequence")
      | x :: rest -> splice (squote env mark x :: acc) rest
    in
    List (l, splice [] items)
  | Vector (l, items) ->
    (match squote env mark (List (l, Array.to_list items)) with
     | List (_, xs) -> Vector (l, Array.of_list xs)
     | _ -> assert false)
  | Set (l, items) ->
    (match squote env mark (List (l, items)) with
     | List (_, xs) -> Set (l, xs)
     | _ -> assert false)
  | Map (l, kes) ->
    Map (l, List.map (fun (k, v) -> squote env mark k, squote env mark v) kes)
  | Meta (l, m, x) -> Meta (l, squote env mark m, squote env mark x)
  | Quote (l, x) -> Quote (l, squote env mark x)
  | Atom (l, Symbol s) ->
    (* rename template symbols; record original for the analyzer *)
    let renamed = s ^ tag in
    Hashtbl.replace marks renamed s;
    Atom (l, Symbol renamed)
  | Atom _ -> f

and eval (env : (string, mval) Hashtbl.t) (f : form) : mval =
  match f with
  | Atom (_, Symbol s) ->
    (match Hashtbl.find_opt env s with
     | Some v -> v
     | None ->
       if is_eval_builtin s then MBuiltin s
       else (match macro_of_sym s with
         | Some fn -> MFn fn
         | None -> MForm f))
  | Atom _ -> MForm f
  | Quote (_, inner) -> MForm inner
  | Meta (_, _, inner) -> eval env inner
  | Vector (l, items) -> MForm (Vector (l, Array.of_list (eval_list env (Array.to_list items))))
  | Set (l, items) -> MForm (Set (l, eval_list env items))
  | Map (l, kes) ->
    MForm (Map (l, List.map (fun (k, v) -> eval_form env k, eval_form env v) kes))
  | List (_, Atom (_, Symbol "syntax-quote") :: [ inner ]) ->
    incr mark_ctr;
    MForm (squote env !mark_ctr inner)
  | List (_, Atom (_, Symbol "quote") :: [ inner ]) -> MForm inner
  | List (l, Atom (_, Symbol "if") :: args) ->
    (match args with
     | [ c; t; e ] -> if truthy (eval env c) then eval env t else eval env e
     | [ c; t ] -> if truthy (eval env c) then eval env t else MForm (Atom (l, Nil))
     | _ -> form_error l "if: expected 2 or 3 arguments")
  | List (l, Atom (_, Symbol "do") :: body) ->
    let rec last = function
      | [] -> MForm (Atom (l, Nil))
      | [ x ] -> eval env x
      | x :: rest -> ignore (eval env x); last rest
    in
    last body
  | List (l, Atom (_, Symbol "let") :: Vector (_, binds) :: body) ->
    let env' = Hashtbl.copy env in
    let rec bind = function
      | Atom (_, Symbol n) :: v :: rest ->
        Hashtbl.replace env' n (eval env' v);
        bind rest
      | [] -> ()
      | _ -> form_error l "macro let: binding vector must be name/value pairs"
    in
    bind (Array.to_list binds);
    eval env' (List (l, Atom (l, Symbol "do") :: body))
  | List (l, Atom (_, Symbol ("fn" | "fn*")) :: rest) ->
    eval_fn l env "anon" rest
  | List (l, callee :: args) ->
    let callee_name =
      match callee with Atom (_, Symbol s) -> Some s | _ -> None
    in
    (match callee_name with
     | Some s ->
       (* a call to another macro passes raw arg forms *)
       (match Hashtbl.find_opt env s with
        | Some v -> apply l v (List.map (eval env) args)
        | None ->
          (match macro_of_sym s with
           | Some fn ->
             apply l (MFn fn) (List.map (fun a -> MForm a) args)
           | None ->
             if is_eval_builtin s then eval_builtin_apply l s (List.map (eval env) args)
             else
               let cv = eval env callee in
               apply l cv (List.map (eval env) args)))
     | None ->
       let cv = eval env callee in
       apply l cv (List.map (eval env) args))
  | List (l, []) -> MForm (List (l, []))

and eval_form env f = match eval env f with MForm f -> f | _ -> f
and eval_list env fs = List.map (eval_form env) fs

and eval_fn l env name rest =
  match rest with
  | Vector (_, params) :: body ->
    let ps, rst =
      let rec split acc = function
        | Atom (_, Symbol "&") :: Atom (_, Symbol r) :: _ -> (List.rev acc, Some r)
        | Atom (_, Symbol p) :: xs -> split (p :: acc) xs
        | [] -> (List.rev acc, None)
        | _ -> form_error l "fn params must be symbols"
      in
      split [] (Array.to_list params)
    in
    MFn { mname = name; mparams = ps; mrest = rst; mbody = body; menv = env }
  | Atom (_, Symbol n) :: rest -> eval_fn l env n rest
  | _ -> form_error l "fn: expected parameter vector"

and apply l v args : mval =
  match v with
  | MFn fn ->
    let env = Hashtbl.copy fn.menv in
    let rec bind_params ps xs =
      match ps, xs with
      | [], xs -> xs
      | p :: ps, x :: xs -> Hashtbl.replace env p x; bind_params ps xs
      | _ :: _, [] -> form_error l "%s: too few arguments" fn.mname
    in
    let leftover = bind_params fn.mparams args in
    (match fn.mrest with
     | Some r -> Hashtbl.replace env r (MForm (List (l, List.map (function MForm f -> f | _ -> Atom (l, Nil)) leftover)))
     | None -> if leftover <> [] then form_error l "%s: too many arguments" fn.mname);
    let rec last = function
      | [] -> MForm (Atom (l, Nil))
      | [ x ] -> eval env x
      | x :: rest -> ignore (eval env x); last rest
    in
    last fn.mbody
  | MBuiltin name -> eval_builtin_apply l name args
  | _ -> form_error l "macro apply: not a function"

(* expand a macro call: arguments are raw forms *)
let expand (fn : mfn) (args : form list) (l : loc) : form =
  match apply l (MFn fn) (List.map (fun a -> MForm a) args) with
  | MForm f -> f
  | _ -> form_error l "macro %s did not return a form" fn.mname

(* parse a defmacro form: (defmacro name [params & rest] body...) *)
let register_defmacro (ns : string) (f : form) : unit =
  match f with
  | List (l, _ :: Atom (_, Symbol name) :: rest) ->
    (match eval_fn l (Hashtbl.create 8) name rest with
     | MFn fn -> register_macro ns name fn
     | _ -> form_error l "defmacro: bad form")
  | _ -> ()

let locate l = l
