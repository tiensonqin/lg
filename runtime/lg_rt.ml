(* lg runtime prelude — printers and small helpers.

   Data structures come from [Clj_core]; this file only carries what the
   emitter needs on top: `str`/`println`/`pr-str` printers per static type,
   list take/drop/range, string->char list, and numeric coercions. *)

let str_int = string_of_int
let str_float x =
  let s = Printf.sprintf "%g" x in
  s
let str_bool = string_of_bool
let str_char = String.make 1
let str_string s = s
let str_kw (k : Clj_core.Keyword.t) = Clj_core.Keyword.to_string k
let str_sym (s : Clj_core.Symbol.t) = Clj_core.Symbol.to_string s
let str_unit () = "nil"

let str_list pr xs =
  "(" ^ String.concat " " (List.map pr xs) ^ ")"

let str_vec pr v =
  "[" ^ String.concat " " (List.map pr (Clj_core.Vec.to_list v)) ^ "]"

let str_map kpr vpr m =
  let entries = List.of_seq (Clj_core.Map.seq m) in
  "{" ^ String.concat ", " (List.map (fun (k, v) -> kpr k ^ " " ^ vpr v) entries) ^ "}"

let str_set pr s =
  "#{" ^ String.concat " " (List.map pr (Clj_core.Set.to_list s)) ^ "}"

let str_opt pr = function Some x -> pr x | None -> "nil"

(* seq on a dynamic collection — used for `seq` where the static type is
   known per call site; these are the fallbacks *)

let vec_to_list = Clj_core.Vec.to_list
let map_to_list m = List.of_seq (Clj_core.Map.seq m)
let set_to_list = Clj_core.Set.to_list

let string_chars s = List.init (String.length s) (String.get s)

let list_take n xs =
  let rec go acc n xs =
    if n <= 0 then List.rev acc
    else match xs with [] -> List.rev acc | x :: t -> go (x :: acc) (n - 1) t
  in
  go [] n xs

let list_drop n xs =
  let rec go n xs =
    if n <= 0 then xs else match xs with [] -> [] | _ :: t -> go (n - 1) t
  in
  go n xs

let range a b =
  if a >= b then [] else List.init (b - a) (fun i -> a + i)

(* ---- dyn: the closed variant behind `any` (^any) and heterogeneous
   literals. Values are boxed at literal/call boundaries and unboxed via
   `as_*` (which raise on a wrong tag — the TAny type is a dynamic
   boundary, not a claim). No Obj.magic anywhere. *)

type dyn =
  | DInt of int
  | DFloat of float
  | DBool of bool
  | DChar of char
  | DStr of string
  | DKw of Clj_core.Keyword.t
  | DSym of Clj_core.Symbol.t
  | DUnit
  | DOpt of dyn option
  | DList of dyn list
  | DVec of dyn Clj_core.Vec.t
  | DMap of (dyn, (dyn, dyn) Clj_core.Map.nest) Clj_core.Map.t
  | DSet of dyn Clj_core.Set.t

let rec str_dyn = function
  | DInt i -> string_of_int i
  | DFloat x -> str_float x
  | DBool b -> string_of_bool b
  | DChar c -> String.make 1 c
  | DStr s -> s
  | DKw k -> Clj_core.Keyword.to_string k
  | DSym s -> Clj_core.Symbol.to_string s
  | DUnit -> "nil"
  | DOpt (Some d) -> str_dyn d
  | DOpt None -> "nil"
  | DList xs -> str_list str_dyn xs
  | DVec v -> str_vec str_dyn v
  | DMap m -> str_map str_dyn str_nest_dyn m
  | DSet s -> str_set str_dyn s

and str_nest_dyn n =
  match n with
  | Clj_core.Map.Leaf d -> str_dyn d
  | Clj_core.Map.Nest m -> str_map str_dyn str_nest_dyn m

let as_int = function DInt i -> i | _ -> invalid_arg "dyn: expected int"
let as_float = function DFloat x -> x | DInt i -> float_of_int i | _ -> invalid_arg "dyn: expected float"
let as_bool = function DBool b -> b | _ -> invalid_arg "dyn: expected bool"
let as_char = function DChar c -> c | _ -> invalid_arg "dyn: expected char"
let as_string = function DStr s -> s | _ -> invalid_arg "dyn: expected string"
let as_kw = function DKw k -> k | _ -> invalid_arg "dyn: expected keyword"
let as_sym = function DSym s -> s | _ -> invalid_arg "dyn: expected symbol"
let as_unit = function DUnit -> () | _ -> invalid_arg "dyn: expected unit"
let as_opt = function DOpt o -> o | _ -> invalid_arg "dyn: expected option"
let as_list = function DList xs -> xs | _ -> invalid_arg "dyn: expected list"
let as_vec = function DVec v -> v | _ -> invalid_arg "dyn: expected vec"
let as_map = function DMap m -> m | _ -> invalid_arg "dyn: expected map"
let as_set = function DSet s -> s | _ -> invalid_arg "dyn: expected set"


let no_match () = failwith "match: no clause matched"

(* bridges between a (Keyword.t, dyn) heterogeneous lg map (TMap (kw, any))
   and clj-core's (dyn, (dyn, dyn) nest) Map.t used by Map.get_in / assoc_in /
   update_in / select_keys on dyn maps *)
let nest_map_of_dyn_map m =
  List.fold_left
    (fun acc (k, v) ->
      let n = match v with DMap s -> Clj_core.Map.Nest s | d -> Clj_core.Map.Leaf d in
      Clj_core.Map.assoc acc (DKw k) n)
    (Clj_core.Map.of_list []) (Clj_core.Map.to_list m)

let dyn_map_of_nest_map m =
  List.fold_left
    (fun acc (k, n) ->
      match k with
      | DKw kw ->
        let d = match n with Clj_core.Map.Leaf d -> d | Clj_core.Map.Nest s -> DMap s in
        Clj_core.Map.assoc acc kw d
      | _ -> acc)
    (Clj_core.Map.of_list []) (Clj_core.Map.to_list m)

let interpose sep xs =
  match xs with [] -> [] | x :: rest -> x :: List.concat_map (fun y -> [ sep; y ]) rest

let butlast xs = match List.rev xs with [] -> [] | _ :: t -> List.rev t
let last_opt xs = match xs with [] -> None | _ -> Some (List.nth xs (List.length xs - 1))
let second_opt xs = match xs with _ :: x :: _ -> Some x | _ -> None

let rec take_while f xs =
  match xs with [] -> [] | x :: t -> if f x then x :: take_while f t else []

let rec drop_while f xs =
  match xs with [] -> [] | x :: t -> if f x then drop_while f t else xs

let distinct xs =
  let rec go seen = function
    | [] -> List.rev seen
    | x :: t -> if List.mem x seen then go seen t else go (x :: seen) t
  in
  go [] xs

let frequencies xs =
  List.fold_left
    (fun m x -> Clj_core.Map.assoc m x (match Clj_core.Map.get m x with Some n -> n + 1 | None -> 1))
    (Clj_core.Map.of_list []) xs

let group_by f xs =
  List.fold_left
    (fun m x ->
      let k = f x in
      Clj_core.Map.assoc m k (match Clj_core.Map.get m k with Some vs -> vs @ [ x ] | None -> [ x ]))
    (Clj_core.Map.of_list []) xs

let dyn_truthy = function DBool b -> b | DUnit -> false | DOpt None -> false | _ -> true
