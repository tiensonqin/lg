(* Reader: .lg2 source text -> form list.

   Supported reader syntax:
     ( ) [ ] { } #{ }  '  ^meta  #_discard  ;line-comment
   Atomics: int (dec, 0x hex, -), float, "string" with escapes, \c chars,
            true/false/nil, :keyword, symbol. *)

open Syntax

let is_ws = function ' ' | '\t' | '\n' | '\r' | ',' -> true | _ -> false
let is_delim = function
  | ' ' | '\t' | '\n' | '\r' | ',' | '(' | ')' | '[' | ']' | '{' | '}' | '"' | ';' | '\'' | '`' | '~' | '^' | '@' -> true
  | _ -> false

let is_digit c = c >= '0' && c <= '9'

let named_char = function
  | "newline" -> '\n' | "space" -> ' ' | "tab" -> '\t' | "return" -> '\r'
  | "backspace" -> '\b' | "formfeed" -> '\012' | s -> s.[0]

(* reader-conditional target (.cljc): native (default) or js (melange) *)
type target = TNative | TJs

let match_target t k =
  match t, k with
  | TNative, ("native" | "default") | TJs, ("js" | "default") -> true
  | _ -> false

type t = { src : string; file : string; mutable pos : int; mutable line : int; mutable col : int; target : target; preserve : bool }

let make ~file ?(target = TNative) ?(preserve = false) src =
  { src; file; pos = 0; line = 1; col = 1; target; preserve }

let eof r = r.pos >= String.length r.src
let peek r = if eof r then '\000' else r.src.[r.pos]
let peek2 r = if r.pos + 1 >= String.length r.src then '\000' else r.src.[r.pos + 1]

let loc r = { file = r.file; line = r.line; col = r.col }

let advance r =
  if r.src.[r.pos] = '\n' then (r.line <- r.line + 1; r.col <- 1) else r.col <- r.col + 1;
  r.pos <- r.pos + 1

let next r = let c = peek r in advance r; c

let rec skip_ws r =
  if eof r then ()
  else
    let c = peek r in
    if is_ws c then (advance r; skip_ws r)
    else if c = ';' then (
      while (not (eof r)) && peek r <> '\n' do advance r done;
      skip_ws r)
    else ()

let read_token r =
  let start = r.pos in
  while (not (eof r)) && not (is_delim (peek r)) do advance r done;
  String.sub r.src start (r.pos - start)

let is_int_token s =
  let s = if String.length s > 0 && (s.[0] = '-' || s.[0] = '+') then String.sub s 1 (String.length s - 1) else s in
  String.length s > 0 && String.for_all is_digit s

let is_hex_token s =
  String.length s > 2 && s.[0] = '0' && (s.[1] = 'x' || s.[1] = 'X')
  && String.for_all (fun c -> is_digit c || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F')) (String.sub s 2 (String.length s - 2))

let is_float_token s =
  (* [+-]? digit+ [. digit*]?  or  . digit+  with optional e/E exponent *)
  let n = String.length s in
  let i = ref (if n > 0 && (s.[0] = '-' || s.[0] = '+') then 1 else 0) in
  let digits () =
    let j = !i in
    while !i < n && is_digit s.[!i] do incr i done;
    !i - j
  in
  let whole = digits () in
  let frac =
    if !i < n && s.[!i] = '.' then (incr i; Some (digits ())) else None
  in
  let has_exp = !i < n && (s.[!i] = 'e' || s.[!i] = 'E') in
  (if has_exp then
     (incr i;
      if !i < n && (s.[!i] = '+' || s.[!i] = '-') then incr i));
  let expd = if has_exp then digits () else 0 in
  !i = n &&
  (match frac with
   | Some f -> whole + f > 0 && (not has_exp || expd > 0)
   | None -> whole > 0 && has_exp && expd > 0)

let read_string r =
  let l = loc r in
  ignore (next r);
  let buf = Buffer.create 16 in
  let rec loop () =
    if eof r then read_error l "unterminated string literal";
    match next r with
    | '"' -> ()
    | '\\' ->
      let e = next r in
      Buffer.add_char buf
        (match e with
         | 'n' -> '\n' | 't' -> '\t' | 'r' -> '\r' | '\\' -> '\\' | '"' -> '"'
         | 'b' -> '\b' | 'f' -> '\x0c'
         | c -> read_error l ("unknown escape \\\\" ^ String.make 1 c ^ " in string literal"));
      loop ()
    | c -> Buffer.add_char buf c; loop ()
  in
  loop ();
  Buffer.contents buf

let read_char r =
  let l = loc r in
  ignore (next r);
  let tok = read_token r in
  if String.length tok = 0 then read_error l "empty character literal"
  else if String.length tok = 5 && tok.[0] = 'u' then
    let cp = int_of_string ("0x" ^ String.sub tok 1 4) in
    if cp > 255 then read_error l ("char literal \\" ^ tok ^ " out of range (\\uXXXX is byte-wide)")
    else Atom (l, Char (Char.chr cp))
  else if tok.[0] = 'o' && String.length tok >= 2 && String.length tok <= 4
          && String.for_all is_digit (String.sub tok 1 (String.length tok - 1)) then
    let cp = int_of_string ("0o" ^ String.sub tok 1 (String.length tok - 1)) in
    if cp > 255 then read_error l ("char literal \\" ^ tok ^ " out of range")
    else Atom (l, Char (Char.chr cp))
  else Atom (l, Char (named_char tok))

let atom_of_token l tok : form =
  if tok = "nil" then
    read_error l "nil is removed: use () for unit, None for option"
  else if tok = "true" then Atom (l, Bool true)
  else if tok = "false" then Atom (l, Bool false)
  else if String.length tok > 0 && tok.[0] = ':' then Atom (l, Keyword (String.sub tok 1 (String.length tok - 1)))
  else if is_hex_token tok then Atom (l, Int (int_of_string tok))
  else if is_int_token tok then Atom (l, Int (int_of_string tok))
  else if is_float_token tok then Atom (l, Float (float_of_string tok))
  else Atom (l, Symbol tok)

let rec read_form r : form =
  skip_ws r;
  if eof r then read_error (loc r) "unexpected end of input";
  let l = loc r in
  match peek r with
  | '(' -> ignore (next r); List (l, read_seq r ')')
  | '[' -> ignore (next r); Vector (l, Array.of_list (read_seq r ']'))
  | '{' ->
    ignore (next r);
    let items = read_seq r '}' in
    let rec pairs = function
      | [] -> []
      | [ _ ] -> read_error l "map literal requires an even number of forms"
      | k :: v :: rest -> (k, v) :: pairs rest
    in
    Map (l, pairs items)
  | '#' ->
    if peek2 r = '{' then (
      ignore (next r); ignore (next r);
      Set (l, read_seq r '}'))
    else if peek2 r = '_' then (
      ignore (next r); ignore (next r);
      let d = read_form r in
      (* preserve mode (fmt): keep the discarded form as a pseudo-node so
         the formatter can re-print it instead of dropping it *)
      if r.preserve then List (l, [ Atom (l, Symbol "#_"); d ])
      else read_form r)
    else if peek2 r = '?' then (
      (* #? / #?@ — .cljc reader conditional: pick the branch for the
         current target; scalar position yields the branch or nil *)
      match read_cond r l with
      | [ f ] -> f
      | [] -> Atom (l, Nil)
      | _ -> read_error l "#?@ splice is only valid inside a collection")
    else read_error l "unsupported # reader form"
  | '\'' -> ignore (next r); Quote (l, read_form r)
  | '^' ->
    ignore (next r);
    let m = read_form r in
    let f = read_form r in
    Meta (l, m, f)
  | '@' ->
    ignore (next r);
    let f = read_form r in
    List (l, [ Atom (l, Symbol "deref"); f ])
  | '`' -> ignore (next r); List (l, [ Atom (l, Symbol "syntax-quote"); read_form r ])
  | '~' ->
    ignore (next r);
    if peek r = '@' then (ignore (next r); List (l, [ Atom (l, Symbol "unquote-splicing"); read_form r ]))
    else List (l, [ Atom (l, Symbol "unquote"); read_form r ])
  | '"' -> Atom (l, Str (read_string r))
  | '\\' -> read_char r
  | ')' | ']' | '}' -> read_error l (Printf.sprintf "unmatched delimiter %c" (peek r))

  | _ -> atom_of_token l (read_token r)

(* #? / #?@ inside a collection: returns 0/1/many forms to splice in *)
and read_cond r l : form list =
  ignore (next r);  (* # *)
  ignore (next r);  (* ? *)
  let splice = peek r = '@' in
  if splice then ignore (next r);
  skip_ws r;
  if peek r <> '(' then read_error l "#? expects (keyword form ... )";
  ignore (next r);
  let rec pairs acc =
    skip_ws r;
    if eof r then read_error l "expected ), got end of input in #?";
    if peek r = ')' then (ignore (next r); List.rev acc)
    else
      let kw = read_form r in
      let f = read_form r in
      pairs ((kw, f) :: acc)
  in
  let ps = pairs [] in
  let rec sel = function
    | [] -> None
    | (Atom (_, Keyword k), f) :: _ when match_target r.target k -> Some f
    | _ :: tl -> sel tl
  in
  match sel ps with
  | result ->
    if r.preserve then
      (* keep every branch as a pseudo-node: (#? kw f kw f ...) or #?@ *)
      let tag = Atom (l, Symbol (if splice then "#?@" else "#?")) in
      let flat_ps = List.concat_map (fun (k, f) -> [ k; f ]) ps in
      [ List (l, tag :: flat_ps) ]
    else
      (match result with
       | None -> []
       | Some f ->
         if splice then
           (match f with
            | List (_, xs) -> xs
            | Vector (_, xs) -> Array.to_list xs
            | _ -> read_error l "#?@ branch must be a list or vector")
         else [ f ])

and read_seq r close : form list =
  skip_ws r;
  if eof r then read_error (loc r) (Printf.sprintf "expected %c, got end of input" close);
  if peek r = close then (ignore (next r); [])
  else
    let fs =
      if peek r = '#' && peek2 r = '?' then read_cond r (loc r)
      else [ read_form r ]
    in
    fs @ read_seq r close

let read_file ~file ?(target = TNative) ?(preserve = false) src : form list =
  let r = make ~file ~target ~preserve src in
  let rec go acc =
    skip_ws r;
    if eof r then List.rev acc
    else go (read_form r :: acc)
  in
  go []
