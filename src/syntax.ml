(* Surface syntax: the result of reading .lg2 source files. *)

type loc = { file : string; line : int; col : int }

let no_loc = { file = "<unknown>"; line = 0; col = 0 }

let string_of_loc l = Printf.sprintf "%s:%d:%d" l.file l.line l.col

type atom =
  | Int of int
  | Float of float
  | Bool of bool
  | Char of char
  | Str of string
  | Keyword of string
  | Symbol of string
  | Nil

type form =
  | Atom of loc * atom
  | List of loc * form list
  | Vector of loc * form array
  | Map of loc * (form * form) list
  | Set of loc * form list
  (* ^meta form — meta is the raw metadata form (symbol, keyword, or map). *)
  | Meta of loc * form * form
  (* (quote form) produced by the ' reader macro *)
  | Quote of loc * form

(* char literal printer — the inverse of Reader's named_char. Shared by
   every form printer (macro form_to_string, fmt) so named/control chars
   never leak into emitted text as raw bytes. *)
let char_to_string = function
  | '\n' -> "\\newline" | ' ' -> "\\space" | '\t' -> "\\tab"
  | '\r' -> "\\return" | '\b' -> "\\backspace" | '\012' -> "\\formfeed"
  | c when c >= '!' && c <= '~' -> "\\" ^ String.make 1 c
  | c -> Printf.sprintf "\\u%04x" (Char.code c)

exception Read_error of loc * string

let read_error loc msg = raise (Read_error (loc, msg))

let atom_loc = function
  | Atom (l, _) | List (l, _) | Vector (l, _) | Map (l, _) | Set (l, _) | Meta (l, _, _) | Quote (l, _) -> l

let symbol_name = function Atom (_, Symbol s) -> Some s | _ -> None

let is_symbol s = function Atom (_, Symbol s2) -> String.equal s s2 | _ -> false
