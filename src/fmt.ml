(* Canonical formatter for .lg/.cljc forms: flat if it fits, else
   vertical layout with 2-space indent. Reader-conditionals resolve to
   the target branch, so fmt rewrites the selected surface. *)
open Syntax

let atom_str = function
  | Int i -> string_of_int i
  | Float x -> let s = Printf.sprintf "%g" x in if String.contains s '.' then s else s ^ ".0"
  | Bool b -> string_of_bool b
  | Char c -> "\\" ^ String.make 1 c
  | Str s -> Printf.sprintf "%S" s
  | Keyword k -> ":" ^ k
  | Symbol s -> s
  | Nil -> "nil"

let width = 90

let seq b sep p =
  let rec loop = function
    | [] -> ()
    | [ x ] -> p x
    | x :: tl -> p x; Buffer.add_string b sep; loop tl
  in
  loop

let flat f =
  let b = Buffer.create 64 in
  let rec go = function
    | Atom (_, a) -> Buffer.add_string b (atom_str a)
    | List (_, fs) -> Buffer.add_char b '('; seq b " " go fs; Buffer.add_char b ')'
    | Vector (_, fs) -> Buffer.add_char b '['; seq b " " go (Array.to_list fs); Buffer.add_char b ']'
    | Map (_, kvs) -> Buffer.add_char b '{'; seq b " " (fun (k, v) -> go k; Buffer.add_char b ' '; go v) kvs; Buffer.add_char b '}'
    | Set (_, fs) -> Buffer.add_string b "#{"; seq b " " go fs; Buffer.add_char b '}'
    | Meta (_, m, f) -> Buffer.add_char b '^'; go m; Buffer.add_char b ' '; go f
    | Quote (_, f) -> Buffer.add_char b '\''; go f
  in
  go f; Buffer.contents b

let rec doc ind f =
  let s = flat f in
  if String.length s + ind <= width then s
  else
    match f with
    | List (_, fs) ->
      let pad = String.make (ind + 2) ' ' in
      (match fs with
       | [] -> "()"
       | [ x ] -> "(" ^ doc (ind + 1) x ^ ")"
       | h :: rest ->
         "(" ^ doc (ind + 2) h ^ "\n" ^ pad
         ^ String.concat ("\n" ^ pad) (List.map (doc (ind + 2)) rest) ^ ")")
    | Vector (_, fs) ->
      let pad = String.make (ind + 2) ' ' in
      "[" ^ String.concat ("\n" ^ pad) (List.map (doc (ind + 2)) (Array.to_list fs)) ^ "]"
    | Map (_, kvs) ->
      let pad = String.make (ind + 2) ' ' in
      "{"
      ^ String.concat ("\n" ^ pad)
          (List.map (fun (k, v) -> doc (ind + 2) k ^ " " ^ doc (ind + 2) v) kvs)
      ^ "}"
    | Set (_, fs) ->
      let pad = String.make (ind + 2) ' ' in
      "#{" ^ String.concat ("\n" ^ pad) (List.map (doc (ind + 2)) fs) ^ "}"
    | Meta (_, m, f2) -> "^" ^ doc ind m ^ " " ^ doc (ind + 1) f2
    | Quote (_, f2) -> "'" ^ doc (ind + 1) f2
    | Atom _ -> s

let format_forms fs = String.concat "\n" (List.map (doc 0) fs) ^ "\n"

let format_file ?(target = Reader.TNative) file =
  let ic = open_in file in
  let n = in_channel_length ic in
  let src = really_input_string ic n in
  close_in ic;
  try
    let fs = Reader.read_file ~file ~target src in
    format_forms fs
  with Syntax.Read_error (l, m) -> raise (Err.E (l, "E201", m, []))
