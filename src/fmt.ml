(* Canonical formatter for .lg/.cljc forms: flat if it fits, else
   vertical layout with 2-space indent.

   Fidelity: fmt preserves ';' comments, '#_' discarded forms, and every
   branch of '#?' reader conditionals. The reader's ~preserve mode turns
   '#_'/'#?' into pseudo-lists headed by "#_"/"#?"/"#?@" symbols; fmt
   prints those back in reader syntax. Comments are re-attached by source
   line: leading comments precede their form, same-line comments trail
   it, and comments inside a multi-line form's span are injected at the
   form's inner indentation. *)

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

(* pseudo-node heads produced by reader ~preserve *)
let is_tag s = function
  | Atom (_, Symbol t) -> String.equal s t
  | _ -> false

let flat f =
  let b = Buffer.create 64 in
  let rec go = function
    | Atom (_, a) -> Buffer.add_string b (atom_str a)
    | List (_, Atom (_, Symbol "#_") :: [ d ]) ->
      Buffer.add_string b "#_"; go d
    | List (_, Atom (_, Symbol t) :: rest) when t = "#?" || t = "#?@" ->
      Buffer.add_string b t; Buffer.add_char b '(';
      seq b " " go rest; Buffer.add_char b ')'
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
    | List (_, Atom (_, Symbol ("#_" | "#?" | "#?@")) :: _) -> s
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

(* ---------- source scan: comments + top-level bracket spans ---------- *)

type cmt = { cl : int; cc : int; ct : string }
type span = { sl : int; scol : int; el : int; ecol : int }

(* one pass over src: collect ';' comments and the (start,end) extent of
   every depth-0 bracket group. Strings are skipped (counting newlines);
   '\' char literals are skipped two chars (the reader rejects delimiter
   char literals, so no fake ';'/'"' can hide inside). *)
let scan src : cmt list * span list =
  let n = String.length src in
  let rec go i line col stack cms sps =
    if i >= n then (List.rev cms, List.rev sps)
    else
      match src.[i] with
      | '\n' -> go (i + 1) (line + 1) 1 stack cms sps
      | ';' ->
        let j = ref i in
        while !j < n && src.[!j] <> '\n' do incr j done;
        let ct = String.sub src i (!j - i) in
        go !j line (col + (!j - i)) stack ({ cl = line; cc = col; ct } :: cms) sps
      | '"' -> skip_str (i + 1) line (col + 1) stack cms sps
      | '\\' -> go (min n (i + 2)) line (col + 2) stack cms sps
      | '#' when i + 1 < n && src.[i + 1] = '{' ->
        go (i + 2) line (col + 2) ((line, col) :: stack) cms sps
      | '(' | '[' | '{' ->
        go (i + 1) line (col + 1) ((line, col) :: stack) cms sps
      | ')' | ']' | '}' ->
        (match stack with
         | (sl, scol) :: [] ->
           go (i + 1) line (col + 1) [] cms ({ sl; scol; el = line; ecol = col + 1 } :: sps)
         | _ :: tl -> go (i + 1) line (col + 1) tl cms sps
         | [] -> go (i + 1) line (col + 1) [] cms sps)
      | _ -> go (i + 1) line (col + 1) stack cms sps
  and skip_str i line col stack cms sps =
    if i >= n then (List.rev cms, List.rev sps)
    else
      match src.[i] with
      | '"' -> go (i + 1) line (col + 1) stack cms sps
      | '\\' -> skip_str (i + 2) line (col + 2) stack cms sps
      | '\n' -> skip_str (i + 1) (line + 1) 1 stack cms sps
      | _ -> skip_str (i + 1) line (col + 1) stack cms sps
  in
  go 0 1 1 [] [] []

(* ---------- comment bucketing and emission ---------- *)

let indent_of line =
  let rec k i = if i < String.length line && line.[i] = ' ' then k (i + 1) else i in
  String.sub line 0 (k 0)

let lines_of s = String.split_on_char '\n' s

(* splice a comment onto a doc: onto first line if [first], else last *)
let splice d ~first ct =
  match lines_of d with
  | [] -> d ^ " " ^ ct
  | h :: tl ->
    if first then String.concat "\n" ((h ^ " " ^ ct) :: tl)
    else
      let rev = List.rev (h :: tl) in
      (match rev with
       | last :: rest -> String.concat "\n" (List.rev ((last ^ " " ^ ct) :: rest))
       | [] -> d ^ " " ^ ct)

(* in-form comments: for a multi-line doc inject them before the last
   line at that line's indent (staying inside the parens); for a
   single-line doc they cannot live inside, so emit after the form *)
let inject_inner d cts =
  if cts = [] then d
  else
    match List.rev (lines_of d) with
    | [ _ ] ->
      d ^ "\n" ^ String.concat "\n" (List.map (fun c -> c.ct) cts)
    | last :: rest ->
      let pad = indent_of last in
      (* rest is reversed lines: l(n-1)..l1 — put comments before last *)
      String.concat "\n" (List.rev rest @ List.map (fun c -> pad ^ c.ct) cts @ [ last ])
    | [] -> d

let format_forms src fs =
  let cms, sps = scan src in
  let cms = ref cms and sps = ref sps in
  let next_loc = ref None in
  let b = Buffer.create 256 in
  (* keep a blank line wherever the source had one between items *)
  let last_end = ref 0 in
  let gap l = if !last_end > 0 && l - !last_end > 1 then Buffer.add_char b '\n' in
  let emit_cmt c =
    gap c.cl; Buffer.add_string b c.ct; Buffer.add_char b '\n'; last_end := c.cl
  in
  let forms = Array.of_list fs in
  for i = 0 to Array.length forms - 1 do
    let f = forms.(i) in
    let fl = atom_loc f in
    next_loc := (if i + 1 < Array.length forms then Some (atom_loc forms.(i + 1)) else None);
    (* this form's span: the first remaining span opening in
       [this form's start, next form's start). Brackets always open at or
       after their form's loc (covering ^meta, 'quote, #_, #? prefixes);
       a span before this form is orphaned and skipped. *)
    let span =
      let rec loop () =
        match !sps with
        | [] -> None
        | s :: tl ->
          let sp = (s.sl, s.scol) in
          if sp < (fl.line, fl.col) then (sps := tl; loop ())
          else if
            (match !next_loc with
             | Some nl -> sp < (nl.line, nl.col)
             | None -> true)
          then (sps := tl; Some s)
          else None
      in
      loop ()
    in
    (* leading comments: line strictly before this form's start *)
    let rec take_leading () =
      match !cms with
      | c :: tl when c.cl < fl.line -> emit_cmt c; cms := tl; take_leading ()
      | _ -> ()
    in
    take_leading ();
    let d = doc 0 f in
    let el, ecol =
      match span with Some s -> (s.el, s.ecol) | None -> (fl.line, fl.col)
    in
    (* trailing comment on the form's first line *)
    let first_trail =
      match !cms with
      | c :: tl when c.cl = fl.line && c.cc > fl.col -> cms := tl; Some c
      | _ -> None
    in
    (* in-form comments: strictly inside the span *)
    let rec take_inner acc =
      match !cms with
      | c :: tl when c.cl > fl.line && c.cl < el -> cms := tl; take_inner (c :: acc)
      | _ -> List.rev acc
    in
    let inner = take_inner [] in
    (* trailing comment on the form's last line *)
    let last_trail =
      match !cms with
      | c :: tl when c.cl = el && c.cc >= ecol -> cms := tl; Some c
      | _ -> None
    in
    let d = match first_trail with Some c -> splice d ~first:true c.ct | None -> d in
    let d = match last_trail with Some c -> splice d ~first:false c.ct | None -> d in
    let d = inject_inner d inner in
    gap fl.line;
    Buffer.add_string b d; Buffer.add_char b '\n';
    last_end := el
  done;
  (* trailing comments after the last form *)
  List.iter emit_cmt !cms;
  Buffer.contents b

let format_file ?(target = Reader.TNative) file =
  let ic = open_in file in
  let n = in_channel_length ic in
  let src = really_input_string ic n in
  close_in ic;
  try
    let fs = Reader.read_file ~file ~target ~preserve:true src in
    format_forms src fs
  with Syntax.Read_error (l, m) -> raise (Err.E (l, "E201", m, []))
