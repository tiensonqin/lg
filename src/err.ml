(* Rich error reporting — Elm-style source snippets with caret spans,
   error codes, and hints. Err.E carries (loc, code, msg, hints); plain
   Type_error paths get wrapped as E100 at the compiler boundary so every
   diagnostic still gets a snippet. *)

open Syntax

exception E of loc * string * string * string list

let err l code msg hints = raise (E (l, code, msg, hints))

(* source line cache for snippets *)
let src_cache : (string, string array) Hashtbl.t = Hashtbl.create 8

let src_line file n =
  let lines =
    match Hashtbl.find_opt src_cache file with
    | Some a -> a
    | None ->
      (try
         let ic = open_in file in
         let rec rd acc = try rd (input_line ic :: acc) with End_of_file -> close_in ic; List.rev acc in
         let a = Array.of_list (rd []) in
         Hashtbl.replace src_cache file a; a
       with Sys_error _ -> [||])
  in
  if n >= 1 && n <= Array.length lines then Some lines.(n - 1) else None

let pad s w = if String.length s >= w then s else s ^ String.make (w - String.length s) ' '

(* underline width: scan the token at (line, col) — an atom runs to the
   next delimiter; a list form underlines just the head token *)
let span_width line_txt col =
  let n = String.length line_txt in
  let i = col - 1 in
  if i < 0 || i >= n then 1
  else
    let c0 = line_txt.[i] in
    if c0 = '(' || c0 = '[' || c0 = '{' then 1
    else
      let rec scan j =
        if j >= n then j
        else match line_txt.[j] with
          | ' ' | '\t' | ')' | ']' | '}' | '(' | '[' | '{' | '"' | ';' -> j
          | _ -> scan (j + 1)
      in
      max 1 (scan i - i)

let render l code msg hints =
  let b = Buffer.create 256 in
  Buffer.add_string b (Printf.sprintf "error[%s]: %s\n" code msg);
  Buffer.add_string b (Printf.sprintf "  --> %s:%d:%d\n" l.file l.line l.col);
  (match src_line l.file l.line with
   | Some txt ->
     let ln = string_of_int l.line in
     let w = String.length ln in
     Buffer.add_string b ("  " ^ String.make w ' ' ^ "|\n");
     Buffer.add_string b ("  " ^ ln ^ "| " ^ txt ^ "\n");
     let ul = span_width txt l.col in
     let padto = max 1 l.col in
     Buffer.add_string b ("  " ^ String.make w ' ' ^ "| " ^ String.make (padto - 1) ' ' ^ String.make ul '^' ^ "\n")
   | None -> ());
  List.iter (fun h -> Buffer.add_string b ("  = " ^ h ^ "\n")) hints;
  Buffer.contents b

let report e = match e with E (l, c, m, hs) -> prerr_string (render l c m hs) | _ -> ()

let warn l code msg =
  let b = Buffer.create 128 in
  Buffer.add_string b (Printf.sprintf "warning[%s]: %s\n" code msg);
  Buffer.add_string b (Printf.sprintf "  --> %s:%d:%d\n" l.file l.line l.col);
  (match src_line l.file l.line with
   | Some txt ->
     let ln = string_of_int l.line in
     let w = String.length ln in
     Buffer.add_string b ("  " ^ String.make w ' ' ^ "|\n");
     Buffer.add_string b ("  " ^ ln ^ "| " ^ txt ^ "\n");
     let ul = span_width txt l.col in
     Buffer.add_string b ("  " ^ String.make w ' ' ^ "| " ^ String.make (max 1 l.col - 1) ' ' ^ String.make ul '^' ^ "\n")
   | None -> ());
  prerr_string (Buffer.contents b)

(* edit distance for "did you mean" *)
let levenshtein a b =
  let la = String.length a and lb = String.length b in
  let d = Array.make_matrix (la + 1) (lb + 1) 0 in
  for i = 0 to la do d.(i).(0) <- i done;
  for j = 0 to lb do d.(0).(j) <- j done;
  for i = 1 to la do
    for j = 1 to lb do
      let cost = if a.[i - 1] = b.[j - 1] then 0 else 1 in
      d.(i).(j) <- min (min (d.(i-1).(j) + 1) (d.(i).(j-1) + 1)) (d.(i-1).(j-1) + cost)
    done
  done;
  d.(la).(lb)

let did_you_mean name candidates =
  let best =
    List.fold_left
      (fun (bd, bn) c ->
        let d = levenshtein name c in
        if d < bd then (d, c) else (bd, bn))
      (4, "") candidates
  in
  match best with d, n when d <= 3 && n <> "" -> Some n | _ -> None
