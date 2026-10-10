(* reader round-trip harness: parse -> form_to_string -> parse -> form_eq.
   Usage: roundtrip <file.lg>... — exits 1 listing every file whose printed
   forms do not re-parse to structurally equal forms.
   Mode --same <a.lg> <b.lg>... (pairs): compares two files' form lists —
   used by the fmt-fidelity lane to prove `lg fmt` preserves the form tree
   (comments excluded — they are not forms; checked separately). *)

let read_forms file =
  let ic = open_in file in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  try Lgc.Reader.read_file ~file ~preserve:true s
  with Lgc.Syntax.Read_error (l, m) ->
    Printf.printf "FAIL(parse) %s:%d:%d %s\n" file l.Lgc.Syntax.line l.Lgc.Syntax.col m;
    exit 1

let compare_forms file fs fs2 =
  if List.length fs <> List.length fs2 then begin
    Printf.printf "FAIL(roundtrip) %s: %d forms -> %d re-parsed\n" file
      (List.length fs) (List.length fs2);
    false
  end
  else
    match List.find_opt (fun (a, b) -> not (Lgc.Macro.form_eq a b)) (List.combine fs fs2) with
    | Some (a, b) ->
      Printf.printf "FAIL(roundtrip) %s: form mismatch\n  in:  %s\n  out: %s\n" file
        (Lgc.Macro.form_to_string a) (Lgc.Macro.form_to_string b);
      false
    | None -> true

let roundtrip file =
  let fs = read_forms file in
  let printed = String.concat "\n" (List.map Lgc.Macro.form_to_string fs) in
  let fs2 =
    try Lgc.Reader.read_file ~file:(file ^ "#printed") ~preserve:true printed
    with Lgc.Syntax.Read_error (l, m) ->
      Printf.printf "FAIL(roundtrip-parse) %s:%d:%d %s\n" file l.Lgc.Syntax.line l.Lgc.Syntax.col m;
      exit 1
  in
  compare_forms file fs fs2

let () =
  let args = List.tl (Array.to_list Sys.argv) in
  match args with
  | [] ->
    prerr_endline "usage: roundtrip [--same <a.lg> <b.lg>...] <file.lg>...";
    exit 2
  | "--same" :: pairs ->
    let rec loop bad = function
      | a :: b :: rest ->
        let ok =
          let fs_a = read_forms a and fs_b = read_forms b in
          compare_forms (a ^ " vs " ^ b) fs_a fs_b
        in
        loop (if ok then bad else a :: bad) rest
      | [] -> List.rev bad
      | _ -> prerr_endline "roundtrip --same: odd number of files"; exit 2
    in
    let bad = loop [] pairs in
    if bad = [] then
      Printf.printf "ok same (%d pairs)\n" (List.length pairs / 2)
    else exit 1
  | files ->
    let bad = List.filter (fun f -> not (roundtrip f)) files in
    if bad = [] then
      Printf.printf "ok roundtrip (%d files)\n" (List.length files)
    else exit 1
