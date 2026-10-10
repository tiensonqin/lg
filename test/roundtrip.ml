(* reader round-trip harness: parse -> form_to_string -> parse -> form_eq.
   Usage: roundtrip <file.lg>... — exits 1 listing every file whose printed
   forms do not re-parse to structurally equal forms. *)

let roundtrip file =
  let src =
    let ic = open_in file in
    let n = in_channel_length ic in
    let s = really_input_string ic n in
    close_in ic;
    s
  in
  let fs = Lgc.Reader.read_file ~file ~preserve:true src in
  let printed = String.concat "\n" (List.map Lgc.Macro.form_to_string fs) in
  let fs2 =
    try Lgc.Reader.read_file ~file:(file ^ "#printed") ~preserve:true printed
    with Lgc.Syntax.Read_error (l, m) ->
      Printf.printf "FAIL(roundtrip-parse) %s:%d:%d %s\n" file l.Lgc.Syntax.line l.Lgc.Syntax.col m;
      exit 1
  in
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

let () =
  let files = List.tl (Array.to_list Sys.argv) in
  if files = [] then begin
    prerr_endline "usage: roundtrip <file.lg>...";
    exit 2
  end;
  let bad = List.filter (fun f -> not (roundtrip f)) files in
  if bad = [] then
    Printf.printf "ok roundtrip (%d files)\n" (List.length files)
  else exit 1
