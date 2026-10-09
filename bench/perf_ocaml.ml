(* OCaml baseline for test/perf.lg — same ops via Clj_core *)
let bench name f =
  let t0 = Unix.gettimeofday () *. 1000. in
  let r = f () in
  Printf.printf "%s: %.0fms -> %s\n" name (Unix.gettimeofday () *. 1000. -. t0) r

let () =
  let n = 200000 in
  let v = List.init n Fun.id in
  bench "list-init" (fun () -> string_of_int (List.length v));
  bench "map+filter+reduce" (fun () ->
    string_of_int (List.fold_left ( + ) 0 (List.filter (fun x -> x mod 3 = 0) (List.map (fun x -> x * 2) v))));
  bench "atom+recur 1M" (fun () ->
    let rec g i acc = if i < 1000000 then g (i + 1) (acc + i) else acc in
    string_of_int (g 0 0))
