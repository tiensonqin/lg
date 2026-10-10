(* OCaml twin of the ox-emit: local vec + stack_ literal + reduce_local *)
let rec spin n acc =
  if n = 0 then acc
  else
    let v @ local = Clj_core.Vec.of_list_local (stack_ [ n; n + 1; n + 2 ]) in
    let m = Clj_core.Vec.reduce_local (fun a b -> a + b) 0 v in
    spin (n - 1) (acc + Clj_core.Vec.count v + m)
let () =
  let s0 = Gc.quick_stat () in
  let t0 = Sys.time () in
  let r = spin 1_000_000 0 in
  let t1 = Sys.time () in
  let s1 = Gc.quick_stat () in
  Printf.printf "%d\ntime %.3fs  minor_words %.0f  minor_colls %d\n" r
    (t1 -. t0) (s1.Gc.minor_words -. s0.Gc.minor_words)
    (s1.Gc.minor_collections - s0.Gc.minor_collections)
