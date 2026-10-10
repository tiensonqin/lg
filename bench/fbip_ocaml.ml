let n = 5_000_000
let () =
  let t0 = Sys.time () in
  let v = ref Clj_core.Vec.empty in
  for i = 0 to n - 1 do v := Clj_core.Vec.conj !v i done;
  let t1 = Sys.time () in
  let b = Lg_rt.vb_new () in
  for i = 0 to n - 1 do Lg_rt.vb_push b i done;
  let v2 = Lg_rt.vb_freeze b in
  let t2 = Sys.time () in
  let s = Gc.quick_stat () in
  Printf.printf "persistent conj: %.3fs (len %d)\nbuilder+freeze: %.3fs (len %d)\nratio: %.1fx\nminor_words: %.0f minor_colls: %d\n"
    (t1 -. t0) (Clj_core.Vec.length !v) (t2 -. t1) (Clj_core.Vec.length v2)
    ((t1 -. t0) /. max (t2 -. t1) 1e-6)
    s.Gc.minor_words s.Gc.minor_collections
