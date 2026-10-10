(* baseline: identical loop shape, plain heap-allocated Clj_core.Vec *)
let rec spin n acc =
  if n = 0 then acc
  else
    let v = Clj_core.Vec.of_list [ n; n + 1; n + 2 ] in
    let m = Clj_core.Vec.reduce (fun a b -> a + b) 0 v in
    spin (n - 1) (acc + Clj_core.Vec.length v + m)
let () = print_int (spin 1_000_000 0); print_newline ()
