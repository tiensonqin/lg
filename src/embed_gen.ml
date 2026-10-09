(* Generates embedded_runtime.ml from runtime sources. Invoked by dune:
   ocaml embed_gen.ml <target> <lg_rt.ml> *)

let args =
  let a = Sys.argv in
  let i = ref 0 in
  Array.iteri (fun k s -> if Filename.basename s = "embed_gen.ml" then i := k) a;
  if !i + 1 >= Array.length a then Array.sub a 1 (Array.length a - 1)
  else Array.sub a (!i + 1) (Array.length a - !i - 1)

let read_all path =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  s

let () =
  let target = args.(0) in
  let rt = read_all args.(1) in
  let oc = open_out target in
  Printf.fprintf oc "let lg_rt_src = %S\n" rt;
  close_out oc
