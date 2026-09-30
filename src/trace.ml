(* Hierarchical trace classes enabled through the LG_TRACE environment
   variable or the --trace flag.  Class names are dot-separated; enabling
   a class also enables its children (e.g. "compile" covers
   "compile.timing" and "compile.cache"), and an exact class enables
   itself only.  Legacy per-feature variables remain as aliases so
   existing scripts keep working:

     LG_COMPILE_TIMINGS=1       -> compile.timing
     LG_COMPILE_TIMINGS=details -> compile.timing.details
     LG_COMPILE_TIMINGS=debug   -> compile.timing.details
                                   (+ compile.timing.debug)
     LG_DUMP_ML=1               -> compile.dump
     LG_COMPILE_CACHE_DEBUG=1   -> compile.cache
*)

let parse_classes value =
  String.split_on_char ',' value
  |> List.filter_map (fun entry ->
         let entry = String.trim entry in
         if entry = "" then None else Some entry)

let env_classes =
  lazy
    (match Sys.getenv_opt "LG_TRACE" with
     | Some value -> parse_classes value
     | None -> [])

let cli_classes = ref []

let add_classes value = cli_classes := parse_classes value @ !cli_classes

let reset_cli_classes_for_testing () = cli_classes := []

let covers enabled cls =
  String.equal enabled cls
  || (String.length cls > String.length enabled
      && String.sub cls 0 (String.length enabled) = enabled
      && cls.[String.length enabled] = '.')

let enabled cls =
  let specified = Lazy.force env_classes @ !cli_classes in
  List.exists (fun entry -> covers entry cls) specified
  ||
  match cls with
  | "compile.timing" -> Sys.getenv_opt "LG_COMPILE_TIMINGS" = Some "1"
  | "compile.timing.details" -> (
      match Sys.getenv_opt "LG_COMPILE_TIMINGS" with
      | Some ("details" | "debug") -> true
      | _ -> false)
  | "compile.timing.debug" -> Sys.getenv_opt "LG_COMPILE_TIMINGS" = Some "debug"
  | "compile.dump" -> Sys.getenv_opt "LG_DUMP_ML" = Some "1"
  | "compile.cache" -> Sys.getenv_opt "LG_COMPILE_CACHE_DEBUG" = Some "1"
  | _ -> false

let enabled_any classes = List.exists enabled classes

let printf cls fmt =
  if enabled cls then
    Printf.ksprintf
      (fun message -> prerr_endline ("[trace " ^ cls ^ "] " ^ message))
      fmt
  else Printf.ksprintf (fun _ -> ()) fmt
