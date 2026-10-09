(* lg.edn package manifest: {:name "proj" :deps {lib {:path "../lib"}
   core {:git "url" :sha "abc"}}}. Parsed with the lg reader — edn maps
   are lg maps. Git deps fetch into <proj>/.lg/deps/<name> and are
   recorded in lg.lock. *)

open Syntax

type dep = DPath of string | DGit of string * string option

let manifest_path dir = Filename.concat dir "lg.edn"

(* find lg.edn walking up from dir *)
let find_manifest start =
  let rec up d =
    let p = manifest_path d in
    if Sys.file_exists p then Some (d, p)
    else
      let parent = Filename.dirname d in
      if parent = d then None else up parent
  in
  up (Unix.realpath start)

let kv_get k kvs =
  List.find_map
    (fun (kf, v) -> match kf with Atom (_, Keyword kk) when kk = k -> Some v | _ -> None)
    kvs

(* form -> (string * dep) option *)
let dep_of_pair = function
  | Atom (_, Symbol name), Map (_, kvs) ->
    let kw k = kv_get k kvs in
    (match kw "path", kw "git" with
     | Some (Atom (_, Str p)), _ -> Some (name, DPath p)
     | _, Some (Atom (_, Str u)) ->
       let sha = match kw "sha" with Some (Atom (_, Str s)) -> Some s | _ -> None in
       Some (name, DGit (u, sha))
     | _ -> None)
  | _ -> None

let load_manifest file =
  let src =
    let ic = open_in file in
    let t = really_input_string ic (in_channel_length ic) in
    close_in ic; t
  in
  match Reader.read_file ~file src with
  | [ Map (_, kvs) ] ->
    let name = match kv_get "name" kvs with
      | Some (Atom (_, Str s)) -> s | _ -> Filename.dirname file |> Filename.basename in
    let deps =
      match kv_get "deps" kvs with
      | Some (Map (_, dkvs)) -> List.filter_map dep_of_pair dkvs
      | _ -> []
    in
    (name, deps)
  | _ -> ("", [])

(* resolve a dep to a directory usable as -I root *)
let resolve proj_dir (name, dep) =
  match dep with
  | DPath p -> if Filename.is_relative p then Filename.concat proj_dir p else p
  | DGit (url, sha) ->
    let dest = Filename.concat (Filename.concat proj_dir ".lg/deps") name in
    if not (Sys.file_exists (Filename.concat dest ".git")) then (
      ignore (Sys.command (Printf.sprintf "mkdir -p %s" (Filename.quote (Filename.dirname dest))));
      let rc = Sys.command (Printf.sprintf "git clone --quiet %s %s" (Filename.quote url) (Filename.quote dest)) in
      if rc <> 0 then failwith ("git clone failed for " ^ name));
    (match sha with
     | Some s ->
       ignore (Sys.command (Printf.sprintf "cd %s && git checkout --quiet %s" (Filename.quote dest) (Filename.quote s)))
     | None -> ());
    dest

(* dep roots for a manifest located in proj_dir; fetch git deps *)
let dep_roots proj_dir deps =
  List.map (fun d -> resolve proj_dir d) deps

(* write lg.lock lines for git deps: name url resolved-sha *)
let write_lock proj_dir deps =
  let lines =
    List.filter_map
      (fun (name, dep) ->
        match dep with
        | DPath _ -> None
        | DGit (url, _) ->
          let dest = Filename.concat (Filename.concat proj_dir ".lg/deps") name in
          let ic = Unix.open_process_in (Printf.sprintf "cd %s && git rev-parse HEAD" (Filename.quote dest)) in
          let sha = try input_line ic with End_of_file -> "" in
          ignore (Unix.close_process_in ic);
          Some (Printf.sprintf "%s %s %s" name url sha))
      deps
  in
  let oc = open_out (Filename.concat proj_dir "lg.lock") in
  List.iter (fun l -> output_string oc (l ^ "\n")) lines;
  close_out oc

(* add manifest dep roots to roots list *)
let roots_with_manifest roots file =
  match find_manifest (Filename.dirname file) with
  | None -> roots
  | Some (proj_dir, mfile) ->
    let _, deps = load_manifest mfile in
    roots @ dep_roots proj_dir deps
