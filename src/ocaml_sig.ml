(* Direct interop with installed OCaml libraries.

   `(:require [ocaml.Mod :as m])` aliases an OCaml module; `m/f` then
   resolves `f`'s type from the module's .cmi via compiler-libs — real
   signatures, not user annotations. `(:require [ocaml.pkg/name])`
   declares an ocamlfind package: its include dirs (via `ocamlfind
   query -r -format %d`) are searched for cmis and the package is added
   to the link line (-package/-linkpkg).

   Labeled/optional OCaml parameters are written as trailing
   keyword/value pairs: `(m/f x :lbl v)` emits `Mod.f ~lbl:v x`.
   Type constructors the cmi signature uses but lg cannot express
   (abstract types, GADTs, objects) are E102 compile errors — no
   silent `any`. *)

open Typ

type ocaml_lbl = ONo | OLbl of string | OOpt of string

(* alias -> OCaml module path ("String", "Eio.Fiber", "Unix") *)
let aliases : (string, string) Hashtbl.t = Hashtbl.create 17

(* ocamlfind package declarations from ocaml.pkg/* specs *)
let packages : string list ref = ref []

(* directories searched for cmi files: stdlib + ocaml.pkg query dirs *)
let cmi_dirs : string list ref = ref []

let run_lines cmd =
  let ic = Unix.open_process_in cmd in
  let rec go acc =
    match input_line ic with
    | s -> go (s :: acc)
    | exception End_of_file -> close_in ic; List.rev acc
  in
  go []

let init () =
  if !cmi_dirs = [] then
    let stdlib =
      match run_lines "ocamlc -where" with
      | d :: _ -> String.trim d
      | [] -> "/usr/lib/ocaml"
    in
    cmi_dirs := [ stdlib ]

let add_package pkg =
  init ();
  if not (List.mem pkg !packages) then begin
    packages := pkg :: !packages;
    (* recursive include dirs so wrapped/sub libraries resolve *)
    let ds =
      run_lines
        (Printf.sprintf "ocamlfind query -r -format '%%d' %s 2>/dev/null" pkg)
    in
    cmi_dirs := !cmi_dirs @ List.map String.trim ds
  end

(* Eio.Fiber -> search dirs for fiber.cmi / eio__Fiber.cmi / eio.Fiber.cmi *)
let cmi_candidates modpath =
  let last =
    match String.rindex_opt modpath '.' with
    | Some i -> String.sub modpath (i + 1) (String.length modpath - i - 1)
    | None -> modpath
  in
  let flat = String.lowercase_ascii (String.map (fun c -> if c = '.' then '_' else c) modpath) in
  [ String.lowercase_ascii last ^ ".cmi"; flat ^ ".cmi";
    String.map (fun c -> if c = '.' then '/' else c) (String.lowercase_ascii modpath) ^ ".cmi";
    flat ^ ".cmi" ]

let find_cmi modpath =
  init ();
  let rec search dirs =
    match dirs with
    | [] -> None
    | d :: tl ->
      (match
         List.find_map
           (fun c -> let p = Filename.concat d c in if Sys.file_exists p then Some p else None)
           (cmi_candidates modpath)
       with
       | Some p -> Some p
       | None ->
         (* wrapped packages: Eio.Fiber may live in <dir>/eio/fiber.cmi *)
         (match String.index_opt modpath '.' with
          | Some i ->
            let pkg = String.lowercase_ascii (String.sub modpath 0 i) in
            let rest = String.sub modpath (i + 1) (String.length modpath - i - 1) in
            let p = Filename.concat (Filename.concat d pkg)
                      (String.lowercase_ascii rest ^ ".cmi") in
            if Sys.file_exists p then Some p else search tl
          | None -> search tl))
  in
  search !cmi_dirs

let sig_cache : (string, Types.signature_item list) Hashtbl.t = Hashtbl.create 17

let signature_of modpath =
  match Hashtbl.find_opt sig_cache modpath with
  | Some s -> Some s
  | None ->
    (match find_cmi modpath with
     | None -> None
     | Some file ->
       let cmi = Cmi_format.read_cmi file in
       Hashtbl.replace sig_cache modpath cmi.Cmi_format.cmi_sign;
       Some cmi.Cmi_format.cmi_sign)

(* Types.type_expr -> (param tys, labels, ret ty) + lg conversion *)
exception Unsupported of string

(* one var table per signature query: occurrences of the same 'a share a
   fresh flexible lg var so ('a -> 'a) instantiates correctly *)
let var_tbl : (int, tvar) Hashtbl.t = Hashtbl.create 7

let rec ty_of_te te : ty =
  match Types.get_desc te with
  | Types.Tarrow (_, a, r, _) -> TFun ([ ty_of_te a ], ty_of_te r)
  | Types.Ttuple ts -> TTuple (List.map (fun (_, t) -> ty_of_te t) ts)
  | Types.Tlink t | Types.Tsubst (t, _) -> ty_of_te t
  | Types.Tvar _ ->
    let id = Types.get_id te in
    (match Hashtbl.find_opt var_tbl id with
     | Some v -> TVar v
     | None ->
       let v = Typ.fresh_var () in
       (match v with
        | TVar tv -> Hashtbl.replace var_tbl id tv
        | _ -> ());
       v)
  | Types.Tpoly (t, _) -> ty_of_te t
  | Types.Tconstr (p, args, _) ->
    let n = Path.name p in
    let base =
      match List.rev (String.split_on_char '.' n) with
      | b :: _ -> b
      | [] -> n
    in
    (match base, args with
     | "int", [] -> TInt
     | "float", [] -> TFloat
     | "bool", [] -> TBool
     | "string", [] -> TString
     | "char", [] -> TChar
     | "unit", [] -> TUnit
     | "bytes", [] -> TString
     | "exn", [] -> TString
     | "list", [ a ] -> TList (ty_of_te a)
     | "option", [ a ] -> TOption (ty_of_te a)
     | "array", [ a ] -> TList (ty_of_te a)
     | "seq", [ a ] -> TSeq (ty_of_te a)
     | "result", [ o; _ ] -> TOption (ty_of_te o)
     | "ref", [ a ] -> TAtom (ty_of_te a)
     | _ -> raise (Unsupported n))
  | _ -> raise (Unsupported "type form")

(* decompose a value's type into positional/labeled params + result *)
let decompose te : (ty list) * ocaml_lbl list * ty =
  let rec go ps ls t =
    match Types.get_desc t with
    | Types.Tarrow (lbl, a, r, _) ->
      let l =
        match lbl with
        | Asttypes.Nolabel -> ONo
        | Asttypes.Labelled s -> OLbl s
        | Asttypes.Optional s -> OOpt s
      in
      go (ps @ [ ty_of_te a ]) (ls @ [ l ]) r
    | Types.Tlink t | Types.Tsubst (t, _) -> go ps ls t
    | _ -> (ps, ls, ty_of_te t)
  in
  go [] [] te

(* look up `name` in modpath's signature: either a value or a variant
   constructor. Returns (param tys, labels, result ty, is_ctor). *)
let lookup modpath name : (ty list * ocaml_lbl list * ty * bool) option =
  match signature_of modpath with
  | None -> None
  | Some items ->
    let rec find = function
      | [] -> None
      | Types.Sig_value (id, vd, _) :: tl ->
        if Ident.name id = name then begin
          let ps, ls, r = decompose vd.Types.val_type in
          Some (ps, ls, r, false)
        end else find tl
      | Types.Sig_type (tid, td, _, _) :: tl ->
        (match td.Types.type_kind with
         | Types.Type_variant (cds, _) ->
           (match
              List.find_opt
                (fun cd -> Ident.name cd.Types.cd_id = name)
                cds
            with
            | Some cd ->
              (match cd.Types.cd_args with
               | Types.Cstr_tuple ts ->
                 let rt =
                   match td.Types.type_manifest with
                   | Some m -> (try ty_of_te m with Unsupported _ -> TCon (Ident.name tid, []))
                   | None -> TCon (Ident.name tid, [])
                 in
                 Some (List.map ty_of_te ts, List.map (fun _ -> ONo) ts, rt, true)
               | Types.Cstr_record _ -> find tl)
            | None -> find tl)
         | _ -> find tl)
      | _ :: tl -> find tl
    in
    find items
