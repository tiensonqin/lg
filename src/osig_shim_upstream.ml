(* Upstream OCaml (5.x) implementation of the compiler-libs surface
   ocaml_sig needs. The OxCaml twin (osig_shim_ox.ml) adapts the same
   four operations to the mode-aware API; dune copies exactly one of
   them to osig_shim.ml by %{ocaml_version}. *)

let cmi_signature (cmi : Cmi_format.cmi_infos) = cmi.Cmi_format.cmi_sign

(* normalized arrow label: the raw arg_label lives in different modules
   (and gains members) across toolchains — normalize at the seam *)
type ocaml_lbl = ONo | OLbl of string | OOpt of string

let split_arrow (t : Types.type_expr) =
  match Types.get_desc t with
  | Types.Tarrow (l, a, r, _) ->
    let l =
      match l with
      | Asttypes.Nolabel -> ONo
      | Asttypes.Labelled s -> OLbl s
      | Asttypes.Optional s -> OOpt s
    in
    Some (l, a, r)
  | _ -> None

let variant_ctors (td : Types.type_declaration) =
  match td.Types.type_kind with
  | Types.Type_variant (cds, _) -> Some cds
  | _ -> None

let cstr_tuple (cd : Types.constructor_declaration) =
  match cd.Types.cd_args with
  | Types.Cstr_tuple ts -> Some ts
  | _ -> None

let record_lbls (td : Types.type_declaration) =
  match td.Types.type_kind with
  | Types.Type_record (lds, _) -> Some lds
  | _ -> None
