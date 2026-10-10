(* OxCaml implementation of the compiler-libs surface ocaml_sig needs.
   The mode-aware API differs from upstream in four places:

   - cmi_sign carries (signature * Mode.Staticity.const) — drop the
     staticity; signatures are runtime-irrelevant metadata for us.
   - Tarrow's first field is arrow_desc = (arg_label * alloc * alloc).
   - Type_variant carries variant_representation + unsafe_mode_crossing.
   - Cstr_tuple payloads are constructor_argument records (ca_type).

   dune copies this file to osig_shim.ml when %{ocaml_version} reports
   an +ox toolchain. *)

let cmi_signature (cmi : Cmi_format.cmi_infos) = fst cmi.Cmi_format.cmi_sign

(* normalized arrow label: the raw arg_label lives in different modules
   (and gains members) across toolchains — normalize at the seam. Ox adds
   Position ([%call_pos]); treat it as an optional label the caller may
   omit, matching its implicit-fill semantics. *)
type ocaml_lbl = ONo | OLbl of string | OOpt of string

let split_arrow (t : Types.type_expr) =
  match Types.get_desc t with
  | Types.Tarrow ((l, _, _), a, r, _) ->
    let l =
      match l with
      | Types.Nolabel -> ONo
      | Types.Labelled s -> OLbl s
      | Types.Optional s -> OOpt s
      | Types.Position s -> OOpt s
    in
    Some (l, a, r)
  | _ -> None

let variant_ctors (td : Types.type_declaration) =
  match td.Types.type_kind with
  | Types.Type_variant (cds, _, _) -> Some cds
  | _ -> None

let cstr_tuple (cd : Types.constructor_declaration) =
  match cd.Types.cd_args with
  | Types.Cstr_tuple ts -> Some (List.map (fun ca -> ca.Types.ca_type) ts)
  | _ -> None
