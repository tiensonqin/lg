type t =
  | Default_receiver
  | Int_receiver
  | Float_receiver
  | Char_receiver
  | String_receiver
  | Symbol_receiver
  | Keyword_receiver
  | Bool_receiver
  | Unit_receiver
  | Nil_receiver
  | List_receiver
  | Vector_receiver
  | Set_receiver
  | Seq_receiver
  | Array_receiver
  | Ref_receiver
  | Tuple_receiver
  | Host_receiver of string
  | Record_receiver of Type_id.t

let default_type_variable = "__lg_protocol_default_receiver"

let compiler_marker_receiver_key marker =
  Types.compiler_marker_type_name marker

let of_type = function
  | Semantic_type.TVar name when name = default_type_variable ->
      Some Default_receiver
  | Semantic_type.TInt -> Some Int_receiver
  | TFloat -> Some Float_receiver
  | TChar -> Some Char_receiver
  | TString -> Some String_receiver
  | TRegex -> Some String_receiver
  | TSymbol -> Some Symbol_receiver
  | TKeyword -> Some Keyword_receiver
  | TBool -> Some Bool_receiver
  | TUnit -> Some Unit_receiver
  | TNil -> Some Nil_receiver
  | TList _ -> Some List_receiver
  | TVector _ -> Some Vector_receiver
  | TSet _ -> Some Set_receiver
  | TSeq _ -> Some Seq_receiver
  | TArray _ -> Some Array_receiver
  | TRef _ -> Some Ref_receiver
  | TTuple _ -> Some Tuple_receiver
  | TRecord fields when Types.is_homogeneous_record fields ->
      Some (Host_receiver "Lg_runtime.Runtime_map.t")
  | TCompiler marker -> Some (Host_receiver (compiler_marker_receiver_key marker))
  | TOcaml name | TOcaml_app (name, _) -> Some (Host_receiver name)
  | TNullable _ -> Some (Host_receiver "option")
  | TNamed_record record -> Some (Record_receiver record.type_id)
  | TFn _ | TOverloaded_fn _ -> Some (Host_receiver "fn")
  | TPoly_variant _ | TUnknown | TMeta _ | TMap_keys | TVar _ | TRecord _ | TConstraint _ ->
      None
