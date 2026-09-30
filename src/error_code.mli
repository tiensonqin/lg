(* Stable compiler diagnostic codes; see docs/errors/. *)

type t =
  | Lexing
  | Parsing
  | Semantic
  | Arity
  | Type_mismatch
  | Unresolved
  | Duplicate
  | Unsupported
  | Invalid_form
  | Interop
  | Destructure
  | Macro
  | Namespace
  | Protocol
  | Inference
  | Internal
  | Ocaml
  | Repl
  | Infrastructure

val all : t list
val code : t -> string
val name : t -> string
val of_string : string -> t option
val summary : t -> string
val doc_path : t -> string
val doc : t -> string option
