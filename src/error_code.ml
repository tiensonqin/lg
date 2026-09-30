(* Stable compiler diagnostic codes.

   Every diagnostic emitted through [Error.error] carries one of these codes.
   The code is part of the user-facing contract: it is stable across releases
   and documented in docs/errors/<CODE>.md. [lg --explain <CODE>] prints that
   documentation.

   Numbering:
     LG1xxx  front end (lexing, parsing)
     LG2xxx  semantic analysis and elaboration
     LG4xxx  OCaml back end
     LG5xxx  interactive / REPL
     LG9xxx  infrastructure *)

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

let all =
  [
    Lexing;
    Parsing;
    Semantic;
    Arity;
    Type_mismatch;
    Unresolved;
    Duplicate;
    Unsupported;
    Invalid_form;
    Interop;
    Destructure;
    Macro;
    Namespace;
    Protocol;
    Inference;
    Internal;
    Ocaml;
    Repl;
    Infrastructure;
  ]

let code = function
  | Lexing -> "LG1001"
  | Parsing -> "LG1002"
  | Semantic -> "LG2000"
  | Arity -> "LG2001"
  | Type_mismatch -> "LG2002"
  | Unresolved -> "LG2003"
  | Duplicate -> "LG2004"
  | Unsupported -> "LG2005"
  | Invalid_form -> "LG2006"
  | Interop -> "LG2007"
  | Destructure -> "LG2008"
  | Macro -> "LG2009"
  | Namespace -> "LG2010"
  | Protocol -> "LG2011"
  | Inference -> "LG2012"
  | Internal -> "LG2999"
  | Ocaml -> "LG4000"
  | Repl -> "LG5001"
  | Infrastructure -> "LG9000"

let name = function
  | Lexing -> "lexing"
  | Parsing -> "parsing"
  | Semantic -> "semantic"
  | Arity -> "arity"
  | Type_mismatch -> "type-mismatch"
  | Unresolved -> "unresolved"
  | Duplicate -> "duplicate"
  | Unsupported -> "unsupported"
  | Invalid_form -> "invalid-form"
  | Interop -> "interop"
  | Destructure -> "destructure"
  | Macro -> "macro"
  | Namespace -> "namespace"
  | Protocol -> "protocol"
  | Inference -> "inference"
  | Internal -> "internal"
  | Ocaml -> "ocaml"
  | Repl -> "repl"
  | Infrastructure -> "infrastructure"

let of_string text =
  let normalized = String.uppercase_ascii (String.trim text) in
  List.find_map
    (fun member -> if code member = normalized then Some member else None)
    all

let summary = function
  | Lexing -> "The reader could not tokenize the input."
  | Parsing -> "The reader produced a malformed form."
  | Semantic -> "The program was rejected during semantic analysis."
  | Arity -> "A call, binding, or special form received the wrong arguments."
  | Type_mismatch -> "A value's type does not match what the context requires."
  | Unresolved -> "A referenced name could not be resolved."
  | Duplicate -> "A name or member was defined more than once."
  | Unsupported -> "A language feature is not supported here."
  | Invalid_form -> "A form has invalid or malformed syntax."
  | Interop -> "A host interop boundary was used incorrectly."
  | Destructure -> "A destructuring pattern is invalid."
  | Macro -> "Macro expansion failed."
  | Namespace -> "A namespace declaration or require is invalid."
  | Protocol -> "A protocol declaration or implementation is invalid."
  | Inference -> "The type checker could not infer a required type."
  | Internal -> "The compiler hit an internal invariant; this is a bug."
  | Ocaml -> "The generated OCaml failed to typecheck."
  | Repl -> "An interactive form was rejected."
  | Infrastructure -> "The toolchain could not complete an operation."

let doc_path member = "docs/errors/" ^ code member ^ ".md"

let doc member =
  let wanted = doc_path member in
  List.assoc_opt wanted Error_docs.docs
