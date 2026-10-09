(* Typed AST: produced by analysis + HM inference, consumed by the mode
   inference pass and the OCaml emitter. *)

open Syntax
open Typ

type mode = Local | Owned | Shared

let string_of_mode = function Local -> "local" | Owned -> "owned" | Shared -> "shared"

type binder = {
  bname : string;
  bid : int;
  mutable bty : ty;
  mutable bmode : mode;      (* inferred later by Modes *)
  mutable bused : int;       (* use count; set by Modes *)
  mutable blit : bool;       (* bound init was a fresh collection literal *)
}

type func = {
  fname : string option;
  fself : binder option;      (* named fn bound to itself for recursion *)
  params : binder list;
  variadic : binder option;  (* [& rest] *)
  body : expr;
  mutable fescapes : bool;   (* set by Modes: does this fn escape its region *)
}

and expr = {
  loc : loc;
  mutable ety : ty;
  mutable emode : mode;      (* allocation-site mode; Shared until Modes runs *)
  desc : edesc;
}

and edesc =
  | EInt of int
  | EFloat of float
  | EBool of bool
  | EChar of char
  | EStr of string
  | EKeyword of string
  | ESymbol of string
  | ENil
  | ELocal of binder
  | EGlobal of string * string * string  (* ocaml module path, name, lg2 name *)
  | EBuiltin of string                    (* resolved builtin call *)
  | EFun of func
  | ECall of expr * expr list
  | EIf of expr * expr * expr
  | EDo of expr list
  | ELet of (binder * expr) list * expr
  | ETuple of expr list
  | EVecLit of expr list
  | EListLit of expr list
  | EMapLit of (expr * expr) list
  | ESetLit of expr list
  | EMatchOpt of expr * binder * expr * expr  (* if-let/when-let: match opt with Some b -> t | None -> e *)
  | EUnbox of expr * ty      (* ^T on an any-typed value: runtime-checked unbox *)
  | EUnboxOpt of expr * ty   (* ^(option T) on an any-option: unbox inside *)
  | EOpt of expr option                     (* (Some e) / None *)
  | EBox of expr                            (* concrete expr widened to `any`: deep-box at emit *)
  | EDynVec of expr * binder * expr * expr (* match on `any`: DVec b -> t | _ -> e *)
  | EDynMap of expr * binder * expr * expr (* match on `any`: DMap b -> t | _ -> e *)
  | EVariant of expr * string * binder list * expr * expr
    (* match se with Mod.Ctor (b..) -> t | _ -> e *)

let binder_id = ref 0
let fresh_binder name = incr binder_id; { bname = name; bid = !binder_id; bty = TUnit; bmode = Shared; bused = 0; blit = false }

let is_lit e =
  match e.desc with
  | EVecLit _ | EListLit _ | EMapLit _ | ESetLit _ | ETuple _ -> true
  | _ -> false

let mk loc ty desc = { loc; ety = ty; emode = Shared; desc }

(* A top-level definition in a module. *)
type topdef = {
  tname : string;
  tloc : loc;
  mutable tsch : scheme;
  texpr : expr;
  tis_fn : bool;
  mutable tmode : mode;
  mutable timplicit : ty option;  (* ^{implicit T} on the def name *)
}

(* FFI selector: OCaml `external` stub, ctypes dynamic symbol, or
   a JavaScript binding (melange emit). *)
type js_kind = JCall | JNew | JSend | JGet | JSet
type js_ret = JDirect | JUndefined | JNull | JNullable
type js_spec = {
  jsym : string;
  jkind : js_kind;
  jmodule : string option;
  jscope : string list;
  jret : js_ret;
}
type ffi_sel = FOcaml of string | FNative of string | FJs of js_spec

(* A top-level module item, in source order. *)
type top =
  | TDef of topdef
  | TExtern of loc * string  (* (extern-type name) — opaque handle type *)
  | TFfi of loc * string * ty list * ty * ffi_sel * string option
    (* (ffi name [args] ret {selector [:library path]}) *)
  | TVariant of loc * string * ty list * (string * (string * ty) list) list
    (* (defvariant (name params...) (ctor [f ty]...) ...) — ty params are
       shared TVar instances across all ctor field types *)

type modl = {
  mname : string;          (* lg2 namespace, e.g. "foo.util" *)
  ocaml_name : string;     (* emitted OCaml module, e.g. "Foo_util" *)
  mpath : string;
  mutable requires : (string * string) list;  (* alias -> lg2 ns *)
  mutable tops : top list;
  mutable effects : expr list;                (* top-level non-def forms, run at init *)
  iface_only : bool;                          (* satisfied by an .lgi with no .lg *)
  mutable uses_ctypes : bool;                 (* any :native ffi declaration *)
}

(* chainable update ops for FBIP builder lowering (emit.ml) *)
type cop =
  | CPush of expr | CSet of expr * expr | CUpd of expr * expr | CPop | CExt of expr
  | CPut of expr * expr | CDrop of expr | CUpdMap of expr * expr | CPair of expr | CMExt of expr
  | CAdd of expr | CDel of expr | CSExt of expr
