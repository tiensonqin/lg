# Foreign function interface

Declare a foreign function with `ffi`, then call it like an ordinary lg
function — the binding is a first-class, statically typed value.

```clojure
(ffi name [argument-types] result-type {selector})
```

## `:ocaml` — OCaml runtime stubs

Emits a typed OCaml `external` declaration. For C stubs written against
the OCaml runtime API; link the object through your build (see
`LG_EXTRA_LINK` below).

```clojure
(ffi cpu-time [] :float {:ocaml "caml_sys_time"})
(cpu-time)   ;; => float
```

At most five arguments (`[]` emits `unit -> ret`). No `:library` option —
the stub is linked statically like any OCaml `external`.

## `:native` — dynamic C symbols via ctypes

```clojure
(ffi c-abs [:int] :int {:native "abs"})
(ffi c-strlen [:string] :int {:native "strlen"})
(ffi probe [:int] :int {:native "probe" :library "./libx.so"})
```

Without `:library` the symbol is resolved in the current process image;
with it, `Dl.dlopen` loads the shared library. `lg build` adds
`ctypes.foreign` to the package list automatically when any module in
the program uses `:native`.

| lg type | C ABI |
| --- | --- |
| `:int` | `int` |
| `:float` | `double` |
| `:bool` | `_Bool` |
| `:char` | `char` |
| `:string` | NUL-terminated `char *` (input only) |
| `:unit` | `void` (result only) |
| `:option<string>` | nullable `char *` → `string option` |
| extern-type | `void *` handle |
| `:option<extern>` | nullable `void *` → `extern option` |

## `extern-type` — opaque handles

```clojure
(extern-type counter)
(ffi make-counter [:int] :counter {:ocaml "lg_counter_new"})
(ffi read-counter [:counter] :int {:ocaml "lg_counter_read"})
```

Each `extern-type` is a distinct nominal type; only same-name types
unify. In `:native` bindings it maps to `void *`; in `:ocaml` bindings to
an abstract type emitted in the module (`type counter`).

## Rules

- Signatures must be statically closed — no type variables.
- `any` cannot cross the boundary (dyn is an internal repr).
- `:option` is supported for `:ocaml` (any type) and for `:native` on
  `:string`/extern handles (NULL ⇄ `None`).
- `:fn<...>` callback signatures and the `:js` selector (Melange) are
  not yet implemented.
- `ffi` declarations participate in the module system normally: they
  can be required cross-module, re-exported through `.lgi`
  (`(ffi name (fn [...] ret))`), and marked `^{:implicit T}` to serve as
  implicit dictionaries.

## Linking C stubs

`lg build` accepts extra link objects via `LG_EXTRA_LINK`:

```sh
ocamlfind ocamlc -c my_stub.c -o my_stub.o
LG_EXTRA_LINK=my_stub.o lg build app.lg -o app
```

See `test/ffi.lg` + `test/ffi_stub.c` for a runnable example.
