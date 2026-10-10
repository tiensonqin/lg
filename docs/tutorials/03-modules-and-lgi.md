# Modules and interfaces

Every `.lg` file is a module named by its `(ns name)` form. Modules
import each other with `:require`; an optional `.lgi` file next to the
source is its public interface.

## requires

```
(ns app
  (:require [qc :as q]
            [ocaml.List :as olist]))
```

`(:require [qc :as q])` pulls the `qc` module in and binds the `q`
alias; references are `q/gen-int`. Bare `(:require [qc])` binds the
alias `qc`. `ocaml.*` requires bind OCaml library functions — their
types are read from the installed `.cmi` signatures.

## .lgi — the export gate

When `foo.lgi` sits next to `foo.lg`, only the entries it lists are
visible to importers; everything else is private. The file is also the
documentation source — it carries signatures and docstrings:

```
;; foo.lgi
(def sum (fn [(list int)] int) :escapes [true]
  "Sum a list of ints.")
(defvariant (tree a)
  (leaf [v a])
  (node [l (tree a)] [r (tree a)]))
(macro measure (fn [any] unit)
  "(measure x) times an expression.")
(private helper)
```

- `(def n sig)` exports a value or function with signature `sig`
- `(defvariant ...)` exports a variant and its constructors
- `(macro n sig "doc")` documents a `defmacro` — macros are not values
- `(private n)` explicitly hides a def (unlisted defs are already
  private; use it for the record)
- `(extern-type n)` declares an opaque handle type

`lg lgi file.lg` regenerates a `.lgi` from the actual exports;
`lg lgi --check` fails when the interface has drifted from the code —
run it in CI. `.lgi` docstrings (or a docstring on the `def`/`defn`/
`defvariant` itself) feed `lg doc`.

## lg doc

`lg doc lib/*.lg --tutorials docs/tutorials -o docs/api` builds the
static API site: one page per module, cross-linked `ns/name` references
in docstrings, and this tutorial section.
