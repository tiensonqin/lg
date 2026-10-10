# Getting started

lg is a small Lisp that compiles to OCaml. Programs are checked by a
Hindley-Milner inferencer and emitted as plain OCaml source, so a build
needs only ocamlfind plus the clj-core/rrbvec packages.

## Install and first program

Build the compiler from source:

```
dune build bin/lg.exe
```

Write `hello.lg`:

```
(ns hello)

(println "hello, lg")
```

Check and run it:

```
lg check hello.lg
lg build hello.lg -o hello
./hello
```

`lg repl` starts a session that compiles each line to bytecode (fast —
incremental, ~85ms per line). `lg emit hello.lg` prints the generated
OCaml for inspection, and `lg build --byte` gives a quick dev binary.

## Language tour

- **Calls** are `(fn arg...)` lists: `(+ 1 2)`, `(println (str "n=" n))`.
- **Bindings**: `let` for locals, `def`/`defn` for module-level values
  and functions. `defn` takes an optional docstring:
  `(defn greet "Say hi." [name] (println (str "hi " name)))`.
- **Collections**: vectors `[1 2 3]`, lists `'(1 2)`, maps `{:a 1}`,
  sets `#{1 2}`. Sequence functions (`map`, `filter`, `reverse`, ...)
  return lazy `(seq t)`; realize with `vec`/`doall` at boundaries.
- **Control**: `if`, `cond`, `match` for destructuring; `do` sequences
  expressions. Loops are written as recursion or `mapv`/`reduce`.
- **Variants**: `(defvariant shape (circle [r float]) square)` defines
  a sum type; `match` dispatches on constructors.
- **Errors**: there is no `nil`. Absence is `(option t)` with
  `Some`/`None`; exceptions are `(try ... (catch e ...))` with
  `throw`/`exn-message`.
- **Macros**: `defmacro` is hygienic and multi-arity, just like
  `(defmacro m ([x] ...) ([x y] ...))`.
