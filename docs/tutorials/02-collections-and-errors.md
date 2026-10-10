# Collections and errors

How lg models data and failure — the two places it intentionally differs
from Clojure.

## Collections

Four persistent collection types, backed by clj-core:

- `[1 2 3]` — `(vec t)` persistent vector; `conj` appends
- `'(1 2)` — `(list t)` linked list; `cons`/`first`/`rest`
- `{:a 1 :b 2}` — `(map k v)` persistent map; `assoc`, `get`, `dissoc`
- `#{1 2}` — `(set t)` persistent set; `conj`, `disj`, `contains?`

Sequence operations are **lazy**: `map`, `filter`, `reverse`,
`distinct`, `interpose`, `take`, `drop`, `concat`, `mapcat` all return
`(seq t)`. Realize at a boundary with `vec`, `set`, `doall`, `dorun`,
or by consuming with `reduce`/`str`/`println`.

```
(map (fn [x] (* x x)) [1 2 3])        ; a lazy seq
(vec (map (fn [x] (* x x)) [1 2 3]))  ; [1 4 9]
```

## No nil — option types

lg has no `nil` value. `()` is the unit value (like OCaml `()`), and
absence is always `(option t)`:

- `(get {:a 1} :b)` returns `None`, `(get {:a 1} :a)` returns `Some 1`
- Destructure with `match`, `if-let`, or `or`:

```
(match (get m k)
  (Some v) (println v)
  None (println "missing"))
```

An `option` never silently becomes a number: `(+ 1 (get m k))` is a
compile-time type error (E101), not a runtime crash.

## Exceptions

For OCaml interop and truly exceptional paths there is
`try`/`catch`/`finally`/`throw`:

```
(try (list/find (fn [x] (= x 9)) [1])
     (catch e (println (exn-message e)))
     (finally (cleanup)))
```

`e` is an opaque `exn` handle; `exn-message` gives its string form and
`(throw e)` re-raises. OCaml exceptions from `:require [ocaml.*]`
bindings (e.g. `Not_found`) are caught the same way. Prefer `option`
for expected absence — exceptions are for the exceptional.
