# lg

A *tiny* language that emits **OCaml**.

## Features

- static inference
- `defvariant` + `match`
- FBIP [builders](https://github.com/tiensonqin/lg2)

``` lg
(defn fib [n]
  (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2)))))
```

Tail *em* and **strong** and `code`.
