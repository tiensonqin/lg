# Golden compiler tests

Each case in `cases/` has a `.cljc` source file and a matching `.expected`
diagnostic or `ok` result. A case normally compiles against the standard
library; add `;; golden: bare` as its first line to compile without it.

To add a case, create both files and run the golden alias twice:

```sh
opam exec --switch=default -- dune build @test/golden/runtest --auto-promote
opam exec --switch=default -- dune build @test/golden/runtest
```

The first run promotes the generated `dune.inc`; the second run checks the
new case. To update an expected result, run:

```sh
opam exec --switch=default -- dune build @test/golden/runtest --auto-promote
```
