#!/usr/bin/env bash
# OxCaml end-to-end smoke: emit --backend=oxcaml, compile with the real
# OxCaml (flambda2) toolchain inside the `oxcaml` opam switch, run each
# binary and diff against the golden .out.
#
# Requires:
#   - an `oxcaml` opam switch (OCaml 5.2.0+ox):
#       opam switch create oxcaml ocaml-variants.5.2.0+ox \
#         --repositories=oxcaml=git+https://github.com/oxcaml/opam-repository.git
#   - dune, ocamlfind, and the native deps built under it. clj-core +
#     rrbvec need their melange/js_of_ocaml stanzas stripped for OxCaml
#     (see docs/design.md §OxCaml) plus two locality-mode fixes in
#     clj-core lib/{str,list}.ml.
#
# Run from the repo root: ./test/oxcaml_smoke.sh

set -e
cd "$(dirname "$0")/.."
eval "$(opam env --switch=oxcaml --set-switch)"

LG=./_build/default/bin/lg.exe
fail=0
for f in test/*.lg; do
  n=$(basename "$f" .lg)
  case "$n" in _*|mel*|wasm|ffi*|ffimod) continue;; esac
  extra=""
  case "$n" in props|qclib|testlib) extra="-I lib";; esac
  if ! "$LG" build "$f" -I lib --backend=oxcaml -o "/tmp/ox_$n" 2>/dev/null; then
    echo "BUILD-FAIL $n"; fail=1; continue
  fi
  if [ -f "test/$n.out" ]; then
    if ! diff -q <("/tmp/ox_$n" 2>/dev/null) "test/$n.out" >/dev/null; then
      echo "DIFF-FAIL $n"; fail=1; continue
    fi
  fi
  echo "ok $n"
done
exit $fail
