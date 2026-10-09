#!/bin/sh
# lg test runner: check -> build -> run -> diff against test/*.out.
# should_fail/*.lg must fail `lg check` (negative tests).
set -u
cd "$(dirname "$0")"
# needs the 5.5.0 switch for clj_core/rrbvec when building emitted OCaml
command -v opam >/dev/null 2>&1 && eval $(opam env --switch=5.5.0 --set-switch) >/dev/null 2>&1
LG=./_build/default/bin/lg.exe
mkdir -p .test-bin
fail=0

# ffi.lg links a C stub via LG_EXTRA_LINK (like a real OCaml-runtime binding)
if [ -f test/ffi_stub.c ]; then
  ocamlfind ocamlc -c test/ffi_stub.c -o .test-bin/ffi_stub.o 2>/dev/null || true
fi

for src in test/*.lg test/*.cljc; do
  [ -e "$src" ] || continue
  name=$(basename "$src"); name=${name%.*}
  case "$name" in _*) continue;; esac
  out="test/$name.out"
  bin=".test-bin/$name"
  link_extra=""
  case "$name" in ffi*) [ -f .test-bin/ffi_stub.o ] && link_extra=".test-bin/ffi_stub.o";; esac
  if ! "$LG" check "$src" -I lib >/dev/null 2>&1; then
    echo "FAIL(check) $name"
    fail=1; continue
  fi
  if [ "$name" = "mel" ]; then
    if ! "$LG" build "$src" -I lib --backend=melange -o "$bin" >/dev/null 2>&1 || ! node "$bin.js" > ".test-bin/$name.out" 2>&1; then
      echo "FAIL(build/run) $name"
      fail=1; continue
    fi
  else
    if ! LG_EXTRA_LINK="$link_extra" "$LG" build "$src" -I lib -o "$bin" >/dev/null 2>&1; then
      echo "FAIL(build) $name"
      fail=1; continue
    fi
    if ! "$bin" > ".test-bin/$name.out" 2>&1; then
      echo "FAIL(run) $name"
      fail=1; continue
    fi
  fi
  if ! diff -u "$out" ".test-bin/$name.out" > /dev/null 2>&1; then
    echo "FAIL(diff) $name"
    diff -u "$out" ".test-bin/$name.out" | head -20
    fail=1; continue
  fi
  echo "ok $name"
done

for src in should_fail/*.lg; do
  [ -e "$src" ] || continue
  name=$(basename "$src"); name=${name%.*}
  case "$name" in _*) continue;; esac
  extra=""
  case "$name" in strict*) extra="--strict";; esac
  if "$LG" check "$src" $extra > ".test-bin/$name.err" 2>&1; then
    echo "FAIL(expected-error) $name: typechecked but should not"
    fail=1
  else
    echo "ok(negative) $name"
  fi
done

# oxcaml backend: emit must carry mode annotations
if "$LG" emit test/oxcaml.lg --backend=oxcaml -o .test-bin/oxcaml.ml >/dev/null 2>&1 \
   && grep -q 'local_\|unique_\|stack_' .test-bin/oxcaml.ml; then
  echo "ok oxcaml-emit"
else
  echo "FAIL(oxcaml-emit)"
  fail=1
fi

exit $fail
