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

for src in test/*.lg; do
  name=$(basename "$src" .lg)
  case "$name" in _*) continue;; esac
  out="test/$name.out"
  bin=".test-bin/$name"
  if ! "$LG" check "$src" >/dev/null 2>&1; then
    echo "FAIL(check) $name"
    fail=1; continue
  fi
  if ! "$LG" build "$src" -o "$bin" >/dev/null 2>&1; then
    echo "FAIL(build) $name"
    fail=1; continue
  fi
  if ! "$bin" > ".test-bin/$name.out" 2>&1; then
    echo "FAIL(run) $name"
    fail=1; continue
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
  name=$(basename "$src" .lg)
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
