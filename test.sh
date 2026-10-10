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
  if [ "$name" = "mel" ] || [ "$name" = "melio" ]; then
    if ! "$LG" build "$src" -I lib --backend=melange -o "$bin" >/dev/null 2>&1 || ! node "$bin.js" > ".test-bin/$name.out" 2>&1; then
      echo "FAIL(build/run) $name"
      fail=1; continue
    fi
  elif [ "$name" = "wasm" ]; then
    if ! command -v wasm_of_ocaml >/dev/null 2>&1; then
      echo "skip wasm (no wasm_of_ocaml)"
      continue
    fi
    if ! "$LG" build "$src" -I lib --backend=wasm -o "$bin" >/dev/null 2>&1 || ! node "$bin.js" > ".test-bin/$name.out" 2>&1; then
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
  elif [ -f "should_fail/$name.err" ] && ! grep -Eq "$(cat "should_fail/$name.err")" ".test-bin/$name.err"; then
    # must fail for the documented reason, not any error
    echo "FAIL(error-class) $name: stderr does not match should_fail/$name.err"
    head -3 ".test-bin/$name.err"
    fail=1
  else
    echo "ok(negative) $name"
  fi
done

# examples/: every example must build and run green (no .out diff —
# several print timings or read input files)
for name in hello features csv json jsonp util stopwatch eiodemo; do
  src="examples/$name.lg"
  [ -e "$src" ] || continue
  if ! "$LG" build "$src" -I lib -I examples -o ".test-bin/ex_$name" >/dev/null 2>&1; then
    echo "FAIL(example-build) $name"
    fail=1; continue
  fi
  if ! ".test-bin/ex_$name" >/dev/null 2>&1; then
    echo "FAIL(example-run) $name"
    fail=1; continue
  fi
  echo "ok example-$name"
done
# multi-file examples (deps resolve inside their own directory)
if "$LG" build examples/impdemo/main.lg -I lib -I examples/impdemo -o .test-bin/ex_impdemo >/dev/null 2>&1 \
   && .test-bin/ex_impdemo >/dev/null 2>&1; then
  echo "ok example-impdemo"
else
  echo "FAIL(example) impdemo"; fail=1
fi
if "$LG" build examples/wfreq/wfreq.lg -I lib -I examples/wfreq -o .test-bin/ex_wfreq >/dev/null 2>&1 \
   && .test-bin/ex_wfreq examples/wfreq/wfreq.lg >/dev/null 2>&1; then
  echo "ok example-wfreq"
else
  echo "FAIL(example) wfreq"; fail=1
fi

# reader round-trip: parse -> print -> parse -> form_eq over every .lg
RT=./_build/default/test/roundtrip.exe
if [ -x "$RT" ]; then
  "$RT" test/*.lg test/*.cljc lib/*.lg examples/*.lg examples/*/*.lg \
    || fail=1
else
  echo "skip roundtrip (not built)"
fi

# oxcaml backend: emit must carry mode annotations
if "$LG" emit test/oxcaml.lg --backend=oxcaml -o .test-bin/oxcaml.ml >/dev/null 2>&1 \
   && grep -q '@ local\|local_\|unique_\|stack_' .test-bin/oxcaml.ml; then
  echo "ok oxcaml-emit"
else
  echo "FAIL(oxcaml-emit)"
  fail=1
fi

exit $fail
