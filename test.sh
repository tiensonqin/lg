#!/bin/sh
# lg test runner: check -> build -> run -> diff against test/*.out.
# should_fail/*.lg must fail `lg check` (negative tests).
set -u
cd "$(dirname "$0")"
# needs the 5.5.0 switch for clj_core/rrbvec when building emitted OCaml
command -v opam >/dev/null 2>&1 && eval $(opam env --switch=5.5.0 --set-switch) >/dev/null 2>&1
LG=./_build/default/bin/lg.exe
mkdir -p .test-bin .test-bin/qcfuzz.d
fail=0
# test/ executables are not in the root @default alias; build them plus
# lg.exe — a binary left in _build by a different switch silently reads
# the wrong cmi family (toolchain-bound format), so always refresh it.
dune build bin/lg.exe test/roundtrip.exe 2>/dev/null || true

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
for name in hello features csv json jsonp util stopwatch eiodemo eioecho; do
  src="examples/$name.lg"
  [ -e "$src" ] || continue
  if ! "$LG" build "$src" -I lib -I examples -o ".test-bin/ex_$name" >/dev/null 2>&1; then
    echo "FAIL(example-build) $name"
    fail=1; continue
  fi
  # eioecho self-terminates (its client fiber exits the process); the
  # timeout guard keeps a networking regression from hanging the suite.
  if ! timeout 30 ".test-bin/ex_$name" >/dev/null 2>&1; then
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

# markdown-lite dogfood: render the sample doc, diff the html golden
if "$LG" build examples/markdown.lg -I lib -I examples -o .test-bin/ex_markdown >/dev/null 2>&1 \
   && .test-bin/ex_markdown examples/markdown.md >/dev/null 2>&1 \
   && diff -u test/markdown.golden.html examples/markdown.html > /dev/null 2>&1; then
  echo "ok example-markdown"
else
  echo "FAIL(example) markdown"
  diff -u test/markdown.golden.html examples/markdown.html | head -20
  fail=1
fi

# compat corpus: frozen v1 programs — add-only, must stay green forever
for src in test/compat/*.lg; do
  [ -e "$src" ] || continue
  name=$(basename "$src"); name=${name%.*}
  if ! "$LG" build "$src" -I lib -o ".test-bin/c_$name" >/dev/null 2>&1; then
    echo "FAIL(compat-build) $name"; fail=1; continue
  fi
  if ! ".test-bin/c_$name" > ".test-bin/c_$name.out" 2>&1; then
    echo "FAIL(compat-run) $name"; fail=1; continue
  fi
  if ! diff -u "test/compat/$name.out" ".test-bin/c_$name.out" > /dev/null 2>&1; then
    echo "FAIL(compat-diff) $name"
    diff -u "test/compat/$name.out" ".test-bin/c_$name.out" | head -10
    fail=1; continue
  fi
  echo "ok compat-$name"
done

# byte/native parity: the semantic core must produce byte-identical
# output under ocamlc (--byte) and ocamlopt
for name in core builtins destructure dyn hof match polydyn; do
  src="test/$name.lg"; [ -e "$src" ] || continue
  if ! "$LG" build "$src" -I lib --byte -o ".test-bin/b_$name" >/dev/null 2>&1; then
    echo "FAIL(byte-build) $name"; fail=1; continue
  fi
  if ! ".test-bin/b_$name" > ".test-bin/b_$name.out" 2>&1; then
    echo "FAIL(byte-run) $name"; fail=1; continue
  fi
  if ! diff -u "test/$name.out" ".test-bin/b_$name.out" > /dev/null 2>&1; then
    echo "FAIL(byte-diff) $name"
    diff -u "test/$name.out" ".test-bin/b_$name.out" | head -10
    fail=1; continue
  fi
  echo "ok byte-$name"
done

# emit snapshots: test/$name.emit.ml is the checked-in `lg emit` output;
# any codegen drift on those files fails the diff
for snap in test/*.emit.ml; do
  [ -e "$snap" ] || continue
  name=$(basename "$snap" .emit.ml)
  if ! "$LG" emit "test/$name.lg" -I lib -o ".test-bin/$name.emit.ml" >/dev/null 2>&1; then
    echo "FAIL(snapshot-emit) $name"; fail=1; continue
  fi
  if ! diff -u "$snap" ".test-bin/$name.emit.ml" > /dev/null 2>&1; then
    echo "FAIL(snapshot-diff) $name"
    diff -u "$snap" ".test-bin/$name.emit.ml" | head -15
    fail=1; continue
  fi
  echo "ok snapshot-$name"
done

# reader round-trip: parse -> print -> parse -> form_eq over every .lg
RT=./_build/default/test/roundtrip.exe
if [ -x "$RT" ]; then
  "$RT" test/*.lg test/*.cljc lib/*.lg examples/*.lg examples/*/*.lg \
    || fail=1
else
  echo "skip roundtrip (not built)"
fi

# fmt fidelity: `lg fmt` on copies of the whole corpus must (a) re-parse
# to the same forms (`--same`), (b) be a fixed point (second fmt reports
# "unchanged"), and (c) preserve every ';' occurrence (comments may move
# but never drop).
if [ -x "$RT" ]; then
  FMTD=.test-bin/fmt-corpus
  rm -rf "$FMTD"
  mkdir -p "$FMTD/test" "$FMTD/lib" "$FMTD/examples"
  cp test/*.lg test/*.cljc "$FMTD/test/" 2>/dev/null
  cp lib/*.lg "$FMTD/lib/" 2>/dev/null
  cp -R examples/ "$FMTD/examples/" 2>/dev/null
  fmtbad=0; pairs=""
  for f in "$FMTD"/test/*.lg "$FMTD"/test/*.cljc "$FMTD"/lib/*.lg \
           "$FMTD"/examples/*.lg "$FMTD"/examples/*/*.lg; do
    [ -e "$f" ] || continue
    rel=${f#$FMTD/}
    if ! "$LG" fmt "$f" >/dev/null 2>&1; then
      echo "FAIL(fmt) $rel"; fmtbad=1; continue
    fi
    if ! "$LG" fmt "$f" 2>/dev/null | grep -q 'unchanged'; then
      echo "FAIL(fmt-idempotent) $rel"; fmtbad=1
    fi
    if [ "$(grep -o ';' "$rel" | wc -l)" != "$(grep -o ';' "$f" | wc -l)" ]; then
      echo "FAIL(fmt-comments-dropped) $rel"; fmtbad=1
    fi
    pairs="$pairs $rel $f"
  done
  # shellcheck disable=SC2086 # intentional word-splitting of file pairs
  if [ $fmtbad = 0 ] && "$RT" --same $pairs >/dev/null 2>&1; then
    nfmt=$(echo "$FMTD"/test/*.lg "$FMTD"/test/*.cljc "$FMTD"/lib/*.lg \
               "$FMTD"/examples/*.lg "$FMTD"/examples/*/*.lg | wc -w | tr -d ' ')
    echo "ok fmt-fidelity ($nfmt files)"
  else
    "$RT" --same $pairs 2>&1 | grep -v '^ok' | head -10
    [ $fmtbad = 0 ] || true
    echo "FAIL(fmt-fidelity)"; fail=1
  fi

  # fmt golden: the comment corpus must format to the checked-in output
  cp test/fmt/comments.lg .test-bin/comments.lg
  if "$LG" fmt .test-bin/comments.lg >/dev/null 2>&1 \
     && diff -u test/fmt/comments.fmted .test-bin/comments.lg > /dev/null 2>&1; then
    echo "ok fmt-comments-golden"
  else
    echo "FAIL(fmt-comments-golden)"
    diff -u test/fmt/comments.fmted .test-bin/comments.lg | head -15
    fail=1
  fi
else
  echo "skip fmt-fidelity (roundtrip not built)"
fi

# qcfuzz: lg-written fuzz corpus — random s-expr sources round-tripped
# through reader/printer, plus generated mini programs that must build
# and run (emit smoke).
if [ -x "$RT" ]; then
  FZD=.test-bin/qcfuzz.d
  rm -rf "$FZD"; mkdir -p "$FZD"
  fzbad=0
  if "$LG" build test/qcfuzz.lg -I lib -o .test-bin/qcfuzz_bin >/dev/null 2>&1 \
     && ./.test-bin/qcfuzz_bin >/dev/null 2>&1 \
     && "$RT" "$FZD"/sexpr_*.lg > /dev/null 2>&1; then
    for f in "$FZD"/prog_*.lg; do
      n=$(basename "$f" .lg)
      if ! { "$LG" build "$f" -I lib -o "$FZD/${n}_bin" >/dev/null 2>&1 \
             && "$FZD/${n}_bin" > /dev/null 2>&1; }; then
        echo "FAIL(qcfuzz-prog) $n"; fzbad=1
      fi
    done
    if [ $fzbad = 0 ]; then echo "ok qcfuzz (40 sexpr + 12 prog)"
    else fail=1; fi
  else
    "$RT" "$FZD"/sexpr_*.lg 2>&1 | head -5
    echo "FAIL(qcfuzz)"; fail=1
  fi
else
  echo "skip qcfuzz (roundtrip not built)"
fi

# repl smoke: defs persist across lines; eval lines print via the wrapper
if printf '(def x 1)\n(+ x 41)\n:quit\n' | "$LG" repl 2>/dev/null | grep -q '42'; then
  echo "ok repl"
else
  echo "FAIL(repl)"; fail=1
fi

# .lgi drift gate: checked-in interfaces must match .lg exports —
# a signature change or a stale entry fails; a drifted copy is caught.
if "$LG" lgi --check --all test/lgi.lg -I lib -I test >/dev/null 2>&1; then
  echo "ok lgi-check"
else
  echo "FAIL(lgi-check)"; fail=1
fi
cp test/_lib.lg .test-bin/_lib.lg
sed 's/int\] int/int] string/' test/_lib.lgi > .test-bin/_lib.lgi
if "$LG" lgi --check .test-bin/_lib.lg >/dev/null 2>&1; then
  echo "FAIL(lgi-drift-missed)"; fail=1
else
  echo "ok lgi-drift-detected"
fi

# LSP: initialize caps, diagnostics push on didOpen/didChange,
# completion (builtins + tops + require-alias members, degraded on errors)
if python3 test/lsp_smoke.py "$LG"; then
  :
else
  fail=1
fi

# lg doc: odoc-style HTML site — index + per-module pages with
# signature/variant/anchor markup and cross-module links; an .lgi
# gates which entries render.
if "$LG" doc lib/qc.lg lib/test.lg test/docd.lg examples/util.lg -I lib -I examples -I test -o .test-bin/apidoc --title "lg test" --tutorials docs/tutorials >/dev/null 2>&1 \
   && [ -f .test-bin/apidoc/index.html ] \
   && [ -f .test-bin/apidoc/qc.html ] \
   && [ -f .test-bin/apidoc/docd.html ] \
   && [ -f .test-bin/apidoc/01-getting-started.html ] \
   && grep -q 'id="gen-int"' .test-bin/apidoc/qc.html \
   && grep -q '(fn \[int int\]' .test-bin/apidoc/qc.html \
   && grep -q 'href="qc.html#gen-int"' .test-bin/apidoc/docd.html \
   && grep -q 'LCG seed' .test-bin/apidoc/qc.html \
   && grep -q 'defvariant' .test-bin/apidoc/docd.html \
   && grep -q '<h2>Tutorials</h2>' .test-bin/apidoc/index.html \
   && grep -q '>macro<' .test-bin/apidoc/test.html \
   && [ -f .test-bin/apidoc/core.html ] \
   && grep -q 'id="map"' .test-bin/apidoc/core.html \
   && grep -q 'id="sf-try"' .test-bin/apidoc/core.html \
   && grep -q 'special form' .test-bin/apidoc/core.html \
   && grep -q 'href="core.html"' .test-bin/apidoc/index.html \
   && ! grep -q 'id="internal-seed"' .test-bin/apidoc/util.html; then
  echo "ok doc"
else
  echo "FAIL(doc)"; fail=1
fi

# oxcaml backend: emit must carry mode annotations
if "$LG" emit test/oxcaml.lg --backend=oxcaml -o .test-bin/oxcaml.ml >/dev/null 2>&1 \
   && grep -q '@ local\|local_\|unique_\|stack_' .test-bin/oxcaml.ml; then
  echo "ok oxcaml-emit"
else
  echo "FAIL(oxcaml-emit)"
  fail=1
fi

# compile-speed regression line (bench): cold builds a single module and a
# two-module chain into a dedicated .lg-obj, plus a no-op warm relink.
# Thresholds are order-of-magnitude guards (measured cold ~0.26s, warm
# ~0.10s on an M-series); override via LG_BENCH_*_MS for slower machines.
now_ms() { python3 -c 'import time; print(int(time.time()*1000))'; }
LG_BENCH_COLD_MS=${LG_BENCH_COLD_MS:-5000}
LG_BENCH_DEPS_MS=${LG_BENCH_DEPS_MS:-8000}
LG_BENCH_WARM_MS=${LG_BENCH_WARM_MS:-3000}
BDIR=.test-bin/bench
rm -rf "$BDIR" && mkdir -p "$BDIR"

t0=$(now_ms)
"$LG" build test/core.lg -I lib -o "$BDIR/core" >/dev/null 2>&1
cold=$(( $(now_ms) - t0 ))
echo "bench cold-core ${cold}ms (limit ${LG_BENCH_COLD_MS}ms)"
[ "$cold" -lt "$LG_BENCH_COLD_MS" ] || { echo "FAIL(bench-cold)"; fail=1; }

t0=$(now_ms)
"$LG" build test/lgi.lg -I lib -o "$BDIR/lgi" >/dev/null 2>&1
deps=$(( $(now_ms) - t0 ))
echo "bench cold-deps ${deps}ms (limit ${LG_BENCH_DEPS_MS}ms)"
[ "$deps" -lt "$LG_BENCH_DEPS_MS" ] || { echo "FAIL(bench-deps)"; fail=1; }

t0=$(now_ms)
"$LG" build test/core.lg -I lib -o "$BDIR/core" >/dev/null 2>&1
warm=$(( $(now_ms) - t0 ))
echo "bench warm-relink ${warm}ms (limit ${LG_BENCH_WARM_MS}ms)"
[ "$warm" -lt "$LG_BENCH_WARM_MS" ] || { echo "FAIL(bench-warm)"; fail=1; }

exit $fail
