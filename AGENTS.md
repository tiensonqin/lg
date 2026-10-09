# AGENTS.md — lg (language) / lg2 (repo)

## Project constraints

- Code, comments, and documentation must be written in English
  (docstrings, comments, *.md docs, commit messages, PR descriptions).
- Solve root causes instead of adding workarounds.
- Prefer simple designs over complex ones.

## Runtime / data structures

- **Prefer clj data structures.** The lg runtime data structures are
  `Clj_core.Vec` / `Map` / `Set` / `List` / `Seq` / `Atom` (from
  logseq/clj-core), and the emitter must target them — do not hand-roll
  collection code or vendor copies.
- `runtime/lg_rt.ml` is the only runtime source the compiler embeds; keep it
  to printers and small helpers. Collection behavior belongs to clj-core.
- OCaml-level names follow Clojure munging (`?` -> `_`, `!` -> `_bang`,
  `-` -> `_`).

## OCaml type safety

- Never use `Obj.magic`. Do not hide it behind an alias, wrapper, or helper.
- Model heterogeneous domains (reader forms, macro values, emitted types)
  with closed, statically typed variants — no universal dynamic type.
- Keep emitted OCaml type-correct: the emitter must never produce code that
  needs casts; unify in the inferencer instead.
