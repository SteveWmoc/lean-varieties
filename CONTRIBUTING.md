# Contributing

## Local checks

Use elan to select the version in `lean-toolchain`. After cloning, retrieve
mathlib's compiled cache and run:

```sh
lake exe cache get
lake build --wfail
lake lint
bash scripts/check-lint.sh
git diff --check
```

The smoke/report script additionally requires Bash and `jq`. Generated files
in `.lake/` and `reports/` are ignored; commit the dependency manifest, not
compiled output. Update the Lean toolchain, mathlib revision, and manifest as
one change when upgrading dependencies.

## What lint checks do

`builtinLint = true` in `lakefile.toml` makes `lake check-lint` succeed and
configures ordinary `lake lint` to use Lean's builtin lint engine. This lets
the Lean GitHub action discover and execute linting automatically.

During `lake build --wfail`, enabled elaboration/style warnings fail the
build. Ordinary `lake lint` then reads recorded text-linter findings, runs
registered environment linters with their enabled options, and checks
deferred documentation references. It fails when it reports violations.
The root import lists every public module so linting covers the library.

`scripts/check-lint.sh` verifies the setup with an isolated temporary package
using the same toolchain. A deliberate unused local variable must appear as a
`linter.unusedVariables` JSON finding and cause ordinary linting to fail.
The temporary package is deleted on exit and is never part of the library.
The script then collects the project's report and requires it to be empty.

`lake lint --code-quality LeanVarieties` emits a stream of JSON objects, not
one JSON array. CI uses `jq --slurp` to save the array as
`reports/code-quality.json`, alongside the original stream. Code-quality
mode itself succeeds even when findings exist and does not run deferred
documentation checks, so it complements ordinary linting rather than
replacing it. The report is uploaded as the `lean-code-quality` Actions
artifact, including when a later report check fails.

These checks use the pinned defaults and any explicit source options. They
are not an invocation of every optional Lean linter or mathlib's separate
`#lint` suite. Prefer fixing a warning to adding a linter suppression.

## Adding mathematical API

- Reuse mathlib's definitions and theorems before adding parallel machinery.
- Keep the convention for `Variety` explicit; reducedness, irreducibility,
  smoothness, and dimension need their own hypotheses when relevant.
- Keep constructions over `Spec k`, and expose structural-map compatibility
  and underlying-object simp lemmas where useful.
- Support arbitrary field universes and zero-dimensional standard spaces.
- Import new public modules in `LeanVarieties.lean`, update the README module
  guide, and add or update a note in `docs/` when the design needs explanation.
- Keep changes focused and wait for the warning-as-error build and lint
  checks before merging.
