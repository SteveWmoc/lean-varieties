#!/usr/bin/env bash
# Verify both failure detection and JSON reporting using the pinned Lean toolchain.
set -euo pipefail
cd "$(dirname "$0")/.."

lake check-lint
probe=$(mktemp -d)
trap 'rm -rf "$probe"' EXIT
cp lean-toolchain "$probe/lean-toolchain"
cat > "$probe/lakefile.toml" <<'EOF'
name = "LintProbe"
builtinLint = true
defaultTargets = ["LintProbe"]

[[lean_lib]]
name = "LintProbe"
EOF
cat > "$probe/LintProbe.lean" <<'EOF'
import Lean

def lintProbe : Nat :=
  let unusedLocal := 1
  0
EOF

# A clean report alone cannot prove that linting is active. This known violation
# must appear in JSON and must cause ordinary linting to return a failure.
lake -d "$probe" --quiet lint --code-quality LintProbe > "$probe/findings.json"
if ! jq --slurp --exit-status '
  any(.[]; .name == "linter.unusedVariables" and
    .source.module.name == "LintProbe" and .value.scalar.value > 0)
' "$probe/findings.json"; then
  cat "$probe/findings.json" >&2
  echo 'Lint smoke check failed: the expected JSON finding is missing.' >&2
  exit 1
fi
if lake -d "$probe" --quiet lint LintProbe > "$probe/lint.log" 2>&1; then
  echo 'Lint smoke check failed: the deliberate unused variable was accepted.' >&2
  exit 1
fi
if ! grep -q 'unusedLocal' "$probe/lint.log"; then
  cat "$probe/lint.log" >&2
  echo 'Lint smoke check failed for a reason other than the expected warning.' >&2
  exit 1
fi
echo 'Lint smoke check passed: the known violation is reported and rejected.'

mkdir -p reports
lake --quiet lint --code-quality LeanVarieties > reports/code-quality.stream.json
jq --slurp . reports/code-quality.stream.json > reports/code-quality.json
# JSON reporting exits successfully even when findings exist. Enforce emptiness
# explicitly, in addition to the ordinary lake lint check run by the Lean action.
jq --exit-status 'type == "array" and length == 0' reports/code-quality.json
