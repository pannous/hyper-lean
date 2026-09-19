#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"

if [[ -L .lake/packages ]]; then
  echo 'Use checkout-local .lake/packages before running Lake; see SETUP_NOTES.md.' >&2
  exit 1
fi

# Build first: `lake env lean` alone can silently read stale local oleans.
lake build Hyper.HyperReal Hyper.HyperProbability Hyper.HyperIntegral \
  Hyper.AlgebraicStochasticsBasic Hyper.AlgebraicStochasticsIntermediate \
  Hyper.AlgebraicStochasticsAdvanced Hyper.AlgebraicDart Hyper.AlgebraicSupport \
  Hyper.GeometricContent Hyper.CubicContent Hyper.AlgebraicOrder Hyper.RoundContent \
  Hyper.HyperListProbability Hyper.HyperListSemantics
lake env lean test_all.lean
lake env lean Hyper/probes/IntegralExamples.lean
audit_log=$(mktemp)
trap 'rm -f "$audit_log"' EXIT
lake env lean test_algebraic.lean | tee "$audit_log"
if grep -Eq 'sorryAx|eq_of_simplify_eq|Lean.ofReduceBool|Lean.trustCompiler' "$audit_log"; then
  echo 'The exact algebraic path acquired an untrusted axiom.' >&2
  exit 1
fi

# The legacy adapter imports old modules but may depend only on standard Lean axioms.
lake env lean test_hyperlist_foundation.lean | tee "$audit_log"
python3 - "$audit_log" <<'PY_AUDIT'
import re
import sys
text = open(sys.argv[1]).read()
allowed = {"propext", "Classical.choice", "Quot.sound"}
reports = re.findall(r"depends on axioms:\s*\[([^]]*)\]", text, re.S)
if not reports:
    raise SystemExit("No HyperList foundation axiom audit results were produced.")
for report in reports:
    unexpected = {x.strip() for x in report.split(",") if x.strip()} - allowed
    if unexpected:
        raise SystemExit("Untrusted HyperList foundation dependency: " + str(unexpected))
print("HyperList foundation audit: only standard Lean axioms.")
PY_AUDIT
