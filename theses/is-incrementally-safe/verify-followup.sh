#!/usr/bin/env bash
set -euo pipefail
# Reject proof escapes before compiling, including custom axioms that Lean permits.
scan_sources() {
  if grep -nE '\b(sorry|admit|axiom|native_decide)\b' "$@"; then
    echo 'Proof escape hatch detected' >&2
    return 1
  fi
}
scan_sources SoftwareIsIncrementallySafe/*.lean audit/Counterexamples.lean
lake build
lake build Counterexamples
for f in SoftwareIsIncrementallySafe/Checker.lean SoftwareIsIncrementallySafe/AuditFix.lean SoftwareIsIncrementallySafe/Example.lean SoftwareIsIncrementallySafe/RunAdmission.lean SoftwareIsIncrementallySafe/FullSnapshotAudit.lean audit/Counterexamples.lean; do
  lake env lean -DwarningAsError=true "$f"
done
# Exercise both the scanner and compiler; expected failures must really fail.
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
for escape in 'theorem bad : False := by sorry' 'theorem bad : False := by admit' 'axiom bad : False' 'theorem bad : True := by native_decide'; do
  printf '%s\n' "$escape" > "$work/Escape.lean"
  if scan_sources "$work/Escape.lean" > "$work/scan.log" 2>&1; then
    echo "FAIL: scanner accepted $escape" >&2
    exit 1
  fi
done
for escape in 'theorem bad : False := by sorry' 'theorem bad : False := by admit' 'def bad : Nat := "not a number"'; do
  printf '%s\n' "$escape" > "$work/CompileNegative.lean"
  if lake env lean -DwarningAsError=true "$work/CompileNegative.lean" > "$work/compile.log" 2>&1; then
    echo "FAIL: compiler accepted negative control $escape" >&2
    exit 1
  fi
done
cat > "$work/AdmissionNegative.lean" <<'LEAN'
import SoftwareIsIncrementallySafe
open SoftwareIsIncrementallySafe
-- This obsolete acceptance claim must fail under the canonical checker.
example : check appSpec (fun _ => ["not-allowed"])
    { omittedDelta with changed := [] } = Verdict.accept := by decide
LEAN
if lake env lean -DwarningAsError=true "$work/AdmissionNegative.lean" > "$work/admission.log" 2>&1; then
  echo 'FAIL: unsafe empty-delta acceptance control compiled' >&2
  exit 1
fi
echo 'PASS: 4 scanner rejection controls, 3 compiler rejection controls, 1 admission rejection control'
