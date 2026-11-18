#!/bin/sh
set -eu
cd "$(dirname "$0")"
if [ -d "$HOME/.elan/bin" ]; then
  PATH="$HOME/.elan/bin:$PATH"
  export PATH
fi

root=$(pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

scan() {
  grep -R -n -E '(^|[^A-Za-z0-9_])(sorry|admit)([^A-Za-z0-9_]|$)|^[[:space:]]*axiom[[:space:]]' "$@"
}

echo "library gate"
if scan SoftwareDoesntNeedReview SoftwareDoesntNeedReview.lean lakefile.lean scripts; then
  echo "refused: sorry, admit, or axiom declaration in the library" >&2
  exit 1
fi
echo "library gate clean"

echo "build"
lake build >"$tmp/build.out" 2>&1
cat "$tmp/build.out"
if grep -E 'warning:|sorryAx' "$tmp/build.out"; then
  echo "refused: warning or sorryAx in the build" >&2
  exit 1
fi

echo "axiom audit"
lake env lean SoftwareDoesntNeedReview/Audit.lean >"$tmp/axioms.out" 2>&1
cat "$tmp/axioms.out"
python3 - "$tmp/axioms.out" <<'PY'
import re, sys
text = open(sys.argv[1], encoding="utf-8").read()
allowed = {"propext", "Classical.choice", "Quot.sound"}
found = False
for line in text.splitlines():
    if "sorryAx" in line:
        sys.exit("refused: sorryAx")
    m = re.search(r"depends on axioms: \[([^\]]*)\]", line)
    if m:
        found = True
        names = [n.strip() for n in m.group(1).split(",") if n.strip()]
        bad = [n for n in names if n not in allowed]
        if bad:
            sys.exit("refused: " + ", ".join(bad))
    elif "does not depend on any axioms" in line:
        found = True
if not found:
    sys.exit("refused: no axiom report")
if "zero_information" not in text:
    sys.exit("refused: headline missing from axiom report")
print("axiom audit clean")
PY

echo "upstream dependencies"
lake env lean scripts/UpstreamDeps.lean >"$tmp/deps.out" 2>&1
cat "$tmp/deps.out"
python3 - "$tmp/deps.out" <<'PY'
import sys
text = open(sys.argv[1], encoding="utf-8").read()
blocks = {}
name = None
for line in text.splitlines():
    if line.startswith("THEOREM "):
        name = line[len("THEOREM "):].strip()
        blocks[name] = []
    elif line.startswith("DEP ") and name:
        blocks[name].append(line[len("DEP "):].strip())
required = {
    "SoftwareDoesntNeedReview.RubberStamp.zero_information": [],
    "SoftwareDoesntNeedReview.RubberStamp.guarded_independent_of_approval": [
        "SoftwareDoesntNeedReview.Chain.Optimality.acceptsGuarded"],
    "SoftwareDoesntNeedReview.Replacement.process_monotone": [
        "SoftwareDoesntNeedReview.Chain.Certifiable.extensive"],
    "SoftwareDoesntNeedReview.Replacement.criterion_never_lost": [
        "SoftwareDoesntNeedReview.Chain.Certifiable.extensive"],
    "SoftwareDoesntNeedReview.Boundary.boundary_missed_by_certifier": [
        "SoftwareDoesntNeedReview.Chain.Quantifiable.recorded"],
    "SoftwareDoesntNeedReview.Boundary.boundary_legacy_witness_insufficient": [
        "SoftwareDoesntNeedReview.Chain.Quantifiable.unrestricted_witness"],
    "SoftwareDoesntNeedReview.Boundary.boundary_no_platform_premise": [
        "SoftwareDoesntNeedReview.Chain.Quantifiable.coverage",
        "SoftwareDoesntNeedReview.Chain.Quantifiable.PlatformPremise"],
    "SoftwareDoesntNeedReview.Boundary.bad_cell_not_qualified": [
        "SoftwareIsComposable.symbolAdmitted"],
    "SoftwareDoesntNeedReview.Chain.Certifiable.extensive_equiv": [
        "SoftwareIsComposable.symbolAdmitted"],
    "SoftwareDoesntNeedReview.Chain.Regress.regress_equiv": [
        "SoftwareIsComposable.symbolAdmitted"],
    "SoftwareDoesntNeedReview.Chain.Safe.safe_equiv": [
        "SoftwareIsComposable.accepts"],
    "SoftwareDoesntNeedReview.Controls.control_human_regression_refused": [
        "SoftwareDoesntNeedReview.Chain.Regress.verdict"],
    "SoftwareDoesntNeedReview.Controls.control_human_regression_equiv": [
        "SoftwareIsComposable.symbolVerdict"],
    "SoftwareDoesntNeedReview.Controls.safety_refused_by_name": [
        "SoftwareDoesntNeedReview.Chain.Safe.verdict"],
    "SoftwareDoesntNeedReview.Controls.safety_equiv": [
        "SoftwareIsComposable.symbolVerdict"],
}
for thm, deps in required.items():
    if thm not in blocks:
        sys.exit("refused: missing theorem block " + thm)
    have = blocks[thm]
    if have == ["none"] and deps:
        sys.exit("refused: " + thm + " has no upstream dependency")
    for dep in deps:
        if dep not in have:
            sys.exit("refused: " + thm + " missing " + dep)
    for dep in have:
        if dep != "none" and not (
            dep.startswith("SoftwareDoesntNeedReview.Chain.") or
            dep.startswith("SoftwareIsComposable.")):
            sys.exit("refused: unexpected dependency " + dep)
print("dependency check clean")
PY

expect_fail() {
  if lake env lean -DwarningAsError=true "$1" >"$tmp/ctrl.out" 2>&1; then
    echo "refused: $1 was accepted" >&2
    cat "$tmp/ctrl.out" >&2
    exit 1
  fi
  echo "refused $1"
  cat "$tmp/ctrl.out"
}

echo "admitted-proof control"
expect_fail controls/Admitted.lean
echo "admit control"
expect_fail controls/AdmitTactic.lean
echo "warning control"
expect_fail controls/Unused.lean

echo "custom-axiom control"
lake env lean controls/CustomAxiom.lean >"$tmp/custom.out" 2>&1 || true
cat "$tmp/custom.out"
if ! grep -q bogusAxiom "$tmp/custom.out"; then
  echo "refused: custom axiom control did not report bogusAxiom" >&2
  exit 1
fi
if python3 - "$tmp/custom.out" <<'PY'
import re, sys
text = open(sys.argv[1], encoding="utf-8").read()
allowed = {"propext", "Classical.choice", "Quot.sound"}
bad = False
for line in text.splitlines():
    m = re.search(r"depends on axioms: \[([^\]]*)\]", line)
    if m:
        names = [n.strip() for n in m.group(1).split(",") if n.strip()]
        if any(n not in allowed for n in names):
            bad = True
if not bad:
    sys.exit(0)
sys.exit(1)
PY
then
  echo "refused: custom axiom passed the allowlist" >&2
  exit 1
fi
echo "refused controls/CustomAxiom.lean"

if ! scan controls/Admitted.lean controls/AdmitTactic.lean controls/CustomAxiom.lean >/dev/null; then
  echo "refused: planted controls were not detected by the source gate" >&2
  exit 1
fi
echo "source gate detects the planted controls"
echo "check clean"
