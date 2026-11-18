#!/bin/sh
set -eu
cd "$(dirname "$0")"
if ! command -v lake >/dev/null 2>&1; then
  export PATH="${HOME}/lean/lean-4.19.0-linux/bin:${PATH}"
fi

fail() {
  echo "$1" >&2
  exit 1
}

src_guard() {
  grep -RInE --exclude-dir=.lake --exclude-dir=build --include='*.lean' \
    '(^|[^[:alnum:]_])(sorry|admit|axiom|native_decide)([^[:alnum:]_]|$)' .
}

echo "== control: admitted proof =="
ctrl=$(mktemp -d)
printf '%s\n' 'theorem forbidden_admission : False := by sorry' > "${ctrl}/Bad.lean"
if grep -En '(^|[^[:alnum:]_])(sorry|admit|axiom|native_decide)([^[:alnum:]_]|$)' "${ctrl}/Bad.lean"; then
  echo "control admitted proof: rejected"
else
  rm -rf "${ctrl}"
  fail "sorry control was not rejected"
fi
rm -rf "${ctrl}"

if src_guard; then
  fail "release tree contains a prohibited proof escape hatch"
fi

mkdir -p build
echo "== building release tree =="
lake build > build/lake.log 2>&1 || {
  cat build/lake.log
  fail "lake build failed"
}
cat build/lake.log

echo "== control: worse release claimed admitted =="
cat > build/WorseControl.lean << 'EOF'
import SoftwareIsComposable.Examples
theorem worse_is_admitted :
    SoftwareIsComposable.releaseAdmitted SoftwareIsComposable.worseOld SoftwareIsComposable.worseNew = true := by
  decide
EOF
set +e
lake env lean -DwarningAsError=true build/WorseControl.lean > build/worse-control.log 2>&1
worse_status=$?
set -e
cat build/worse-control.log
if [ "${worse_status}" -eq 0 ]; then
  fail "worse release control was accepted"
fi
echo "control worse release: rejected"

if grep -Eq 'sorryAx|error:|warning:' build/lake.log; then
  fail "release tree has checker diagnostics"
fi

echo "== axioms =="
lake env lean -DwarningAsError=true SoftwareIsComposable/Axioms.lean > build/axioms.log 2>&1
cat build/axioms.log
if grep -Eq 'sorryAx|error:|warning:' build/axioms.log; then
  fail "axiom audit failed"
fi

echo "== harness =="
lake exe harness examples/old.csv examples/new.csv > build/harness.out
cat build/harness.out
diff -u examples/expected.txt build/harness.out

echo "== implications =="
lake env lean -DwarningAsError=true Implications.lean > build/implications-lean.log 2>&1
cat build/implications-lean.log
if grep -Eq 'sorryAx|error:|warning:' build/implications-lean.log; then
  fail "implications generator failed"
fi
cat build/implications.md

{
  echo "== control: admitted proof =="
  echo "rejected by source guard"
  echo "== control: worse release =="
  echo "rejected"
  cat build/worse-control.log
  echo "== release tree =="
  cat build/lake.log
  echo "== axioms =="
  cat build/axioms.log
  echo "== harness =="
  cat build/harness.out
  echo "== implications =="
  cat build/implications.md
} > CHECK.log

echo "checker passed"
