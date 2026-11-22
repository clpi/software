#!/bin/sh
set -eu
cd "$(dirname "$0")"
if ! command -v lake >/dev/null 2>&1; then
  for candidate in "${HOME}/.elan/bin" "${HOME}/lean/lean-4.19.0-linux/bin"; do
    if [ -x "${candidate}/lake" ]; then
      PATH="${candidate}:${PATH}"
      export PATH
      break
    fi
  done
fi
if ! command -v lake >/dev/null 2>&1; then
  echo "lake not found; install the pinned toolchain or put elan on PATH" >&2
  exit 1
fi
fail() {
  echo "$1" >&2
  exit 1
}
source_guard() {
  grep -RInE --exclude-dir=.lake --exclude-dir=build --include='*.lean' \
    '(^|[^[:alnum:]_])(sorry|admit|axiom|native_decide)([^[:alnum:]_]|$)' .
}

mkdir -p build
echo "== controls: proof escape scans =="
ctrl=$(mktemp -d build/escape-control.XXXXXX)
for escape in sorry admit axiom native_decide; do
  case "$escape" in
    sorry) printf '%s\n' 'theorem forbidden_admission : False := by sorry' > "${ctrl}/Bad.lean" ;;
    admit) printf '%s\n' 'theorem forbidden_admission : False := by admit' > "${ctrl}/Bad.lean" ;;
    axiom) printf '%s\n' 'axiom forbidden_admission : False' > "${ctrl}/Bad.lean" ;;
    native_decide) printf '%s\n' 'theorem forbidden_admission : True := by native_decide' > "${ctrl}/Bad.lean" ;;
  esac
  if grep -En '(^|[^[:alnum:]_])(sorry|admit|axiom|native_decide)([^[:alnum:]_]|$)' "${ctrl}/Bad.lean"; then
    echo "control ${escape}: rejected"
  else
    rm -rf "${ctrl}"
    fail "${escape} control was not rejected"
  fi
done
rm -rf "${ctrl}"
if source_guard; then
  fail "release tree contains a prohibited proof escape hatch"
fi
echo "release source scan: clean"

echo "== building release tree =="
lake build > build/lake.log 2>&1 || {
  cat build/lake.log
  fail "lake build failed"
}
cat build/lake.log
if grep -Eq 'sorryAx|error:|warning:' build/lake.log; then
  fail "release tree has checker diagnostics"
fi

echo "== compiling every repository Lean file with warnings as errors =="
find . -type f -name '*.lean' -not -path './.lake/*' -not -path './build/*' -print | LC_ALL=C sort > build/lean-files.txt
lean_count=$(wc -l < build/lean-files.txt | tr -d ' ')
[ "${lean_count}" -gt 0 ] || fail "no Lean files found"
index=0
while IFS= read -r source; do
  index=$((index + 1))
  log="build/lean-${index}.log"
  if ! lake env lean -DwarningAsError=true "${source}" > "${log}" 2>&1; then
    cat "${log}"
    fail "warnings-as-errors compilation failed: ${source}"
  fi
  if grep -Eq 'sorryAx|error:|warning:' "${log}"; then
    cat "${log}"
    fail "checker diagnostic in ${source}"
  fi
done < build/lean-files.txt
echo "checked ${lean_count} Lean source files"

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

echo "== axiom dependencies =="
lake env lean -DwarningAsError=true SoftwareIsComposable/Axioms.lean > build/axioms.log 2>&1
cat build/axioms.log
if grep -Eq 'sorryAx|error:|warning:' build/axioms.log; then
  fail "axiom audit failed"
fi

echo "== harness =="
lake exe harness examples/old.csv examples/new.csv > build/harness.out
cat build/harness.out
diff -u examples/expected.txt build/harness.out

echo "== theorem implications =="
lake env lean -DwarningAsError=true Implications.lean > build/implications-lean.log 2>&1
cat build/implications-lean.log
if grep -Eq 'sorryAx|error:|warning:' build/implications-lean.log; then
  fail "implications generator failed"
fi
cat build/implications.md
{
  echo "== proof escape controls =="
  echo "sorry: rejected"
  echo "admit: rejected"
  echo "axiom: rejected"
  echo "native_decide: rejected"
  echo "release source scan: clean"
  echo "== release tree =="
  cat build/lake.log
  echo "== all Lean files =="
  echo "${lean_count} Lean source files compiled with -DwarningAsError=true"
  echo "== control: worse release =="
  echo "rejected"
  cat build/worse-control.log
  echo "== axiom dependencies =="
  cat build/axioms.log
  echo "== harness =="
  cat build/harness.out
  echo "== theorem implications =="
  cat build/implications.md
} > CHECK.log
echo "checker passed"
