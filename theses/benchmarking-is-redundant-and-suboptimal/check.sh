#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
LEAN="${LEAN:-${LEAN_BIN:-lean}}"
export LEAN_PATH=.
"$LEAN" --version
sources=(Qualification.lean Redundancy.lean Benchmark.lean Tests.lean)
forbidden='\b(sorry|admit|axiom|native_decide)\b'
if grep -nE "$forbidden" "${sources[@]}"; then
  echo 'FAIL: forbidden proof token'; exit 1
fi
controls=$(mktemp -d)
trap 'rm -rf "$controls"' EXIT
for mod in Qualification Redundancy Benchmark Tests; do
  "$LEAN" -DwarningAsError=true -o "$mod.olean" "$mod.lean" | tee "$controls/$mod.log"
  if grep -q 'sorryAx' "$controls/$mod.log"; then
    echo 'FAIL: admitted theorem in axiom report'; exit 1
  fi
done
printf 'theorem rejected : True := by sorry\n' > "$controls/Admission.lean"
if "$LEAN" -DwarningAsError=true "$controls/Admission.lean" > "$controls/rejection.log" 2>&1; then
  echo 'FAIL: admission control passed'; exit 1
fi
grep -q 'sorry' "$controls/rejection.log"
printf 'theorem rejected : False := True.intro\n' > "$controls/TypeError.lean"
if "$LEAN" -DwarningAsError=true "$controls/TypeError.lean" > "$controls/rejection.log" 2>&1; then
  echo 'FAIL: type-error control passed'; exit 1
fi
grep -q 'error:' "$controls/rejection.log"
# Unlike sorry, custom axioms need not produce warnings. Test the source scan.
for token in sorry admit axiom native_decide; do
  printf '%s\n' "$token" > "$controls/Forbidden.lean"
  if ! grep -qE "$forbidden" "$controls/Forbidden.lean"; then
    echo "FAIL: scanner missed $token"; exit 1
  fi
done
echo 'PASS: four modules, admission/type-error rejection controls, four forbidden-token controls'
