#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")"
export PATH="${HOME}/.elan/bin:${PATH}"

if [ "$(cat vendor/software-is-composable/REVISION)" != "033c12c01299a9b28983bee410c230641adc7d1e" ]; then
  echo "composable snapshot is not 033c12c0" >&2
  exit 1
fi

if grep -RInE --include='*.lean' --exclude-dir=.lake \
  '(^|[^[:alnum:]_])(sorry|admit|axiom|native_decide)([^[:alnum:]_]|$)' .; then
  echo "Rejected prohibited proof escape hatch" >&2
  exit 1
fi

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
cp lean-toolchain "$TMP/"

echo "RED admit"
printf '%s\n' 'theorem forbidden_admission : False := by admit' > "$TMP/Admitted.lean"
set +e
lean -DwarningAsError=true "$TMP/Admitted.lean" > "$TMP/admit.out" 2>&1
admit_code=$?
set -e
cat "$TMP/admit.out"
if [ "$admit_code" -eq 0 ]; then
  echo "admit was accepted" >&2
  exit 1
fi
echo "RED admit rejected exit ${admit_code}"

echo "RED sorry"
printf '%s\n' 'theorem forbidden_sorry : False := by sorry' > "$TMP/Sorry.lean"
set +e
lean -DwarningAsError=true "$TMP/Sorry.lean" > "$TMP/sorry.out" 2>&1
sorry_code=$?
set -e
cat "$TMP/sorry.out"
if [ "$sorry_code" -eq 0 ]; then
  echo "sorry was accepted" >&2
  exit 1
fi
echo "RED sorry rejected exit ${sorry_code}"

lake build SoftwareDoesntRegress.Profiles

cat > "$TMP/Red.lean" <<'EOF'
import SoftwareDoesntRegress.Profiles
open SoftwareDoesntRegress

#eval IO.println s!"RED refuse symbol {firstRefusal exNames exInc exPure}"
#eval IO.println s!"RED pure {accepts exInc exPure}"
#eval IO.println s!"RED equal {accepts exInc exEqual}"
#eval IO.println s!"RED trade {accepts exInc exTrade}"

theorem control_false_accept : accepts exInc exPure = true := by decide
EOF

echo "RED regressed symbol and false acceptance"
set +e
lake env lean -DwarningAsError=true "$TMP/Red.lean" > "$TMP/red.out" 2>&1
red_code=$?
set -e
cat "$TMP/red.out"
if [ "$red_code" -eq 0 ]; then
  echo "false acceptance compiled" >&2
  exit 1
fi
if ! grep -q 'RED refuse symbol (some emit)' "$TMP/red.out"; then
  echo "named symbol refusal was not shown" >&2
  exit 1
fi
echo "RED false acceptance rejected exit ${red_code}"

echo "GREEN"
lake build > "$TMP/green.out" 2>&1
green_code=$?
cat "$TMP/green.out"
if [ "$green_code" -ne 0 ]; then
  exit "$green_code"
fi
if grep -Eq 'sorryAx|error:|warning:' "$TMP/green.out"; then
  echo "Rejected checker diagnostics" >&2
  exit 1
fi

./.lake/build/bin/gate examples/stream.json > "$TMP/stream.out"
cat "$TMP/stream.out"
diff -u examples/stream.expected "$TMP/stream.out"

{
  echo "RED admit"
  cat "$TMP/admit.out"
  echo "RED sorry"
  cat "$TMP/sorry.out"
  echo "RED regressed symbol and false acceptance"
  cat "$TMP/red.out"
  echo "GREEN"
  cat "$TMP/green.out"
  echo "GATE"
  cat "$TMP/stream.out"
} > CHECK.log

echo "PASS"
