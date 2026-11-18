#!/bin/sh
set -eu
cd "$(dirname "$0")"
if [ -n "${LEAN:-}" ]; then
  :
elif command -v lean >/dev/null 2>&1; then
  LEAN=lean
elif [ -x "$HOME/lean-4.19.0-linux/bin/lean" ]; then
  LEAN="$HOME/lean-4.19.0-linux/bin/lean"
else
  echo "lean not found" >&2
  exit 1
fi
export PATH="$(dirname "$(command -v "$LEAN")"):$PATH"
if [ -n "${LAKE:-}" ]; then
  :
elif command -v lake >/dev/null 2>&1; then
  LAKE=lake
else
  echo "lake not found" >&2
  exit 1
fi
export LEAN_PATH=".:${LEAN_PATH:-}"

echo "=== red: admitted proof ==="
if "$LEAN" -DwarningAsError=true controls/Admitted.lean >/tmp/admitted.out 2>&1; then
  echo "admitted proof was accepted" >&2
  exit 1
fi
cat /tmp/admitted.out

echo "=== red: C1-C4 accept under the submitted-field checker ==="
"$LEAN" -DwarningAsError=true Audit/Counterexamples.lean

echo "=== pass: default target ==="
if grep -En '(^|[^[:alnum:]_])(sorry|admit|axiom|native_decide)([^[:alnum:]_]|$)' \
  IncrementalCert.lean IncrementalCert/*.lean Audit/Refusals.lean Cli.lean Axioms.lean Implications.lean
then
  echo "Rejected prohibited proof escape hatch" >&2
  exit 1
fi
"$LAKE" build
echo "=== red: empty required passes the subset reading of C4 ==="
echo "empty_required_passes_c4"
"$LAKE" env "$LEAN" -DwarningAsError=true Implications.lean
"$LAKE" env "$LEAN" -DwarningAsError=true Axioms.lean

echo "=== cli ==="
set +e
cli_out=$("$LAKE" env "$LEAN" --run Cli.lean examples/chain.json 2>&1)
cli_code=$?
set -e
printf '%s\n' "$cli_out"
if [ "$cli_code" -eq 0 ]; then
  echo "cli did not refuse the middle release" >&2
  exit 1
fi
printf '%s\n' "$cli_out" | grep -q -F "release-one: refused app"
printf '%s\n' "$cli_out" | grep -q -F "release-two: not-applied"
echo "check passed"
