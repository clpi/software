#!/bin/sh
# Cold gate for the Pareto proof home. Compiles every proof and
# test from source, audits axioms, and runs the standing
# controls. Exit zero only if everything passes.
set -eu
cd "$(dirname "$0")"
LEAN="${LEAN:-lean}"
BUILD="$(mktemp -d)"
trap 'rm -rf "$BUILD"' EXIT

echo "== compile =="
"$LEAN" -o "$BUILD/Pareto.olean" Pareto.lean
LEAN_PATH="$BUILD" "$LEAN" -o "$BUILD/Tests.olean" Tests.lean
echo "compile exit 0"

echo "== placeholder scan =="
if grep -nE 'sorry|admit' Pareto.lean Tests.lean; then
  echo "REFUSED: placeholder proof step found"
  exit 1
fi
echo "no placeholders"

echo "== axiom audit =="
LEAN_PATH="$BUILD" "$LEAN" Audit.lean > "$BUILD/axioms.txt" 2>&1
cat "$BUILD/axioms.txt"
python3 - "$BUILD/axioms.txt" <<'PYEOF'
import re
import sys

allowed = {"propext", "Classical.choice", "Quot.sound"}
text = open(sys.argv[1]).read()
found = set()
for match in re.finditer(r"depends on axioms: \[([^\]]*)\]", text):
    for name in match.group(1).split(","):
        name = name.strip()
        if name:
            found.add(name)
extra = found - allowed
if "sorryAx" in found or extra:
    print("REFUSED: axioms beyond the standard three:", sorted(found))
    sys.exit(1)
print("axioms within the standard three:", sorted(found) if found else "none beyond none")
PYEOF

echo "== hypothesis and naming audit =="
python3 audit.py Pareto.lean Tests.lean
echo "== control: the audit must refuse the draft that assumes finiteness =="
if python3 audit.py controls/draft.lean; then
  echo "REFUSED: the hypothesis audit passed a draft it must refuse"
  exit 1
fi
echo "control passed: draft refused"
echo "GATE PASS"
