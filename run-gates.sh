#!/usr/bin/env bash
# Run every gate of every thesis in place. Gate list: consolidation/gates.tsv (thesis, gate).
# Usage: ./run-gates.sh [thesis ...]   (no argument = all). Needs lean/lake v4.19.0 on PATH.
# Exit 1 if any gate exits non-zero. 8 gates fail at every import because they need inputs
# the caller supplies (see consolidation/gates-results.tsv); they fail the same way in the old repos.
set -uo pipefail
cd "$(dirname "$0")"
fails=0
while IFS=$'\t' read -r name gate; do
  [ $# -gt 0 ] && ! printf '%s\n' "$@" | grep -qx "$name" && continue
  root="theses/$name"
  case "$gate" in
    lake:*) (cd "$root/${gate#lake:}" && lake build) ;;
    *.py)   (cd "$root/$(dirname "$gate")" && python3 "$(basename "$gate")") ;;
    *)      (cd "$root/$(dirname "$gate")" && bash "$(basename "$gate")") ;;
  esac > /dev/null 2>&1
  rc=$?; printf '%s\t%s\t%s\n' "$name" "$gate" "$rc"; [ $rc -ne 0 ] && fails=$((fails+1))
done < consolidation/gates.tsv
echo "gates failing: $fails"; [ $fails -eq 0 ]
