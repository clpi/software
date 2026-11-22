#!/usr/bin/env python3
"""Standing audits for the Pareto proof home.

Two checks over the proof sources:

1. Hypothesis audit (obligation 3 control). Finiteness must be
   derived, never assumed. This audit refuses any source where
   finiteness appears as a hypothesis: a binder whose type is a
   finiteness predicate, or any use of the foreign finiteness
   typeclasses. It is run over the proof files (must pass) and
   over the draft in the controls folder (must refuse); a gate
   that passes the draft has failed its control.

2. Naming audit. Every declaration name minted in the proof
   sources is a single lowercase word: no underscores, no
   capitals, no mashed compounds detectable as mixed case.
"""
import re
import sys

FINITE_BINDER = re.compile(r"\(\s*[A-Za-z][A-Za-z0-9']*\s*:\s*fin\b")
FINITE_TOKEN = re.compile(r"\b(Finite|Fintype)\b")
DECL = re.compile(r"^(?:def|theorem|structure|inductive|namespace)\s+([A-Za-z][A-Za-z0-9']*)")


def check(path):
    bad = []
    with open(path) as handle:
        for number, line in enumerate(handle, 1):
            if FINITE_BINDER.search(line) or FINITE_TOKEN.search(line):
                bad.append((number, "finiteness stated as a hypothesis"))
            m = DECL.match(line)
            if m:
                name = m.group(1)
                if name != name.lower() or "_" in name:
                    bad.append((number, "minted name is not a single lowercase word: " + name))
    return bad


def main():
    failed = False
    for path in sys.argv[1:]:
        bad = check(path)
        for number, why in bad:
            print(f"REFUSED {path}:{number}: {why}")
            failed = True
        if not bad:
            print(f"OK {path}")
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
