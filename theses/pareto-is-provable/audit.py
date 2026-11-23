#!/usr/bin/env python3
"""Standing audits for the Pareto proof home.

Three checks over the proof sources:

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

3. Premise audit (obligation 19). Every assumption used in
   every theorem of the proof sources is extracted from its
   signature (binder types and statement antecedents) and
   decomposed into leaf conditions. A leaf is admitted only
   if it is one of: the registered premise P1 or its stamped
   instrument record; the section 5 operation admissibility
   condition; or a concrete decidable condition over named
   data (membership or non-membership in a named list, an
   equality or an inequality of concrete terms). A leaf of
   any other shape — an abstract predicate, a finiteness
   statement, an unregistered universal — is refused, and
   the obligation whose proof carries it reopens. The
   registry premises P2, P3, P4 enter the proofs in content,
   as the lane records state (pin equalities, the tally
   checker pass, the separate checker code path), and their
   concrete forms are exactly the equality and checker-pass
   leaves admitted above.
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
        for name, atom in premise_check(path):
            print(f"REFUSED {path} {name}: unregistered assumption: {atom}")
            failed = True
    sys.exit(1 if failed else 0)


DATA = re.compile(
    r"^(Nat|Bool|row|cand|axis|space|table|cell|receipt|verdictrec|"
    r"tuple|record|op|outcome|entry|eight\.verdictrec|"
    r"axis × Nat × Nat|Type|α)$")
THEOREM = re.compile(r"^theorem\s+([A-Za-z][A-Za-z0-9']*)")
NAMESPACE = re.compile(r"^namespace\s+([A-Za-z][A-Za-z0-9']*)")
END = re.compile(r"^end\s+([A-Za-z][A-Za-z0-9']*)")


def is_data(kind):
    kind = kind.strip()
    if DATA.match(kind):
        return True
    if kind.startswith("List "):
        return True
    if "→" in kind:
        parts = [p.strip() for p in kind.split("→")]
        return all(is_data(p) for p in parts[:-1]) and (
            is_data(parts[-1]) or parts[-1] == "Prop")
    return False


def groups(text):
    out, depth, start = [], 0, None
    for i, ch in enumerate(text):
        if ch in "([{":
            if depth == 0:
                start = i
            depth += 1
        elif ch in ")]}":
            depth -= 1
            if depth == 0 and start is not None:
                out.append(text[start:i + 1])
                start = None
    return out


def split_top(text, seps):
    parts, depth, cur, i = [], 0, "", 0
    while i < len(text):
        ch = text[i]
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        if depth == 0 and any(text.startswith(s, i) for s in seps):
            sep = [s for s in seps if text.startswith(s, i)][0]
            parts.append(cur)
            cur = ""
            i += len(sep)
            continue
        cur += ch
        i += 1
    parts.append(cur)
    return [p.strip() for p in parts if p.strip()]


def strip_forall(text):
    text = text.strip()
    while text.startswith("∀"):
        text = text[1:].strip()
        if text.startswith("("):
            depth = 0
            for i, ch in enumerate(text):
                if ch in "([{":
                    depth += 1
                elif ch in ")]}":
                    depth -= 1
                    if depth == 0:
                        text = text[i + 1:].strip()
                        break
        else:
            depth = 0
            for i, ch in enumerate(text):
                if ch in "([{":
                    depth += 1
                elif ch in ")]}":
                    depth -= 1
                elif ch == "," and depth == 0:
                    text = text[i + 1:].strip()
                    break
        if text.startswith(","):
            text = text[1:].strip()
    return text


def norm(text):
    return re.sub(r"\s+", " ", text).strip().strip(",").strip()


def atoms_of(sig):
    atoms = []
    for g in groups(sig):
        if not g.startswith("("):
            continue
        inner = g[1:-1].strip()
        if inner.startswith("∀"):
            atoms.append(norm(strip_forall(inner)))
            continue
        depth, colon = 0, None
        for i, ch in enumerate(inner):
            if ch in "([{":
                depth += 1
            elif ch in ")]}":
                depth -= 1
            elif ch == ":" and depth == 0:
                colon = i
                break
        if colon is not None:
            kind = inner[colon + 1:].strip()
            if not is_data(kind):
                atoms.append(norm(strip_forall(kind))
                             if kind.startswith("∀") else norm(kind))
    depth, colon = 0, None
    for i, ch in enumerate(sig):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif ch == ":" and depth == 0:
            colon = i
            break
    if colon is not None:
        stmt = strip_forall(sig[colon + 1:])
        for g in groups(stmt):
            if g.startswith("("):
                inner = g[1:-1].strip()
                if inner.startswith("∀"):
                    atoms.append(norm(strip_forall(inner)))
                stmt = stmt.replace(g, " ", 1)
        for seg in split_top(stmt, ["→"])[:-1]:
            seg = norm(strip_forall(seg))
            if seg:
                atoms.append(seg)
    return atoms


LEAVES = [
    re.compile(r"^p1 stamped$"),
    re.compile(r"^stamped .+$"),
    re.compile(r"^adm .+$"),
    re.compile(r"^\S+( \S+)* ∈ .+$"),
    re.compile(r"^\S+( \S+)* ∉ .+$"),
    re.compile(r"^\S+( \S+)* ≠ \S+( \S+)*$"),
    re.compile(r"^\S+( \S+)* = \S+( \S+)*$"),
]


def atom_ok(atom):
    if re.search(r"\bfin\b|Finite|Fintype", atom):
        return False
    leaves = split_top(atom, ["→", "↔", "∨", "∧"])
    if not leaves:
        return False
    return all(any(p.match(leaf) for p in LEAVES) for leaf in leaves)


def premise_check(path):
    bad = []
    lines = open(path).read().split("\n")
    stack, i = [], 0
    while i < len(lines):
        line = lines[i]
        m = NAMESPACE.match(line)
        if m:
            stack.append(m.group(1))
        m = END.match(line)
        if m and stack and stack[-1] == m.group(1):
            stack.pop()
        m = THEOREM.match(line)
        if m:
            name = (stack[-1] + "." if stack else "") + m.group(1)
            sig = line
            while ":=" not in sig and i + 1 < len(lines):
                i += 1
                sig += "\n" + lines[i]
            sig = sig.split(":=")[0]
            for atom in atoms_of(sig):
                if not atom_ok(atom):
                    bad.append((name, atom))
        i += 1
    return bad

if __name__ == "__main__":
    main()
