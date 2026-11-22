#!/usr/bin/env python3
"""Escape scan over every tracked .lean file.

Strips comments (nested /- -/, doc comments, --) and string literals, then looks
for tokens that skip or weaken the kernel check, end a file early, or switch off
warnings. A hit fails unless gate/allow.txt lists the exact file and token with a
reason. Usage: escape_scan.py FILE...
"""
import re
import sys

TOKENS = [
    "sorry", "admit", "native_decide", "decide!", "implemented_by", "extern",
    "unsafe", "opaque", "partial", "axiom", "debug.skipKernelTC", "ofReduceBool",
    "trustCompiler", "csimp", "#exit", "set_option", "run_cmd", "run_tac",
    "elab", "elab_rules", "macro", "macro_rules", "syntax", "initialize",
    "builtin_initialize",
]
PAT = re.compile(
    r"(?<![\w.'#!?])(" + "|".join(re.escape(t) for t in TOKENS) + r")(?![\w'!?])"
)


def strip(src):
    out, i, n, depth = [], 0, len(src), 0
    while i < n:
        if depth:
            if src.startswith("/-", i):
                depth += 1
                i += 2
            elif src.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                out.append("\n" if src[i] == "\n" else " ")
                i += 1
        elif src.startswith("/-", i):
            depth = 1
            i += 2
        elif src.startswith("--", i):
            while i < n and src[i] != "\n":
                i += 1
        elif src[i] == '"':
            i += 1
            while i < n and src[i] != '"':
                i += 2 if src[i] == "\\" else 1
            i += 1
            out.append('""')
        elif src[i] == "'" and i + 2 < n and src[i + 2] == "'":
            out.append("' '")
            i += 3
        else:
            out.append(src[i])
            i += 1
    if depth:
        raise SystemExit("unterminated block comment")
    return "".join(out)


def main(files):
    allow = {}
    with open("gate/allow.txt") as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            path, token, reason = (x.strip() for x in line.split("|", 2))
            allow[(path, token)] = reason
    used, hits = set(), []
    for path in files:
        with open(path, encoding="utf-8") as f:
            code = strip(f.read())
        for ln, text in enumerate(code.splitlines(), 1):
            for m in PAT.finditer(text):
                key = (path, m.group(1))
                if key in allow:
                    used.add(key)
                    print(f"allowed  {path}:{ln}: {m.group(1)}  ({allow[key]})")
                else:
                    hits.append(f"{path}:{ln}: {m.group(1)}: {text.strip()}")
    stale = [f"{p} | {t}" for (p, t) in allow if (p, t) not in used]
    for h in hits:
        print("ESCAPE   " + h)
    for s in stale:
        print("STALE    allow.txt entry matches nothing: " + s)
    print(f"escape scan: {len(files)} files, {len(hits)} escapes, {len(stale)} stale allowances")
    return 1 if hits or stale else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
