#!/usr/bin/env python3
"""Mechanical platform audit for the traceability proof.

Enumerates every definition and theorem statement in the proof
modules by asking the Lean kernel checker to print each type
(#check), then scans that printed statement list against a fixed
word list of platform, language, program and mechanism names.
Zero hits is the pass condition. Rerunnable:

    LEAN=/path/to/lean python3 platform-audit.py

Writes PLATFORM-AUDIT.log beside this script and exits nonzero
on any hit or tooling failure.
"""
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

from audit import compile_sources, run_lean

HERE = os.path.dirname(os.path.abspath(__file__))
MODULES = sorted(path.name for path in Path(HERE).glob("*.lean"))

WORDS = [
    "linux", "windows", "macos", "darwin", "freebsd", "openbsd",
    "unix", "posix", "kernel", "syscall", "syscalls",
    "operating", "idol", "zig", "python", "rust", "java",
    "javascript", "typescript", "haskell", "ocaml", "golang",
    "swift", "kotlin", "scala", "perl", "ruby", "lua",
    "cpu", "gpu", "x86", "arm64", "socket", "sockets",
    "thread", "threads", "process", "processes", "pid",
    "driver", "drivers", "hardware", "bytecode", "compiler",
    "interpreter", "shell", "disk", "heap", "pointer",
    "binary", "executable", "machine",
]


def statements(path):
    """Names declared by theorem/lemma/def/structure/inductive at top
    level of the module, with the module namespace."""
    text = open(path).read()
    ns = re.search(r"^namespace\s+(\w+)", text, re.M).group(1)
    names = re.findall(
        r"^(?:theorem|lemma|def|structure|inductive)\s+(\w+)", text, re.M)
    return ns, names


def main():
    lean = os.environ.get("LEAN", "lean")
    lines = []
    all_names = []
    gen = ["import %s" % mod[:-5] for mod in MODULES]
    for mod in MODULES:
        ns, names = statements(os.path.join(HERE, mod))
        for n in names:
            gen.append("#check @%s.%s" % (ns, n))
            all_names.append("%s.%s" % (ns, n))
    lines.append("Statement enumeration: %d statements" % len(all_names))
    for n in all_names:
        lines.append("  statement %s" % n)
    with tempfile.TemporaryDirectory() as td:
        build = Path(td)
        genfile = os.path.join(td, "audit-print.lean")
        open(genfile, "w").write("\n".join(gen) + "\n")
        # Compile from a fresh snapshot, including new control modules.
        # Neither repository oleans nor an inherited LEAN_PATH are trusted.
        compile_sources(lean, [Path(HERE) / mod for mod in MODULES], build, lambda _: None)
        proc = run_lean(lean, ["-DwarningAsError=true", genfile], build)
    if proc.returncode != 0:
        lines.append("AUDIT TOOLING FAILURE")
        lines.append(proc.stdout)
        lines.append(proc.stderr)
        open(os.path.join(HERE, "PLATFORM-AUDIT.log"), "w").write(
            "\n".join(lines) + "\n")
        print("\n".join(lines))
        return 1
    printed = proc.stdout
    lines.append("Printed statements (kernel checker output):")
    lines.append(printed.rstrip())
    pattern = re.compile(
        r"\b(" + "|".join(re.escape(w) for w in WORDS) + r")\b",
        re.IGNORECASE)
    hits = pattern.findall(printed)
    lines.append("Word list (%d words): %s" % (len(WORDS), ", ".join(WORDS)))
    lines.append("Hits: %d" % len(hits))
    if hits:
        lines.append("Hit words: %s" % ", ".join(sorted(set(hits))))
    lines.append("Platform audit: %s" % ("FAIL" if hits else "PASS"))
    out = "\n".join(lines) + "\n"
    open(os.path.join(HERE, "PLATFORM-AUDIT.log"), "w").write(out)
    print(out)
    return 1 if hits else 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, RuntimeError, subprocess.SubprocessError) as error:
        output = f"AUDIT TOOLING FAILURE\n{error}\nPlatform audit: FAIL\n"
        Path(HERE, "PLATFORM-AUDIT.log").write_text(output)
        print(output, end="")
        sys.exit(1)
