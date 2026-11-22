#!/usr/bin/env python3
"""Fresh repository-wide Lean compilation and kernel declaration audit.

Every .lean file outside Git's internal directory is copied into a fresh
temporary build. Imports can use this build and the pinned Lean installation,
never a stale repository .olean or an inherited LEAN_PATH. This repository's
modules use their file basenames; duplicate module names fail closed.

The generated auditor enumerates the imported kernel environment by module
origin. It checks all theorem declarations, including generated and private
ones, and prints the axiom dependencies of every theorem. Source #print
commands and textual theorem-name parsing are not coverage authorities.
"""

from pathlib import Path
import hashlib
import os
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent
PROHIBITED = re.compile(
    r"(?<![\w])(sorry|sorryAx|admit|axiom|native_decide|implemented_by|extern|"
    r"unsafe|opaque|partial)(?![\w])|debug\.skipKernelTC"
)
DIAGNOSTIC = re.compile(r"sorryAx|error:|warning:")
MODULE_NAME = re.compile(r"[A-Za-z_][A-Za-z_0-9]*\Z")


def sources():
    return sorted(path for path in ROOT.rglob("*.lean") if ".git" not in path.parts)


def run_lean(lean, arguments, build):
    env = dict(os.environ)
    env["LEAN_PATH"] = str(build)
    return subprocess.run(
        [lean, *arguments], cwd=build, env=env, capture_output=True, text=True
    )


def compile_sources(lean, files, build, emit):
    """Build a snapshot without consulting or changing repository artifacts."""
    modules = []
    for path in files:
        name = path.stem
        if not MODULE_NAME.fullmatch(name) or name in modules:
            raise RuntimeError(f"unsupported or duplicate module basename: {path.relative_to(ROOT)}")
        modules.append(name)
        text = path.read_text()
        if match := PROHIBITED.search(text):
            line = text[:match.start()].count("\n") + 1
            raise RuntimeError(
                f"prohibited proof token {match.group()!r}: {path.relative_to(ROOT)}:{line}"
            )
        (build / path.name).write_text(text)
    pending = list(zip(files, modules))
    while pending:
        next_pass = []
        errors = []
        for path, module in pending:
            proc = run_lean(
                lean,
                ["-DwarningAsError=true", "-o", f"{module}.olean", f"{module}.lean"],
                build,
            )
            output = proc.stdout + proc.stderr
            if proc.returncode or DIAGNOSTIC.search(output):
                next_pass.append((path, module))
                errors.append((path, output))
            else:
                emit(f"Compiled: {path.relative_to(ROOT)}")
                if output:
                    emit(output.rstrip())
        if len(next_pass) == len(pending):
            for path, output in errors:
                emit(f"Failed: {path.relative_to(ROOT)}")
                emit(output.rstrip())
            raise RuntimeError("Lean compilation failed")
        pending = next_pass
    return modules


def auditor(modules):
    imports = "\n".join(f"import {module}" for module in modules)
    module_names = ", ".join("`" + module for module in modules)
    return f'''import Lean
{imports}
open Lean Elab Command
run_elab do
  let env ← getEnv
  let modules : Array Name := #[{module_names}]
  let allowed : Array Name := #[`propext, `Quot.sound]
  let mut theorems : Array Name := #[]
  for (name, info) in env.constants do
    if let some index := env.getModuleIdxFor? name then
      if modules.contains env.header.moduleNames[index]! then
        if info.isTheorem then
          theorems := theorems.push name
  if theorems.isEmpty then
    throwError "Rejected: no repository theorems found"
  let mut used : Array Name := #[]
  for name in theorems.qsort Name.lt do
    let axioms ← collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Rejected: {{name}} depends on forbidden axiom {{ax}}"
      unless used.contains ax do
        used := used.push ax
    if axioms.isEmpty then
      logInfo m!"'{{name}}' does not depend on any axioms"
    else
      logInfo m!"'{{name}}' depends on axioms: {{axioms.qsort Name.lt |>.toList}}"
  logInfo m!"Kernel theorem audit: {{theorems.size}} theorem declarations (including generated declarations)"
  logInfo m!"Axiom subset check passed: every repository theorem uses only {{allowed.toList}}"
  logInfo m!"Axioms printed: {{used.qsort Name.lt |>.toList}}"
'''


def main():
    log = ROOT / "proof" / "CHECK.log"
    lines = []

    def emit(line):
        lines.append(line)

    try:
        lean = os.environ.get("LEAN", "lean")
        if not (lean := shutil.which(lean)):
            raise RuntimeError("Lean executable not found")
        files = sources()
        if not files:
            raise RuntimeError("no Lean sources found")
        version = subprocess.run([lean, "--version"], capture_output=True, text=True, check=True)
        emit(version.stdout.rstrip())
        pin = (ROOT / "proof" / "lean-toolchain").read_text().strip()
        match = re.fullmatch(r"leanprover/lean4:v([0-9.]+)", pin)
        if not match or f"version {match.group(1)}," not in version.stdout:
            raise RuntimeError(f"Lean version does not match {pin}")
        emit(f"Repository Lean files: {len(files)}")
        manifest_files = sorted(set(files + [
            ROOT / "proof" / "check.sh", ROOT / "proof" / "audit.py",
            ROOT / "proof" / "platform-audit.py", ROOT / "proof" / "lean-toolchain",
            ROOT / "examples" / "check.sh", ROOT / "examples" / "range-ledger" / "check.sh",
            ROOT / "examples" / "range-ledger" / "mutation.patch",
        ]))
        emit("Source SHA256 manifest:")
        manifest = []
        for path in manifest_files:
            entry = f"{hashlib.sha256(path.read_bytes()).hexdigest()}  {path.relative_to(ROOT)}"
            manifest.append(entry)
            emit(entry)
        (ROOT / "proof" / "SOURCE-SHA256.txt").write_text("\n".join(manifest) + "\n")
        with tempfile.TemporaryDirectory(prefix="traceability-check-") as temp:
            build = Path(temp)
            modules = compile_sources(lean, files, build, emit)
            (build / "RepositoryAudit.lean").write_text(auditor(modules))
            proc = run_lean(lean, ["-DwarningAsError=true", "RepositoryAudit.lean"], build)
            output = proc.stdout + proc.stderr
            emit(output.rstrip())
            if proc.returncode or DIAGNOSTIC.search(output):
                raise RuntimeError("kernel declaration audit failed")
        emit(f"Gate passed: {len(files)} Lean files, warnings as errors, fresh imports, no prohibited proof tokens")
        status = 0
    except (RuntimeError, OSError, subprocess.SubprocessError) as error:
        emit(f"Rejected: {error}")
        status = 1
    output = "\n".join(lines) + "\n"
    log.write_text(output)
    if status:
        print(output, end="")
    else:
        prefixes = ("Lean (version", "Repository Lean files:", "Compiled:",
                    "Kernel theorem audit:", "Axiom subset check passed:",
                    "Axioms printed:", "Gate passed:")
        for line in output.splitlines():
            if line.startswith(prefixes):
                print(line)
        print("Full proof transcript: proof/CHECK.log")
        print("Checked source hashes: proof/SOURCE-SHA256.txt")
    return status


if __name__ == "__main__":
    sys.exit(main())
