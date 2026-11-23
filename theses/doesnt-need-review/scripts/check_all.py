#!/usr/bin/env python3
"""Discover, check, and axiom-audit every Lean source in this repository.

The two Lake packages deliberately keep different upstream module identities.
Each file is checked in its nearest package, including otherwise unimported files.
This gate trusts Lean, Python, the operating system, and the gate itself. It is not
a sandbox for hostile metaprograms and does not establish real-world fidelity.
"""

from __future__ import annotations

import argparse
import hashlib
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[1]
AUDITOR = ROOT / "scripts" / "AuditAll.lean"
EXCLUDED = {".git", ".lake", "__pycache__"}
FORBIDDEN = re.compile(
    r"(?<![A-Za-z0-9_])"
    r"(sorry|admit|axiom|sorryAx|native_decide|unsafe|implemented_by|extern)"
    r"(?![A-Za-z0-9_])"
)
WEAKENING = re.compile(
    r"\bset_option\s+(?:warningAsError|linter(?:\.[A-Za-z0-9_]+)*)\s+false\b"
    r"|\bset_option\s+(?:debug\.skipKernelTC|debug\.skipKernelCheck)\s+true\b"
)
AUDIT_MARKER = re.compile(r"^ALL_DECLARATIONS_AUDITED (\d+) IMPLEMENTATION_AUXILIARIES (\d+)$", re.M)


class GateError(RuntimeError):
    pass


def visible_code(text: str) -> str:
    """Erase comments and quoted strings, preserving newlines for diagnostics.

    This conservative scanner understands nested Lean block comments. Elaborated
    kernel declarations are checked separately; scanning is not a Lean parser.
    """
    out = list(text)
    i = 0
    depth = 0
    quoted = False
    line = False
    while i < len(text):
        char = text[i]
        pair = text[i:i + 2]
        if line:
            if char == "\n":
                line = False
            else:
                out[i] = " "
            i += 1
        elif depth:
            if pair == "/-":
                out[i:i + 2] = "  "
                depth += 1
                i += 2
            elif pair == "-/":
                out[i:i + 2] = "  "
                depth -= 1
                i += 2
            else:
                if char != "\n":
                    out[i] = " "
                i += 1
        elif quoted:
            if char == "\\" and i + 1 < len(text):
                out[i] = " "
                if text[i + 1] != "\n":
                    out[i + 1] = " "
                i += 2
            else:
                if char == '"':
                    quoted = False
                if char != "\n":
                    out[i] = " "
                i += 1
        elif pair == "--":
            out[i:i + 2] = "  "
            line = True
            i += 2
        elif pair == "/-":
            out[i:i + 2] = "  "
            depth = 1
            i += 2
        elif char == '"':
            out[i] = " "
            quoted = True
            i += 1
        else:
            i += 1
    return "".join(out)


def scan_source(path: Path, text: str) -> None:
    code = visible_code(text)
    for rule in (FORBIDDEN, WEAKENING):
        match = rule.search(code)
        if match:
            line = code.count("\n", 0, match.start()) + 1
            raise GateError(f"source escape rejected: {path}:{line}: {match.group()}")


def discover(root: Path) -> list[Path]:
    found = []
    for path in root.rglob("*.lean"):
        relative = path.relative_to(root)
        if any(part in EXCLUDED for part in relative.parts):
            continue
        if path.is_symlink() or not path.is_file():
            raise GateError(f"source must be a regular, non-symlink file: {path}")
        found.append(path)
    return sorted(found)


def package_for(path: Path, root: Path) -> Path | None:
    for parent in (path.parent, *path.parent.parents):
        if parent != root and root not in parent.parents:
            break
        if (parent / "lakefile.lean").is_file() or (parent / "lakefile.toml").is_file():
            return parent
    return None


def invoke(command: list[str], cwd: Path, label: str,
           environment: dict[str, str] | None = None) -> str:
    result = subprocess.run(command, cwd=cwd, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, check=False, env=environment)
    output = result.stdout
    if result.returncode != 0 or re.search(r"\bwarning:", output):
        tail = output[-12000:]
        raise GateError(f"{label} failed (exit {result.returncode}):\n{tail}")
    return output


def command_for(package: Path | None) -> list[str]:
    return ["lake", "env", "lean"] if package is not None else ["lean"]


def check_toolchain(package: Path, *, direct: bool = False) -> None:
    """Bind the running binaries to the declared release, including direct PATH use."""
    pin = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
    match = re.fullmatch(r"leanprover/lean4:v(\d+\.\d+\.\d+)", pin)
    if not match or (package / "lean-toolchain").read_text(encoding="utf-8").strip() != pin:
        raise GateError(f"unsupported or inconsistent toolchain pin: {package}")
    version = match.group(1)
    command = ["lean"] if direct else ["lake", "env", "lean"]
    actual = invoke(command + ["--version"], package, "read running Lean version").strip()
    lake = invoke(["lake", "--version"], package, "read running Lake version").strip()
    if not actual.startswith(f"Lean (version {version},") or f"(Lean version {version})" not in lake:
        raise GateError(f"running toolchain differs from {pin}: {actual}; {lake}")
    mode = "PATH" if direct else str(package.relative_to(ROOT))
    print(f"TOOLCHAIN VERIFIED {mode}: {actual}; {lake}", flush=True)


def module_name(relative: Path) -> str:
    parts = relative.with_suffix("").parts
    return ".".join(part if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", part)
                    else "«" + part + "»" for part in parts)


def lean_environment(package: Path | None, cwd: Path) -> tuple[str, dict[str, str]]:
    environment = dict(os.environ)
    if package is None:
        return shutil.which("lean") or "lean", environment
    lean_path = invoke(["lake", "env", "printenv", "LEAN_PATH"], cwd,
                       "resolve package imports").strip()
    prefix = invoke(["lake", "env", "lean", "--print-prefix"], cwd,
                    "resolve pinned Lean executable").strip()
    environment["LEAN_PATH"] = lean_path
    return str(Path(prefix) / "bin" / "lean"), environment


def overlay_imports(destination: Path, lean_path: str, cwd: Path, lean: str) -> None:
    """Merge package module trees: Lean resolves a directory prefix as one root."""
    sysroot = Path(lean).resolve().parents[1] / "lib" / "lean"
    for entry in lean_path.split(os.pathsep):
        if not entry:
            continue
        source = Path(entry)
        if not source.is_absolute():
            source = cwd / source
        source = source.resolve()
        if not source.is_dir() or source == sysroot:
            continue
        for original in source.rglob("*.olean"):
            output = destination / original.relative_to(source)
            if not output.exists():
                output.parent.mkdir(parents=True, exist_ok=True)
                output.symlink_to(original)


def check_file(path: Path, root: Path, temporary: Path, auditor: str,
               *, source_scan: bool = True) -> tuple[int, int]:
    text = path.read_text(encoding="utf-8")
    if source_scan:
        scan_source(path, text)
    package = package_for(path, root)
    cwd = package or root
    lean, environment = lean_environment(package, cwd)
    artifact_root = temporary / hashlib.sha256(str(path).encode()).hexdigest()
    artifact_root.mkdir(exist_ok=True)
    overlay_imports(artifact_root, environment.get("LEAN_PATH", ""), cwd, lean)
    relative = path.relative_to(cwd)
    module = module_name(relative)
    compiled = artifact_root / relative.with_suffix(".olean")
    compiled.parent.mkdir(parents=True, exist_ok=True)
    if compiled.is_symlink():
        compiled.unlink()
    invoke([lean, "-DwarningAsError=true", "--root=" + str(cwd), "-o", str(compiled),
            str(path)], cwd, f"compile {path}", environment)
    # Audit the artifact produced above, without changing its imports or proof
    # search environment. The temporary path precedes every package build path.
    audit_root = temporary / "auditor"
    audit_compiled = audit_root / "scripts" / "AuditAll.olean"
    if not audit_compiled.is_file():
        audit_compiled.parent.mkdir(parents=True, exist_ok=True)
        invoke([lean, "-DwarningAsError=true", "--root=" + str(ROOT), "-o",
                str(audit_compiled), str(AUDITOR)], ROOT, "compile kernel auditor")
    if module != "scripts.AuditAll":
        local_auditor = artifact_root / "scripts" / "AuditAll.olean"
        local_auditor.parent.mkdir(parents=True, exist_ok=True)
        if local_auditor.is_symlink() or local_auditor.exists():
            local_auditor.unlink()
        local_auditor.symlink_to(audit_compiled)
    environment["LEAN_PATH"] = os.pathsep.join(
        [str(artifact_root), str(audit_root), environment.get("LEAN_PATH", "")])
    wrapped = artifact_root / "GateRunner.lean"
    imports = f"import {module}\n"
    if module != "scripts.AuditAll":
        imports += "import scripts.AuditAll\n"
    wrapped.write_text(imports + f"audit_module_declarations {module}\n", encoding="utf-8")
    output = invoke([lean, "-DwarningAsError=true", str(wrapped)], cwd,
                    f"audit {path}", environment)
    matches = AUDIT_MARKER.findall(output)
    if len(matches) != 1:
        raise GateError(f"audit did not emit exactly one coverage marker for {path}:\n{output}")
    if path.read_text(encoding="utf-8") != text:
        raise GateError(f"source changed during gate: {path}")
    return tuple(map(int, matches[0]))


def controls(temporary: Path, auditor: str) -> None:
    control_root = temporary / "controls"
    control_root.mkdir()
    scratch = temporary / "wrapped-controls"
    scratch.mkdir()
    hidden = control_root / "not-imported" / "Hidden.lean"
    hidden.parent.mkdir()
    hidden.write_text("theorem discovered : True := by trivial\n", encoding="utf-8")
    if discover(control_root) != [hidden]:
        raise GateError("unimported-file discovery control failed")
    check_file(hidden, control_root, scratch, auditor)
    print("CONTROL passed: an unimported file is discovered and audited", flush=True)

    rejected_sources = {
        "unimported-compile-error": "theorem broken : False := by trivial\n",
        "warning": "def warned (unused : Nat) : Nat := 0\n",
        "sorry": "theorem gap : False := by sorry\n",
        "admit": "theorem gap : False := by admit\n",
        "custom-axiom": "axiom planted : False\n",
        "native-decide": "theorem native : True := by native_decide\n",
        "unsafe": "unsafe def escape : Nat := 0\n",
        "diagnostic-weakening": "set_option warningAsError false\n",
        "extern": '@[extern "gate_control"] def escape : Nat := 0\n',
        "implemented-by": "@[implemented_by replacement] def escape : Nat := 0\n",
    }
    for name, source in rejected_sources.items():
        hidden.write_text(source, encoding="utf-8")
        try:
            check_file(hidden, control_root, scratch, auditor)
        except GateError:
            print(f"CONTROL rejected: {name}", flush=True)
        else:
            raise GateError(f"negative control unexpectedly passed: {name}")

    # Bypass the textual `axiom` token deliberately: the environment audit must
    # still reject a custom axiom generated by a command elaborator.
    hidden.write_text("""import Lean
open Lean Elab Command
elab "plant_control" : command => do
  liftCoreM <| addDecl (.axiomDecl {
    name := `plantedControl
    levelParams := []
    type := mkConst ``False
    isUnsafe := false })
plant_control
""", encoding="utf-8")
    scan_source(hidden, hidden.read_text())
    invoke(["lean", "-DwarningAsError=true", str(hidden)], control_root,
           "kernel-axiom control must compile before its audit")
    try:
        check_file(hidden, control_root, scratch, auditor)
    except GateError as error:
        if "unapproved kernel axiom plantedControl" not in str(error):
            raise GateError(f"kernel-axiom control failed for the wrong reason: {error}") from error
        print("CONTROL rejected: generated custom axiom at kernel audit", flush=True)
    else:
        raise GateError("generated custom axiom escaped the kernel audit")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--controls-only", action="store_true")
    args = parser.parse_args()
    if not shutil.which("lean") or not shutil.which("lake"):
        raise GateError("lean and lake must be on PATH (the pinned lean-toolchain is authoritative)")
    check_toolchain(ROOT, direct=True)
    auditor = AUDITOR.read_text(encoding="utf-8")
    scan_source(AUDITOR, auditor)
    with tempfile.TemporaryDirectory(prefix="review-all-file-gate-") as temporary_name:
        temporary = Path(temporary_name)
        controls(temporary, auditor)
        if args.controls_only:
            return 0
        files = discover(ROOT)
        if not files:
            raise GateError("no Lean sources discovered")
        snapshots = {p: hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
        for path in files:
            scan_source(path, path.read_text(encoding="utf-8"))
        packages = sorted({package_for(path, ROOT) for path in files} - {None})
        for package in packages:
            check_toolchain(package)
            invoke(["lake", "build"], package, f"build package {package.relative_to(ROOT)}")
        checked = temporary / "wrapped-sources"
        checked.mkdir()
        for path in files:
            count, auxiliary = check_file(path, ROOT, checked, auditor)
            print(f"CHECKED {path.relative_to(ROOT)} declarations={count} "
                  f"compiler_implementation_auxiliaries={auxiliary}", flush=True)
        if discover(ROOT) != files:
            raise GateError("Lean source inventory changed during gate")
        for path, digest in snapshots.items():
            if hashlib.sha256(path.read_bytes()).hexdigest() != digest:
                raise GateError(f"source changed during gate: {path}")
        print(f"ALL-FILE GATE PASSED: {len(files)} Lean sources; "
              f"{len(packages)} isolated packages", flush=True)
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except GateError as failure:
        print(f"REFUSED: {failure}", file=sys.stderr)
        sys.exit(1)
