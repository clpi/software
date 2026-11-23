#!/usr/bin/env python3
"""Bind the statement's imported definitions to their declared source pins."""

import hashlib
import json
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
LOCK = json.loads((ROOT / "imports.lock.json").read_text())


def git(path, *args):
    return subprocess.check_output(["git", *args], cwd=path, text=True).strip()


def check_package(package, name, expected):
    manifest = json.loads((package / "lake-manifest.json").read_text())
    matches = [entry for entry in manifest["packages"]
               if entry["name"].strip("«»") == name]
    if len(matches) != 1 or matches[0]["rev"] != expected:
        sys.exit("dependency manifest mismatch: " + name)
    path = package / manifest["packagesDir"] / name
    if git(path, "rev-parse", "HEAD") != expected:
        sys.exit("dependency checkout mismatch: " + name)
    changed = subprocess.run(["git", "diff", "--quiet", "HEAD", "--", "."], cwd=path)
    if changed.returncode != 0:
        sys.exit("modified dependency sources: " + name)
    untracked = git(path, "ls-files", "--others", "--exclude-standard")
    if untracked:
        sys.exit("untracked dependency files: " + name)
    return path


for item in LOCK["imports"]:
    name = item["repository"].split("/")[-1]
    path = check_package(ROOT / "statement", name, item["pin"])
    for source in item["files"]:
        data = (path / source["path"]).read_bytes()
        blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        if blob != source["git_blob"] or hashlib.sha256(data).hexdigest() != source["sha256"]:
            sys.exit("import content mismatch: " + name + "/" + source["path"])
    print("IMPORT PIN VERIFIED", item["repository"], item["pin"], len(item["files"]), "files")

check_package(ROOT, "software-is-composable", LOCK["legacy"]["composable"])
check_package(ROOT, "software-is-quantifiable", LOCK["legacy"]["quantifiable"])
print("LEGACY PINS VERIFIED; statement and legacy environments remain distinct")
