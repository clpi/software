#!/usr/bin/env python3
"""Prove the reconcile commits after the import lose nothing.

Usage: reconcile-audit.py REPO IMPORT_REF [HEAD_REF]
Every path under theses/ at IMPORT_REF must still exist at HEAD_REF and read the same bytes,
following in-repo symlinks, except Lake dependency config (lakefile.lean, lakefile.toml,
lake-manifest.json), whose diffs are printed in full for review. Nothing may be deleted.
"""
import subprocess, sys, posixpath
repo, base = sys.argv[1], sys.argv[2]; head = sys.argv[3] if len(sys.argv) > 3 else 'HEAD'
def git(*a): return subprocess.run(['git', '-C', repo, *a], capture_output=True, text=True, check=True).stdout
def tree(ref):
    t = {}
    for l in git('ls-tree', '-r', '-z', ref).split('\0'):
        if not l: continue
        meta, path = l.split('\t', 1); mode, typ, blob = meta.split(); t[path] = (mode, blob)
    return t
B, H = tree(base), tree(head)
def resolve(path, depth=0):
    mode, blob = H[path]
    if mode != '120000': return blob
    tgt = posixpath.normpath(posixpath.join(posixpath.dirname(path), git('cat-file', 'blob', blob)))
    if tgt not in H or depth > 8: return None
    return resolve(tgt, depth + 1)
LAKE = ('lakefile.lean', 'lakefile.toml', 'lake-manifest.json')
same = linked = lake = 0; bad = []
for p, (mode, blob) in B.items():
    if not p.startswith('theses/'): continue
    if p not in H: bad.append(f'deleted {p}'); continue
    if H[p] == (mode, blob): same += 1; continue
    if posixpath.basename(p) in LAKE: lake += 1; continue
    if H[p][0] == '120000' and resolve(p) == blob: linked += 1; continue
    bad.append(f'changed {p}')
print(f'unchanged {same}, now symlinks to identical bytes {linked}, Lake config edited {lake}, problems {len(bad)}')
for b in bad[:20]: print('FAIL', b)
if lake:
    print(git('diff', base, head, '--', *[f':(glob)theses/**/{n}' for n in LAKE]))
sys.exit(1 if bad else 0)
