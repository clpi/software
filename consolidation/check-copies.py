#!/usr/bin/env python3
"""Fail if any reconciled copy drifts. Usage: check-copies.py [REPO]
consolidation/shared.tsv: every linked path must be a symlink resolving to its shared file.
consolidation/copies.tsv: every listed path (Lean files Lake cannot symlink) must hold the same bytes.
"""
import os, sys, hashlib
repo = sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(__file__), '..')
bad = 0
def h(p): return hashlib.sha256(open(p, 'rb').read()).hexdigest()
for line in open(os.path.join(repo, 'consolidation/shared.tsv')).read().splitlines()[1:]:
    blob, target, paths = line.split('\t')
    t = os.path.realpath(os.path.join(repo, target))
    for p in paths.split():
        f = os.path.join(repo, p)
        if not os.path.islink(f) or os.path.realpath(f) != t: print('DRIFT (not linked to shared):', p); bad += 1
for line in open(os.path.join(repo, 'consolidation/copies.tsv')).read().splitlines()[1:]:
    blob, paths = line.split('\t'); ps = paths.split()
    hs = {h(os.path.join(repo, p)) for p in ps}
    if len(hs) != 1: print('DRIFT (copies differ):', ps); bad += 1
print('copies: OK' if not bad else f'copies: {bad} drifted'); sys.exit(1 if bad else 0)
