#!/usr/bin/env python3
"""Reconcile Lake dependencies: every require of a sibling clpi/software-<x> becomes a path
require of theses/<x> in this repo, so every thesis builds against the one current version.

Usage: reconcile_deps.py REPO [THESIS_TO_KEEP_PINNED ...]
Rewrites lakefile.lean / lakefile.toml under theses/, then the caller runs `lake update`
(offline: all deps are paths) and `lake build` in each package. Prints what it changed.
"""
import os, re, sys
repo = sys.argv[1]
SKIP = set(sys.argv[2:])  # theses that keep exact pins (see CONSOLIDATION.md)
URL = r'https://github\.com/clpi/software-([a-z0-9-]+?)(?:\.git)?'
changed = []
for root, dirs, files in os.walk(os.path.join(repo, 'theses')):
    dirs[:] = [d for d in dirs if d != '.lake']
    if os.path.relpath(root, os.path.join(repo, 'theses')).split(os.sep)[0] in SKIP: continue
    for f in files:
        p = os.path.join(root, f)
        if f == 'lakefile.lean':
            t = open(p).read()
            def sub(m):
                rel = os.path.relpath(os.path.join(repo, 'theses', m.group(1)), root)
                changed.append(f'{os.path.relpath(p, repo)}: {m.group(1)}'); return f'from "{rel}"'
            t2 = re.sub(r'from git\s*"' + URL + r'"\s*@\s*"[0-9a-f]{40}"', sub, t)
            if t2 != t: open(p, 'w').write(t2)
        elif f == 'lakefile.toml':
            t = open(p).read(); blocks = t.split('[[require]]')
            for i, b in enumerate(blocks[1:], 1):
                m = re.search(r'git\s*=\s*"' + URL + r'"', b)
                if not m: continue
                rel = os.path.relpath(os.path.join(repo, 'theses', m.group(1)), root)
                b = re.sub(r'\n\s*git\s*=\s*"[^"]*"', f'\npath = "{rel}"', b)
                b = re.sub(r'\n\s*rev\s*=\s*"[^"]*"', '', b)
                blocks[i] = b; changed.append(f'{os.path.relpath(p, repo)}: {m.group(1)}')
            t2 = '[[require]]'.join(blocks)
            if t2 != t: open(p, 'w').write(t2)
print('\n'.join(changed))
