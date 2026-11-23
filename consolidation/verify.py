#!/usr/bin/env python3
"""Prove the consolidated repo loses nothing from the old clpi/software-* repos.

Usage: verify.py SRC_DIR MONO_REPO MAPS_DIR [--manifest OUT.tsv] [--ref import]

SRC_DIR   one full clone per old repo (all remote branches, PR heads under refs/pr/*, tags)
MONO_REPO the consolidated git repo built by build.sh
MAPS_DIR  build.sh's maps/ (commit maps, imports.txt)

Checks, all by git object hash (a tree hash equal means every path, mode and byte is equal):
 1. every commit reachable from any old ref has a mapped commit in MONO whose
    theses/<name> tree equals the old commit's root tree, with the same author,
    author date and message;
 2. every old branch, PR head and tag has a MONO ref pointing at the mapped commit;
 3. main:theses/<name> equals the old default-branch tree, for every repo;
 4. main has nothing outside theses/ except the listed top-level files;
 5. an inventory (every file, every Lean theorem/lemma name, every gate script,
    every receipt file) maps old repo:path -> MONO path and is re-derived from MONO.
Exits non-zero on any miss.
"""
import os, re, subprocess, sys, collections

def git(repo, *a, check=True):
    r = subprocess.run(['git', '-C', repo, *a], capture_output=True, text=True)
    if check and r.returncode:
        raise SystemExit(f'git {a} in {repo}: {r.stderr}')
    return r.stdout

SRC, MONO, MAPS = sys.argv[1:4]
manifest = sys.argv[sys.argv.index('--manifest') + 1] if '--manifest' in sys.argv else None
# The import snapshot: the commit tagged `import` once reconcile commits sit on main.
REF = sys.argv[sys.argv.index('--ref') + 1] if '--ref' in sys.argv else 'main'
ALLOWED_TOP = {'theses', 'shared', 'CONCEPTS.md', 'README.md', 'CONSOLIDATION.md', 'lean-toolchain', 'consolidation', '.gitignore', 'run-gates.sh'}
fail = collections.Counter(); ok = collections.Counter()
def bad(kind, msg):
    fail[kind] += 1
    if fail[kind] <= 5: print('FAIL', kind, msg)

imports = {l.split()[0]: (l.split()[1], l.split()[2]) for l in open(os.path.join(MAPS, 'imports.txt'))}
mono_refs = dict(reversed(l.split()) for l in git(MONO, 'for-each-ref', '--format=%(objectname) %(refname)').splitlines())
LEAN_THM = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)*(theorem|lemma)\s+([^\s:({\[]+)', re.M)
GATE = re.compile(r'(^|/)(check|run|verify|replay|gate)[^/]*\.(sh|py)$|(^|/)lakefile\.(lean|toml)$')
RECEIPT = re.compile(r'(?i)(receipt|SHA256SUMS|CHECK[^/]*\.log$|\.log$|evidence/|verification\.txt$)')
inv = []
dirs = sorted(os.listdir(SRC))
if len(dirs) != len(imports): bad('repo-count', f'{len(dirs)} clones vs {len(imports)} imports')
for d in dirs:
    name = d[len('software-'):] if d.startswith('software-') else d
    src = os.path.join(SRC, d)
    if name not in imports: bad('import', f'{name} not imported'); continue
    cmap = {}
    for l in open(os.path.join(MAPS, f'{name}.commit-map')).read().split('\n')[1:]:
        if l.strip(): o, n = l.split(); cmap[o] = n
    # old refs: branches (origin/*), PR heads, tags
    old_refs = {}
    for l in git(src, 'for-each-ref', '--format=%(refname) %(objectname) %(*objectname)', 'refs/remotes/origin', 'refs/pr', 'refs/tags').splitlines():
        p = l.split(); ref, obj = p[0], (p[2] if len(p) > 2 and p[2] else p[1])
        if ref.endswith('/HEAD'): continue
        old_refs[ref] = obj
    # 1. every reachable commit
    commits = git(src, 'rev-list', *set(old_refs.values())).split() if old_refs else []
    meta_old = {}
    fmt = '%H%x00%T%x00%an%x00%ae%x00%aI%x00%B%x1e'
    for rec in git(src, 'log', '--no-walk=unsorted', f'--format={fmt}', *commits).split('\x1e') if commits else []:
        rec = rec.strip('\n')
        if rec: h, t, an, ae, ad, msg = rec.split('\x00', 5); meta_old[h] = (t, an, ae, ad, msg.strip())
    newcs = [cmap.get(c) for c in commits]
    missing = [c for c, n in zip(commits, newcs) if not n or n == '0' * 40]
    for c in missing: bad('commit-unmapped', f'{name} {c}')
    present = [n for n in newcs if n and n != '0' * 40]
    meta_new = {}
    if present:
        fmtn = '%H%x00%an%x00%ae%x00%aI%x00%B%x1e'
        for rec in git(MONO, 'log', '--no-walk=unsorted', f'--format={fmtn}', *present).split('\x1e'):
            rec = rec.strip('\n')
            if rec: h, an, ae, ad, msg = rec.split('\x00', 4); meta_new[h] = (an, ae, ad, msg.strip())
        trees = git(MONO, 'rev-parse', *[f'{n}:theses/{name}' for n in present], check=False).split()
        tmap = dict(zip(present, trees))
    for c in commits:
        n = cmap.get(c)
        if not n or n == '0' * 40: continue
        t, an, ae, ad, msg = meta_old[c]
        if tmap.get(n) != t: bad('commit-tree', f'{name} {c[:10]} -> {n[:10]}')
        elif meta_new.get(n) != (an, ae, ad, msg): bad('commit-meta', f'{name} {c[:10]}')
        else: ok['commits'] += 1
    # 2. every ref
    for ref, obj in old_refs.items():
        if ref.startswith('refs/remotes/origin/'): nref = f'refs/heads/archive/{name}/' + ref[len('refs/remotes/origin/'):]
        elif ref.startswith('refs/pr/'): nref = f'refs/heads/archive/{name}/pr/' + ref[len('refs/pr/'):]
        else: nref = f'refs/tags/{name}/' + ref[len('refs/tags/'):]
        got = mono_refs.get(nref)
        if got and nref.startswith('refs/tags/'): got = git(MONO, 'rev-parse', got + '^{commit}').strip()
        if got != cmap.get(obj): bad('ref', f'{name} {ref} -> {nref}')
        else: ok['refs'] += 1
    # 3. main tree
    defb, defsha = imports[name]
    old_tree = git(src, 'rev-parse', defsha + '^{tree}').strip()
    new_tree = git(MONO, 'rev-parse', f'{REF}:theses/{name}', check=False).strip()
    if old_tree != new_tree: bad('main-tree', name)
    else: ok['main-trees'] += 1
    # 5. inventory at default HEAD, re-derived from MONO bytes
    for line in git(src, 'ls-tree', '-r', defsha).splitlines():
        meta, path = line.split('\t', 1); mode, typ, blob = meta.split()
        npath = f'theses/{name}/{path}'
        nblob = git(MONO, 'rev-parse', f'{REF}:{npath}', check=False).strip()
        if nblob != blob: bad('file', f'{name}:{path}'); continue
        ok['files'] += 1
        kind = 'gate' if GATE.search(path) else 'receipt' if RECEIPT.search(path) else 'file'
        inv.append((name, path, npath, blob, kind, ''))
        if path.endswith('.lean') and typ == 'blob':
            text = git(MONO, 'cat-file', 'blob', nblob)
            text = re.sub(r'/-.*?-/', '', text, flags=re.S)
            for m in LEAN_THM.finditer(text):
                inv.append((name, path, npath, blob, m.group(1), m.group(2))); ok['theorems'] += 1
        if kind != 'file': ok[kind + 's'] += 1
# 4. nothing extra at top
for line in git(MONO, 'ls-tree', REF).splitlines():
    top = line.split('\t', 1)[1]
    if top not in ALLOWED_TOP: bad('top-level', top)
    elif top != 'theses': ok['top-level-added'] += 1
if manifest:
    with open(manifest, 'w') as f:
        f.write('repo\told_path\tnew_path\tblob\tkind\tdecl\n')
        for r in inv: f.write('\t'.join(r) + '\n')
print('OK  ', dict(ok))
print('FAIL', dict(fail) if fail else 'none')
sys.exit(1 if fail else 0)
