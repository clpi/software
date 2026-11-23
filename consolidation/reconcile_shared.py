#!/usr/bin/env python3
"""Reconcile byte-identical copies across theses into one shared file each.

Usage: reconcile_shared.py REPO   (a working tree of the consolidated repo, on main)
Every blob that appears at 2+ paths under theses/ in 2+ theses is stored once under shared/
(or the root lean-toolchain), and each old path becomes a relative symlink to it. The old
path still exists and still reads the same bytes. Skipped: .gitignore (git does not follow
symlinked .gitignore) and empty files. Writes consolidation/shared.tsv (blob, shared path,
every linked path).
"""
import os, subprocess, collections, sys
repo = sys.argv[1]
def git(*a): return subprocess.run(['git', '-C', repo, *a], capture_output=True, text=True, check=True).stdout
rows = []
for line in git('ls-tree', '-r', 'HEAD', 'theses').splitlines():
    meta, path = line.split('\t', 1); mode, typ, blob = meta.split()
    if typ == 'blob' and mode in ('100644', '100755'): rows.append((blob, mode, path))
groups = collections.defaultdict(list)
for blob, mode, path in rows: groups[blob].append((mode, path))
NAMES = {  # readable homes for the shared copies, by blob prefix
    '05949028': 'shared/gates/proof-check.sh',            # family Lean gate, 8 theses
    '2f50f934': 'shared/gates/proof-check-solver.sh',     # checking-is-choral, qualification-is-two-sided
    '60c22e66': 'shared/gates/lake-check.sh',             # doesnt-have-to-regress, is-composable, is-incrementally-certifiable
    '9fe15703': 'shared/gates/twin-check.sh',             # estate-is-censused, proofs-are-portable
    'ffbb480c': 'shared/incremental/gate.py',             # incremental gate, 4 engines
}
for b, n in [('340e8b7f', 'frontier.py'), ('dc9f65cf', 'fuzz_s1.py')]: NAMES[b] = 'shared/incremental/' + n
EMPTY = 'e69de29bb2d1d6434b8b29ae775ad8c2d48c5391'
chosen = {}
pinned = []
for blob, ps in groups.items():
    theses = {p.split('/')[1] for _, p in ps}
    base = os.path.basename(ps[0][1])
    if len(theses) < 2 or blob == EMPTY or base == '.gitignore': continue
    if base.endswith('.lean'):
        # Lake refuses a module whose real path lies outside its package root, so Lean
        # copies stay as files; consolidation/check-copies.py fails if any copy drifts.
        pinned.append((blob, ' '.join(p for _, p in ps))); continue
    chosen[blob] = ps
bybase = collections.Counter(os.path.basename(ps[0][1]) for ps in chosen.values())
out = []
for blob, ps in sorted(chosen.items(), key=lambda kv: kv[1][0][1]):
    base = os.path.basename(ps[0][1])
    if base == 'lean-toolchain':
        target = 'lean-toolchain'
        if open(os.path.join(repo, target), 'rb').read() != open(os.path.join(repo, ps[0][1]), 'rb').read():
            raise SystemExit('root lean-toolchain differs')
    else:
        target = NAMES.get(blob[:8])
        if not target:
            sub = 'lean' if base.endswith('.lean') else 'gates' if base.endswith(('.sh', '.py')) else 'data'
            name = base if bybase[base] == 1 else f'{blob[:8]}-{base}'
            target = f'shared/{sub}/{name}'
        os.makedirs(os.path.join(repo, os.path.dirname(target)), exist_ok=True)
        data = open(os.path.join(repo, ps[0][1]), 'rb').read()
        open(os.path.join(repo, target), 'wb').write(data)
        if any(m == '100755' for m, _ in ps): os.chmod(os.path.join(repo, target), 0o755)
    for mode, p in ps:
        full = os.path.join(repo, p)
        rel = os.path.relpath(os.path.join(repo, target), os.path.dirname(full))
        os.remove(full); os.symlink(rel, full)
    out.append((blob, target, ' '.join(p for _, p in ps)))
with open(os.path.join(repo, 'consolidation/shared.tsv'), 'w') as f:
    f.write('blob\tshared_path\tlinked_paths\n')
    for r in out: f.write('\t'.join(r) + '\n')
with open(os.path.join(repo, 'consolidation/copies.tsv'), 'w') as f:
    f.write('blob\tpaths_that_must_stay_identical\n')
    for r in sorted(pinned, key=lambda r: r[1]): f.write('\t'.join(r) + '\n')
print(len(pinned), 'Lean copy groups pinned identical;', len(out), 'shared files;', sum(len(r[2].split()) for r in out), 'paths now symlinks')
