#!/usr/bin/env python3
"""Point a thesis's Lake requires at the consolidated repo, keeping every pin exact.

Usage: repin.py THESIS_DIR MAPS_DIR MONO_URL
Each `https://github.com/clpi/software-<x>` require (lakefile.lean, lakefile.toml and
lake-manifest.json) becomes MONO_URL @ <rewritten commit of the same pin> / theses/<x>.
The pinned source is byte-identical (the rewritten commit's theses/<x> tree equals the
old commit's tree, checked by verify.py), so no dependency version changes.
"""
import json, re, sys, os
d, maps, url = sys.argv[1:4]
cmap = {}
for f in os.listdir(maps):
    if f.endswith('.commit-map'):
        for l in open(os.path.join(maps, f)).read().split('\n')[1:]:
            if l.strip(): o, n = l.split(); cmap[o] = n
URL = re.compile(r'https://github\.com/clpi/software-([a-z0-9-]+?)(?:\.git)?(?=["\s/]|$)')
changed = []
m = os.path.join(d, 'lake-manifest.json')
if os.path.exists(m):
    j = json.load(open(m))
    for p in j['packages']:
        g = URL.fullmatch(p.get('url', ''))
        if not g: continue
        name = g.group(1)
        p['url'] = url; p['subDir'] = f'theses/{name}'
        p['rev'] = cmap[p['rev']]
        if re.fullmatch(r'[0-9a-f]{40}', p.get('inputRev') or ''): p['inputRev'] = cmap[p['inputRev']]
        changed.append(f'manifest {name}')
    json.dump(j, open(m, 'w'), indent=1); open(m, 'a').write('\n')
lf = os.path.join(d, 'lakefile.lean')
if os.path.exists(lf):
    t = open(lf).read()
    def sub(mm):
        name = mm.group(1); rev = mm.group(2)
        changed.append(f'lakefile.lean {name}')
        return f'from git\n  "{url}" @ "{cmap.get(rev, rev)}" / "theses/{name}"'
    t = re.sub(r'from git\s*"https://github\.com/clpi/software-([a-z0-9-]+)(?:\.git)?"\s*@\s*"([0-9a-f]{40})"', sub, t)
    open(lf, 'w').write(t)
lt = os.path.join(d, 'lakefile.toml')
if os.path.exists(lt):
    t = open(lt).read()
    blocks = t.split('[[require]]')
    for i, b in enumerate(blocks[1:], 1):
        g = URL.search(b)
        if not g: continue
        name = g.group(1)
        b = URL.sub(url, b)
        b = re.sub(r'rev\s*=\s*"([0-9a-f]{40})"', lambda mm: f'rev = "{cmap.get(mm.group(1), mm.group(1))}"', b)
        if 'subDir' not in b: b = b.rstrip('\n') + f'\nsubDir = "theses/{name}"\n\n'
        blocks[i] = b; changed.append(f'lakefile.toml {name}')
    open(lt, 'w').write('[[require]]'.join(blocks))
print('\n'.join(changed) or 'nothing to repin')
