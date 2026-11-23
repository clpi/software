#!/usr/bin/env python3
"""Gate for shared/core: build SoftwareCore, then build every bridge against the real
thesis module it names (compiled from the thesis's own source, never a copy) and check
the axioms of every bridge theorem. Exit 1 on any failure.

Each bridge's first line names its variant:  -- variant: <dir under repo root> <Module>
"""
import os, re, subprocess, sys, tempfile, shutil
HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.normpath(os.path.join(HERE, '..', '..'))
LEAN = os.environ.get('LEAN', 'lean')
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
ESC = re.compile(r'(^|[^\w])(sorry|admit|axiom|native_decide|implemented_by|extern|unsafe|opaque|partial)([^\w]|$)')
fails = 0
def run(cmd, env=None, cwd=None):
    r = subprocess.run(cmd, capture_output=True, text=True, env=env, cwd=cwd)
    return r.returncode, r.stdout + r.stderr
# 1. escapes in the core and the bridges (comments stripped)
for root, _, fs in os.walk(HERE):
    if '.lake' in root: continue
    for f in fs:
        if f.endswith('.lean'):
            t = open(os.path.join(root, f)).read()
            t = re.sub(r'/-.*?-/', '', t, flags=re.S); t = re.sub(r'--[^\n]*', '', t)
            for i, l in enumerate(t.split('\n')):
                if ESC.search(l): print(f'ESCAPE {f}:{i+1}: {l.strip()}'); fails += 1
# 2. the core library
rc, out = run(['lake', 'build'], cwd=HERE)
print('SoftwareCore build:', 'ok' if rc == 0 else 'FAIL')
if rc: print(out[-2000:]); sys.exit(1)
core = os.path.join(HERE, '.lake', 'build', 'lib', 'lean')
# 3. bridges
def compile_module(root, mod, out, done):
    if mod in done: return True
    src = os.path.join(root, *mod.split('.')) + '.lean'
    if not os.path.exists(src): return True  # toolchain module (Init, Std, Lean)
    for imp in re.findall(r'^import\s+(\S+)', open(src).read(), re.M):
        if not compile_module(root, imp, out, done): return False
    olean = os.path.join(out, *mod.split('.')) + '.olean'
    os.makedirs(os.path.dirname(olean), exist_ok=True)
    env = dict(os.environ, LEAN_PATH=out)
    rc, o = run([LEAN, '-R', root, '-o', olean, src], env=env)
    if rc: print(f'  variant {mod} failed to compile:\n{o[-1500:]}'); return False
    done.add(mod); return True
bridges = sorted(f for f in os.listdir(os.path.join(HERE, 'bridges')) if f.endswith('.lean'))
nthm = 0
for b in bridges:
    path = os.path.join(HERE, 'bridges', b)
    text = open(path).read()
    m = re.match(r'-- variant: (\S+) (\S+)', text)
    if not m: print(f'FAIL {b}: no variant line'); fails += 1; continue
    vroot, vmod = os.path.join(REPO, m.group(1)), m.group(2)
    with tempfile.TemporaryDirectory() as out:
        if not compile_module(vroot, vmod, out, set()): print(f'FAIL {b}'); fails += 1; continue
        env = dict(os.environ, LEAN_PATH=f'{core}:{out}')
        bmod = 'Bridge' + b[:-5]
        bolean = os.path.join(out, bmod + '.olean')
        tmpsrc = os.path.join(out, bmod + '.lean'); shutil.copy(path, tmpsrc)
        rc, o = run([LEAN, '-DwarningAsError=true', '-R', out, '-o', bolean, tmpsrc], env=env)
        if rc: print(f'FAIL {b}:\n{o[-2500:]}'); fails += 1; continue
        ns = re.search(r'^namespace (\S+)', text, re.M).group(1)
        thms = re.findall(r'^theorem (\S+)', text, re.M)
        probe = os.path.join(out, 'Probe.lean')
        open(probe, 'w').write(f'import {bmod}\n' + ''.join(f'#print axioms {ns}.{t}\n' for t in thms))
        rc, o = run([LEAN, probe], env=env)
        axs = set()
        for line in o.splitlines():
            mm = re.search(r'depends on axioms: \[(.*)\]', line)
            if mm: axs |= {a.strip() for a in mm.group(1).split(',')}
        bad = axs - ALLOWED
        if rc or bad or o.count("axioms") < len(thms):
            print(f'FAIL {b}: axioms {sorted(axs)} rc={rc}\n{o[-800:]}'); fails += 1; continue
        nthm += len(thms)
        print(f'ok   {b:28s} {len(thms)} theorem(s) against {m.group(1)}:{vmod}; axioms {sorted(axs) or "none"}')
print(f'bridges: {len(bridges)} files, {nthm} equivalence theorems, failures {fails}')
sys.exit(1 if fails else 0)
