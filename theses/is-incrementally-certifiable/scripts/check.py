#!/usr/bin/env python3
"""Compile every repository Lean source and reject unchecked proof assumptions."""
from __future__ import annotations
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / '.lake/all-files-gate'
FORBIDDEN = re.compile(r"(?<![\w'])(?:sorry|admit|axiom|sorryAx|native_decide|unsafe|unsafeCast|ofReduceBool|ofReduceNat|trustCompiler|implemented_by|extern|addDecl|addAndCompile|setEnv|modifyEnv|setOptions|withOptions|run_elab|run_meta|run_cmd)(?![\w'])")
SAFE_OPTIONS = {'autoImplicit', 'maxRecDepth', 'maxHeartbeats', 'pp.universes'}
ALLOWED = ['propext', 'Classical.choice', 'Quot.sound']


def code_only(text):
    """Strip strings and nested comments, preserving line numbers."""
    result = list(text)
    i, depth, string, line = 0, 0, False, False
    while i < len(text):
        pair = text[i:i + 2]
        if line:
            if text[i] == '\n': line = False
            else: result[i] = ' '
            i += 1
        elif depth:
            if pair in ('/-', '-/'):
                depth += 1 if pair == '/-' else -1
                result[i:i + 2] = '  '
                i += 2
            else:
                if text[i] != '\n': result[i] = ' '
                i += 1
        elif string:
            if text[i] == '\\':
                result[i:i + 2] = '  '
                i += 2
            else:
                if text[i] == '"': string = False
                if text[i] != '\n': result[i] = ' '
                i += 1
        elif pair in ('--', '/-'):
            line, depth = pair == '--', int(pair == '/-')
            result[i:i + 2] = '  '
            i += 2
        elif text[i] == '"':
            string, result[i] = True, ' '
            i += 1
        else: i += 1
    return ''.join(result)


def scan(path):
    code = code_only(path.read_text())
    match = FORBIDDEN.search(code)
    if match:
        line = code[:match.start()].count('\n') + 1
        raise RuntimeError(f'proof escape {match.group()} at {path}:{line}')
    for option in re.findall(r'\bset_option\s+(\S+)', code):
        if option not in SAFE_OPTIONS:
            raise RuntimeError(f'unapproved compiler option {option} at {path}')


def inventory(root):
    files = []
    for directory, dirs, names in os.walk(root):
        dirs[:] = sorted(d for d in dirs if not (Path(directory) == root and d in {'.git', '.lake'}))
        for directory_name in dirs:
            if (Path(directory) / directory_name).is_symlink():
                raise RuntimeError(f'symlinked source directory: {Path(directory) / directory_name}')
        for name in sorted(names):
            if name.endswith('.lean'):
                path = Path(directory) / name
                if path.is_symlink(): raise RuntimeError(f'Lean source symlink: {path}')
                files.append(path)
    return sorted(files)


def module(path):
    return '.'.join(p if re.fullmatch(r"[A-Za-z_][A-Za-z_0-9']*", p) else '«' + p + '»'
                    for p in path.relative_to(ROOT).with_suffix('').parts)


def ordered(files):
    modules = {module(p): p for p in files}
    seen, active, result = set(), set(), []
    def visit(name):
        if name in seen: return
        if name in active: raise RuntimeError(f'local import cycle at {name}')
        active.add(name)
        for imported in re.findall(r'^\s*import\s+([^\n]+)', code_only(modules[name].read_text()), re.M):
            for dep in imported.split():
                if dep in modules: visit(dep)
        active.remove(name)
        seen.add(name)
        result.append(modules[name])
    for name in sorted(modules): visit(name)
    return result


def run(args, log, env=None, fail=False):
    done = subprocess.run(args, cwd=ROOT, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (OUT / log).write_text(done.stdout)
    if fail:
        if done.returncode == 0 or 'error:' not in done.stdout:
            raise RuntimeError(f'negative control did not fail for a Lean error: {args}; see {log}')
    elif done.returncode:
        raise RuntimeError(f'command failed: {args}; see {OUT / log}\n{done.stdout[-6000:]}')
    return done.stdout


def audit_source(modules):
    imports = '\n'.join('import ' + n for n in modules)
    own = ', '.join('`' + n for n in modules)
    allowed = ', '.join('`' + n for n in ALLOWED)
    return imports + '\nimport Lean\n' + f'''
open Lean Elab Command
elab "audit_all_repository_proofs" : command => do
  let env ← getEnv
  let own : List Name := [{own}]
  let allowed : List Name := [{allowed}]
  let mut count := 0
  let mut runtimeCount := 0
  let mut names : Array Name := #[]
  for (name, _) in env.constants.map₁.toList ++ env.constants.map₂.toList do
    if let some idx := env.getModuleIdxFor? name then
      if own.contains env.header.moduleNames[idx.toNat]! then
        names := names.push name
  for name in names.qsort (fun a b => a.toString < b.toString) do
    let some info := env.find? name | throwError "declaration disappeared: {{name}}"
    if let .axiomInfo ax := info then
      if ax.isUnsafe then
        let logical ← try liftTermElabM (Lean.Meta.isProp ax.type) catch _ => pure false
        if logical then throwError "unsafe proposition axiom: {{name}}"
        runtimeCount := runtimeCount + 1
        IO.println s!"UNSAFE_RUNTIME {{name}}"
      else
        throwError "custom axiom declaration: {{name}}"
    unless info.isUnsafe do
      if (← liftTermElabM (Lean.Meta.isProp info.type)) then
        let axioms ← collectAxioms name
        for ax in axioms do
          unless allowed.contains ax do
            throwError "prohibited transitive axiom {{ax}} in {{name}}"
        count := count + 1
        IO.println s!"AUDITED {{name}} AXIOMS {{axioms}}"
  if count == 0 then throwError "empty proof audit"
  IO.println s!"AUDIT_TOTAL {{count}}"
  IO.println s!"UNSAFE_RUNTIME_TOTAL {{runtimeCount}}"
audit_all_repository_proofs
'''


def main():
    if len(sys.argv) != 1: raise RuntimeError('check.sh takes no arguments; all checks are mandatory')
    os.chdir(ROOT)
    files = inventory(ROOT)
    if not files: raise RuntimeError('empty Lean inventory')
    hashes = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    for path in files: scan(path)
    inputs = ['check.sh', 'scripts/check.py', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain', 'controls/Admitted.lean.fail']
    input_hashes = {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in inputs}
    if OUT.exists(): shutil.rmtree(OUT)
    OUT.mkdir(parents=True)
    lean = shutil.which(os.environ.get('LEAN', 'lean'))
    if lean is None: raise RuntimeError('Lean not on PATH; set LEAN to pinned executable')
    lake = shutil.which(os.environ.get('LAKE', str(Path(lean).parent / 'lake')))
    if lake is None: raise RuntimeError('Lake not beside Lean; set LAKE')
    version = run([lean, '--version'], 'version.log').strip()
    pin = (ROOT / 'lean-toolchain').read_text().strip().split(':v')[-1]
    if f'version {pin},' not in version and f'version {pin} ' not in version:
        raise RuntimeError(f'Lean version mismatch: {version}; expected {pin}')
    base_env = os.environ.copy()
    base_env['PATH'] = str(Path(lean).parent) + os.pathsep + base_env['PATH']
    dependencies = []
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    for dependency in manifest['packages']:
        name = dependency['name'].strip('«»')
        directory = ROOT / manifest['packagesDir'] / name
        if dependency['type'] != 'git' or not re.fullmatch('[0-9a-f]{40}', dependency['rev']):
            raise RuntimeError(f'dependency must have an immutable Git pin: {name}')
        if not directory.exists():
            directory.parent.mkdir(parents=True, exist_ok=True)
            run(['git', 'clone', '--no-checkout', dependency['url'], str(directory)], f'fetch-{name}.log', base_env)
            run(['git', '-C', str(directory), 'checkout', '--detach', dependency['rev']], f'checkout-{name}.log', base_env)
        head = subprocess.check_output(['git', '-C', str(directory), 'rev-parse', 'HEAD'], text=True).strip()
        dirty = subprocess.check_output(['git', '-C', str(directory), 'status', '--porcelain', '--untracked-files=all'], text=True)
        if head != dependency['rev'] or dirty: raise RuntimeError(f'dependency differs from pin: {name}')
        dependencies.append({'name': name, 'commit': head})
    run([lake, 'build'], 'lake-build.log', base_env)
    lean_path = run([lake, 'env', 'printenv', 'LEAN_PATH'], 'lean-path.log', base_env).strip()
    build = OUT / 'build'
    build.mkdir()
    env = base_env | {'LEAN_PATH': str(build) + os.pathsep + lean_path}
    print(f'Checking {len(files)} Lean files with {version}', flush=True)
    for index, source in enumerate(ordered(files)):
        target = build / source.relative_to(ROOT).with_suffix('.olean')
        target.parent.mkdir(parents=True, exist_ok=True)
        run([lean, '-DwarningAsError=true', '-o', str(target), str(source)], f'compile-{index:03}.log', env)
        print('COMPILED ' + str(source.relative_to(ROOT)), flush=True)
    audit = OUT / 'AxiomAudit.lean'
    audit.write_text(audit_source([module(p) for p in files]))
    audited = run([lean, '-DwarningAsError=true', str(audit)], 'axioms.log', env)
    total = int(re.search(r'AUDIT_TOTAL (\d+)', audited).group(1))
    with tempfile.TemporaryDirectory(prefix='lean-gate-controls-') as temporary:
        temporary = Path(temporary)
        fixture = temporary / 'Admitted.lean'
        fixture.write_text((ROOT / 'controls/Admitted.lean.fail').read_text())
        try: scan(fixture)
        except RuntimeError: pass
        else: raise RuntimeError('escape scanner accepted admitted proof')
        run([lean, '-DwarningAsError=true', str(fixture)], 'control-admitted.log', env, True)
        orphan = temporary / 'unlisted/Orphan.lean'
        orphan.parent.mkdir()
        orphan.write_text('axiom orphan : False\n')
        if orphan not in inventory(temporary): raise RuntimeError('inventory missed orphan file')
        try: scan(orphan)
        except RuntimeError: pass
        else: raise RuntimeError('escape scanner accepted orphan custom axiom')
        nested = temporary / 'nested/.lake/Hidden.lean'
        nested.parent.mkdir(parents=True)
        nested.write_text('axiom hidden : False\n')
        if nested not in inventory(temporary):
            raise RuntimeError('inventory missed nested metadata-name directory')
        try: scan(nested)
        except RuntimeError: pass
        else: raise RuntimeError('escape scanner accepted nested custom axiom')
        for label, source in {
            'native-decide': 'example : True := by native_decide\n',
            'kernel-bypass': 'set_option debug.skipKernelTC true\n',
            'warning-bypass': 'set_option warningAsError false\n',
        }.items():
            escape = temporary / (label + '.lean')
            escape.write_text(source)
            try: scan(escape)
            except RuntimeError: pass
            else: raise RuntimeError(f'escape scanner accepted {label}')
        linked = temporary / 'linked-source'
        linked.symlink_to(ROOT / 'Legacy', target_is_directory=True)
        try: inventory(temporary)
        except RuntimeError: pass
        else: raise RuntimeError('inventory accepted symlinked source directory')
        linked.unlink()
        custom = temporary / 'CustomAxiom.lean'
        custom.write_text('axiom injected : False\ntheorem propagated : False := injected\n')
        run([lean, '--root=' + str(temporary), '-o', str(build / 'CustomAxiom.olean'), str(custom)], 'control-custom-compile.log', env)
        custom_audit = temporary / 'AuditCustom.lean'
        custom_audit.write_text(audit_source(['CustomAxiom']))
        output = run([lean, '-DwarningAsError=true', str(custom_audit)], 'control-custom-audit.log', env, True)
        if 'custom axiom declaration' not in output and 'prohibited transitive axiom' not in output:
            raise RuntimeError('custom-axiom control failed for wrong reason')
        imported = temporary / 'CustomUse.lean'
        imported.write_text('import CustomAxiom\ntheorem importedProof : False := injected\n')
        run([lean, '--root=' + str(temporary), '-o', str(build / 'CustomUse.olean'), str(imported)], 'control-transitive-compile.log', env)
        transitive_audit = temporary / 'AuditTransitive.lean'
        transitive_audit.write_text(audit_source(['CustomUse']))
        output = run([lean, '-DwarningAsError=true', str(transitive_audit)], 'control-transitive-audit.log', env, True)
        if 'prohibited transitive axiom injected' not in output:
            raise RuntimeError('transitive-axiom control failed for wrong reason')
        warning = temporary / 'Warning.lean'
        warning.write_text('example (unused : Nat) : True := by trivial\n')
        run([lean, '-DwarningAsError=true', str(warning)], 'control-warning.log', env, True)
    run(['sh', 'examples/check.sh'], 'examples.log', env | {'LEAN': lean})
    cli = subprocess.run([lean, '--run', 'Cli.lean', 'examples/chain.json'], cwd=ROOT, env=env, text=True,
                         stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (OUT / 'cli.log').write_text(cli.stdout)
    if cli.returncode == 0 or 'release-one: refused app' not in cli.stdout or 'release-two: not-applied' not in cli.stdout:
        raise RuntimeError('CLI refusal control failed')
    for dependency in dependencies:
        directory = ROOT / manifest['packagesDir'] / dependency['name']
        head = subprocess.check_output(['git', '-C', str(directory), 'rev-parse', 'HEAD'], text=True).strip()
        dirty = subprocess.check_output(['git', '-C', str(directory), 'status', '--porcelain', '--untracked-files=all'], text=True)
        if head != dependency['commit'] or dirty:
            raise RuntimeError(f'dependency changed while checking: {dependency["name"]}')
    if inventory(ROOT) != files or any(hashlib.sha256((ROOT / p).read_bytes()).hexdigest() != h for p, h in hashes.items()):
        raise RuntimeError('Lean sources changed while checking')
    if any(hashlib.sha256((ROOT / p).read_bytes()).hexdigest() != h for p, h in input_hashes.items()):
        raise RuntimeError('gate configuration changed while checking')
    receipt = {
        'commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
        'dirty': bool(subprocess.check_output(['git', 'status', '--porcelain'], text=True)),
        'unsafe_runtime_declarations': int(re.search(r'UNSAFE_RUNTIME_TOTAL (\d+)', audited).group(1)),
        'lean': version, 'files_checked': len(files), 'proof_declarations_audited': total,
        'allowed_standard_axioms': ALLOWED, 'custom_axioms': 0, 'warnings_as_errors': True,
        'dependencies': dependencies, 'sources': hashes, 'gate_inputs': input_hashes,
        'negative_controls': ['admitted proof', 'unlisted custom axiom', 'nested metadata-name source', 'native decision', 'kernel bypass', 'warning bypass', 'source directory symlink', 'compiled custom axiom', 'imported custom axiom', 'warning', 'range-ledger mutation', 'CLI refusal'],
    }
    (OUT / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(f'PASS: {len(files)} Lean files; {total} proof declarations; no custom proof axioms; all controls rejected', flush=True)
    print('Receipt: ' + str(OUT / 'receipt.json'), flush=True)


if __name__ == '__main__':
    try: main()
    except (RuntimeError, subprocess.CalledProcessError) as exc:
        print(f'FAIL: {exc}', file=sys.stderr)
        sys.exit(1)
