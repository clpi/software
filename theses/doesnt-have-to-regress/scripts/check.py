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
import tomllib

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / '.lake/all-files-gate'
FORBIDDEN = re.compile(r"(?<![\w'])(?:sorry|admit|axiom|sorryAx|native_decide|partial|unsafe|unsafeCast|ofReduceBool|ofReduceNat|trustCompiler|implemented_by|extern|addDecl|addAndCompile|setEnv|modifyEnv|setOptions|withOptions|run_elab|run_meta|run_cmd|elab|elab_rules|macro|macro_rules|syntax|declare_syntax_cat|initialize|builtin_initialize|elabCommand|runParserCategory|runFrontend)(?![\w'])")
SAFE_OPTIONS = {'autoImplicit', 'maxRecDepth', 'maxHeartbeats', 'pp.universes'}
ALLOWED = ['propext', 'Classical.choice', 'Quot.sound']


def code_only(text):
    """Lex Lean comments and literal forms without letting literals hide code."""
    result = list(text)
    size = len(text)

    def blank(start, end):
        for pos in range(start, end):
            if text[pos] != '\n': result[pos] = ' '

    def identifier_char(char):
        return char.isalnum() or char in "_'"

    i = 0
    while i < size:
        start = i
        if text.startswith('--', i):
            end = text.find('\n', i + 2)
            i = size if end < 0 else end
            blank(start, i)
        elif text.startswith('/-', i):
            i, depth = i + 2, 1
            while i < size and depth:
                if text.startswith('/-', i): depth, i = depth + 1, i + 2
                elif text.startswith('-/', i): depth, i = depth - 1, i + 2
                else: i += 1
            if depth: raise RuntimeError('unterminated Lean block comment')
            blank(start, i)
        elif text[i] == 'r' and (i == 0 or not identifier_char(text[i - 1])) and (raw := re.match(r'r(#{0,})"', text[i:])):
            delimiter = '"' + raw.group(1)
            end = text.find(delimiter, i + len(raw.group(0)))
            if end < 0: raise RuntimeError('unterminated Lean raw string')
            i = end + len(delimiter)
            blank(start, i)
        elif text[i] == "'" and (i == 0 or not identifier_char(text[i - 1])) and not text.startswith("''", i):
            end = i + 1
            if end < size and text[end] == '\\':
                end += 1
                if end >= size: raise RuntimeError('unterminated Lean character escape')
                end += {'x': 3, 'u': 5}.get(text[end], 1)
            else: end += 1
            if end >= size or text[end] != "'":
                raise RuntimeError('unrecognized Lean character literal')
            i = end + 1
            blank(start, i)
        elif text[i] == '"':
            i += 1
            while i < size and text[i] != '"':
                i += 2 if text[i] == '\\' else 1
            if i >= size: raise RuntimeError('unterminated Lean string')
            i += 1
            blank(start, i)
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


def audit_source(modules, allow_empty=False):
    imports = '\n'.join('import ' + n for n in modules)
    own = ', '.join('`' + n for n in modules)
    allowed = ', '.join('`' + n for n in ALLOWED)
    report = '  for line in SoftwareDoesntRegress.implicationLines env do\n    IO.println line\n' if 'SoftwareDoesntRegress.Implications' in modules else ''
    nonempty = '' if allow_empty else '  if count == 0 then throwError "empty proof audit"\n'
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
    if info.isUnsafe then
      let logical ← try liftTermElabM (Lean.Meta.isProp info.type) catch _ => pure false
      if logical then throwError "unsafe proposition declaration: {{name}}"
      let leaf := name.getString!
      let numbered := if leaf.startsWith "_spec_" then leaf.toList.drop 6
        else if leaf.startsWith "_elambda_" then leaf.toList.drop 9 else []
      let compilerName := leaf == "_cstage1" || leaf == "_cstage2" ||
        (!numbered.isEmpty && numbered.all Char.isDigit)
      let authored ← findDeclarationRanges? name
      unless compilerName && authored.isNone do
        throwError "unrecognized unsafe declaration: {{name}}"
      runtimeCount := runtimeCount + 1
      IO.println s!"GENERATED_UNSAFE_RUNTIME {{name}}"
    else if let .axiomInfo _ := info then
      throwError "custom axiom declaration: {{name}}"
    unless info.isUnsafe do
      if (← liftTermElabM (Lean.Meta.isProp info.type)) then
        let axioms ← collectAxioms name
        for ax in axioms do
          unless allowed.contains ax do
            throwError "prohibited transitive axiom {{ax}} in {{name}}"
        count := count + 1
        IO.println s!"AUDITED {{name}} AXIOMS {{axioms}}"
{nonempty.rstrip()}
  IO.println s!"AUDIT_TOTAL {{count}}"
  IO.println s!"GENERATED_UNSAFE_RUNTIME_TOTAL {{runtimeCount}}"
{report}audit_all_repository_proofs
'''


def main():
    if len(sys.argv) != 1: raise RuntimeError('check.sh takes no arguments; all checks are mandatory')
    os.chdir(ROOT)
    files = inventory(ROOT)
    if not files: raise RuntimeError('empty Lean inventory')
    hashes = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    for path in files: scan(path)
    inputs = ['check.sh', 'scripts/check.py', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain', 'examples/stream.json', 'examples/stream.expected', 'examples/check.sh', 'examples/replay.py', 'examples/range-ledger/check.sh', 'examples/range-ledger/replay.py', 'examples/range-ledger/mutation.patch', 'controls/QuotedEscape.lean.fail', 'controls/GeneratedEscape.lean.fail', 'controls/SpoofedRuntime.lean.fail']
    dynamic_inputs = sorted(str(p.relative_to(ROOT)) for p in (ROOT / 'examples').glob('dynamic-*') if p.is_file())
    inputs += ['examples/check_dynamic.py', '.github/workflows/check.yml'] + dynamic_inputs
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
    expected = {
        'software-is-composable': '033c12c01299a9b28983bee410c230641adc7d1e',
        'software-is-quantifiable': 'a21c7c56fa028f32014dd795b35b14f688e8fdf1',
    }
    declared = {d['name'].strip('«»'): d['rev'] for d in manifest['packages']}
    if declared != expected or len(manifest['packages']) != len(expected):
        raise RuntimeError('dependency manifest differs from audited pins')
    lake_config = tomllib.loads((ROOT / 'lakefile.toml').read_text())
    declared_config = {d['name'].strip('«»'): d['rev'] for d in lake_config['require']}
    if declared_config != expected or len(lake_config['require']) != len(expected):
        raise RuntimeError('Lake declarations differ from audited dependency pins')
    if lake_config.get('leanOptions', {}).get('warningAsError') is not True:
        raise RuntimeError('Lake warningAsError must stay enabled')
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
    # Different executables each declare a global `main`; Lean cannot import
    # both in one environment. Partition only their audit imports, never the
    # source inventory. Each repository module is audited exactly once for
    # its own declarations; transitive proof axioms are still checked.
    modules = [module(p) for p in files]
    entries = [entry.get('root', entry['name']) for entry in lake_config.get('lean_exe', [])]
    if len(entries) != len(set(entries)) or any(entry not in modules for entry in entries):
        raise RuntimeError('executable roots must be distinct inventoried Lean modules')
    groups = [('libraries', [name for name in modules if name not in entries])]
    groups += [(entry, [entry]) for entry in sorted(entries)]
    flattened = [name for _, names in groups for name in names]
    if sorted(flattened) != sorted(modules) or len(flattened) != len(set(flattened)):
        raise RuntimeError('proof-audit partition omitted or duplicated a source module')
    checker_hashes, audit_groups, audit_logs = {}, [], []
    total, runtime_total = 0, 0
    for index, (label, names) in enumerate(groups):
        audit = OUT / f'AxiomAudit{index}.lean'
        audit.write_text(audit_source(names, allow_empty=label != 'libraries'))
        checker_hashes[audit.name] = hashlib.sha256(audit.read_bytes()).hexdigest()
        audited = run([lean, '-DwarningAsError=true', str(audit)], f'axioms-{index}.log', env)
        count = int(re.search(r'^AUDIT_TOTAL (\d+)', audited, re.M).group(1))
        runtime_count = int(re.search(r'^GENERATED_UNSAFE_RUNTIME_TOTAL (\d+)', audited, re.M).group(1))
        total += count
        runtime_total += runtime_count
        audit_groups.append({'label': label, 'modules': names, 'proof_declarations': count,
                             'generated_unsafe_runtime_declarations': runtime_count})
        audit_logs.append(f'GROUP {label}\n' + audited)
    (OUT / 'axioms.log').write_text('\n'.join(audit_logs))
    with tempfile.TemporaryDirectory(prefix='lean-gate-controls-') as temporary:
        temporary = Path(temporary)
        fixture = temporary / 'Admitted.lean'
        fixture.write_text('theorem forbidden_admission : False := by admit\n')
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
            'partial': 'partial def f : Nat := f\n',
            'unsafe': 'unsafe def f : Nat := 0\n',
            'extern': '@[extern \"f\"] opaque f : Nat\n',
            'implemented-by': '@[implemented_by replacement] def f : Nat := 0\n',
            'sorry': 'example : False := by sorry\n',
            'kernel-bypass': 'set_option debug.skipKernelTC true\n',
            'warning-bypass': 'set_option warningAsError false\n',
        }.items():
            escape = temporary / (label + '.lean')
            escape.write_text(source)
            try: scan(escape)
            except RuntimeError: pass
            else: raise RuntimeError(f'escape scanner accepted {label}')
        linked = temporary / 'linked-source'
        linked.symlink_to(ROOT / 'SoftwareDoesntRegress', target_is_directory=True)
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
        for name in ['QuotedEscape', 'GeneratedEscape', 'SpoofedRuntime']:
            escaped = temporary / (name + '.lean')
            escaped.write_text((ROOT / 'controls' / (name + '.lean.fail')).read_text())
            try: scan(escaped)
            except RuntimeError: pass
            else: raise RuntimeError('source scan accepted ' + name)
            run([lean, '--root=' + str(temporary), '-o', str(build / (name + '.olean')), str(escaped)],
                'control-' + name + '-compile.log', env)
            unsafe_audit = temporary / ('Audit' + name + '.lean')
            unsafe_audit.write_text(audit_source([name]))
            output = run([lean, '-DwarningAsError=true', str(unsafe_audit)],
                         'control-' + name + '-audit.log', env, True)
            if 'unrecognized unsafe declaration' not in output:
                raise RuntimeError('unsafe declaration control failed for wrong reason: ' + name)
        raw = temporary / 'RawString.lean'
        raw.write_text('def label : String := r##"quote " and unsafe text"##\n'
                       'unsafe def rawHidden : Nat := 0\n')
        try: scan(raw)
        except RuntimeError as exc:
            if 'unsafe' not in str(exc): raise
        else: raise RuntimeError('raw string hid an unsafe declaration')
        literal = temporary / 'ValidLiterals.lean'
        literal.write_text('def label : String := r##"quote " and unsafe text"##\n'
                           'def quoteChar : Char := \'"\'\n'
                           'def escapedQuote : Char := \'\\"\'\n'
                           'def escapedHex : Char := \'\\x22\'\n'
                           'def escapedUnicode : Char := \'\\u0022\'\n')
        scan(literal)
        run([lean, '-DwarningAsError=true', str(literal)], 'control-valid-literals.log', env)
        warning = temporary / 'Warning.lean'
        warning.write_text('example (unused : Nat) : True := by trivial\n')
        run([lean, '-DwarningAsError=true', str(warning)], 'control-warning.log', env, True)
    run(['sh', 'examples/check.sh'], 'examples.log', env | {'LEAN': lean})
    actual = run([str(ROOT / '.lake/build/bin/gate'), 'examples/stream.json'], 'gate-stream.log', env)
    if actual != (ROOT / 'examples/stream.expected').read_text():
        raise RuntimeError('gate executable output differs from expected stream')
    dynamic_output = run([sys.executable, 'examples/check_dynamic.py'], 'dynamic-controls.log', env)
    if 'DYNAMIC_CONTROLS_PASS' not in dynamic_output:
        raise RuntimeError('dynamic command-stream controls did not report completion')
    with tempfile.TemporaryDirectory(prefix='regress-parser-controls-') as temporary:
        temporary = Path(temporary)
        refused_inputs = {
            'truncated': '{"names": [], "releases": [',
            'trailing': '{"names": [], "releases": []}x',
            'malformed': '{"names": [], "releases": [x]}',
            'object-trailing-comma': '{"names": [], "releases": [],}',
            'array-trailing-comma': '{"names": ["a",], "releases": []}',
            'duplicate-key': '{"names": [], "names": ["b"], "releases": []}',
            'nested-duplicate-key': '{"names": [], "releases": [{"name": "x", "name": "y", "symbols": []}]}',
            'leading-zero': '{"names": [], "releases": [], "extra": 00}',
            'raw-newline': '{"names": ["a\nb"], "releases": []}',
            'raw-control': '{"names": ["a\x01b"], "releases": []}',
            'escape-outside-supported-subset': '{"names": ["a\\nb"], "releases": []}',
        }
        for label, content in refused_inputs.items():
            fixture = temporary / (label + '.json')
            fixture.write_text(content)
            result = subprocess.run([str(ROOT / '.lake/build/bin/gate'), str(fixture)],
                                    cwd=ROOT, env=env, text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            (OUT / ('parser-' + label + '.log')).write_text(result.stdout)
            if result.returncode == 0 or 'invalid stream' not in result.stdout:
                raise RuntimeError('parser did not fail closed: ' + label)
        fixture = temporary / 'FalseAcceptance.lean'
        fixture.write_text('import SoftwareDoesntRegress.Profiles\n'
                          'open SoftwareDoesntRegress\n'
                          'theorem rejected : accepts exInc exPure = true := by decide\n')
        run([lean, '-DwarningAsError=true', str(fixture)], 'control-false-acceptance.log', env, True)
        exhaustion = temporary / 'Exhaustion.lean'
        exhaustion.write_text('import GateExe\n'
                              '#guard (GateExe.parseValue 0 "0".toList).isNone\n'
                              '#guard (GateExe.parseArray 0 "]".toList).isNone\n'
                              '#guard (GateExe.parseObject 0 "}".toList).isNone\n')
        run([lean, '-DwarningAsError=true', str(exhaustion)], 'parser-exhaustion.log', env)
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
    if sorted(str(p.relative_to(ROOT)) for p in (ROOT / 'examples').glob('dynamic-*') if p.is_file()) != dynamic_inputs:
        raise RuntimeError('dynamic scenario inventory changed while checking')
    receipt = {
        'commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip() if (ROOT / '.git').exists() else None,
        'dirty': bool(subprocess.check_output(['git', 'status', '--porcelain'], text=True)) if (ROOT / '.git').exists() else None,
        'source_proof_escapes': 0,
        'generated_checker_sha256': hashlib.sha256(json.dumps(checker_hashes, sort_keys=True).encode()).hexdigest(),
        'generated_checkers': checker_hashes, 'audit_groups': audit_groups,
        'generated_unsafe_runtime_declarations': runtime_total,
        'lean': version, 'files_checked': len(files), 'proof_declarations_audited': total,
        'allowed_standard_axioms': ALLOWED, 'custom_proof_axioms': 0, 'warnings_as_errors': True,
        'dependencies': dependencies, 'sources': hashes, 'gate_inputs': input_hashes,
        'dynamic_controls': dynamic_output.strip().splitlines(),
        'negative_controls': ['admitted proof', 'unlisted custom axiom', 'nested metadata-name source', 'native decision', 'kernel bypass', 'warning bypass', 'source directory symlink', 'compiled custom axiom', 'imported custom axiom', 'warning', 'partial definition', 'unsafe definition', 'extern', 'implemented_by', 'sorry', 'range-ledger mutation', 'false acceptance', 'malformed parser input', 'truncated parser input', 'trailing parser input', 'parser fuel exhaustion', 'quote-literal unsafe concealment', 'raw-string unsafe concealment', 'command-synthesized unsafe declaration', 'spoofed compiler runtime name', 'duplicate object keys', 'trailing commas', 'leading-zero numbers', 'raw string controls', 'unsupported JSON escapes'],
    }
    (OUT / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(f'PASS: {len(files)} Lean files; {total} proof declarations; no custom proof axioms; all controls rejected', flush=True)
    print('Receipt: ' + str(OUT / 'receipt.json'), flush=True)


if __name__ == '__main__':
    try: main()
    except (RuntimeError, subprocess.CalledProcessError) as exc:
        print(f'FAIL: {exc}', file=sys.stderr)
        sys.exit(1)
