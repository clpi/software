"""Append-only Lean receipts for actual linked code and captured execution values.

Compiler extensions decide only the new suffix and import a prior prefix proof.
Value extensions use parent correctness constants and prove local operations.
Local storage integrity and the Lean installation remain trust boundaries.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

from .engine import canonical, clone


class KernelError(RuntimeError):
    pass


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def natural(value, label: str) -> int:
    if type(value) is not int or value < 0:
        raise KernelError(f"{label} must be a nonnegative integer")
    return value


def integer(value) -> str:
    if type(value) is not int:
        raise KernelError("integer operands must be exact integers")
    return f"({value} : Int)"


def string(value) -> str:
    if not isinstance(value, str):
        raise KernelError("input name must be a string")
    return "(String.mk [" + ", ".join(f"Char.ofNat {ord(c)}" for c in value) + "])"


def operation(value: dict) -> str:
    if not isinstance(value, dict):
        raise KernelError("source operation must be an object")
    op = value.get("op")
    if op == "const" and set(value) == {"op", "value"}:
        return f".literal {integer(value['value'])}"
    if op == "input" and set(value) == {"op", "name"}:
        return f".input {string(value['name'])}"
    if op in {"add", "mul", "neg"} and set(value) == {"op"}:
        return f".{op}"
    raise KernelError("unsupported or malformed source operation")


def instruction(value: list) -> str:
    if not isinstance(value, list) or not value:
        raise KernelError("malformed stack instruction")
    op = value[0]
    if op == "PUSH" and len(value) == 2:
        return f".push {integer(value[1])}"
    if op == "INPUT" and len(value) == 2:
        return f".input {string(value[1])}"
    if op == "READ" and len(value) == 2:
        return f".read {natural(value[1], 'argument position')}"
    if op in {"ADD", "MUL", "NEG"} and len(value) == 1:
        return f".{op.lower()}"
    raise KernelError("unsupported or malformed stack instruction")


def render_row(row: dict) -> str:
    premises = ", ".join(str(natural(n, "premise")) for n in row["premises"])
    code = ", ".join(instruction(item) for item in row["code"])
    return f"  ⟨{operation(row['operation'])}, [{premises}], [{code}]⟩"


class KernelSession:
    """One writer and immutable accepted modules, with explicit restart replay.

    A hot extension reads its delta and retained indices. Lean still imports
    earlier module metadata; import, normalization, and I/O are not cost-free.
    """

    def __init__(self, directory, lean=None, proof_root=None):
        self.directory = Path(directory).resolve()
        self.directory.mkdir(parents=True, exist_ok=True)
        found = shutil.which(str(lean or os.environ.get("LEAN", "lean")))
        if not found:
            raise KernelError("Lean executable not found")
        self.lean = str(Path(found).resolve())
        self.proof_root = Path(proof_root) if proof_root else Path(__file__).resolve().parent.parent / "proof"
        version = subprocess.run([self.lean, "--version"], capture_output=True, text=True, check=True).stdout.strip()
        if "version 4.19.0," not in version:
            raise KernelError("incremental receipts require pinned Lean 4.19.0")
        self.scope = {"format": "lean-cumulative-integer-receipts-v1", "lean_version": version,
                      "lean_binary": digest(Path(self.lean)), "driver": digest(Path(__file__)),
                      "sources": {name: digest(self.proof_root / f"{name}.lean")
                                  for name in ("Incremental", "Pipeline", "Evaluation")}}
        self.rows, self.tasks = [], {}
        self.count, self.prefix = 0, ""
        self.executions, self.execution_tasks, self.execution_modules = [], {}, []
        self.execution_count, self.execution_prefix = 0, ""
        self.module = "IncrementalReceipt0"
        self.receipts = self.replayed_receipts = self.lean_processes = self.fixed_modules_built = 0
        self.rows_checked_this_session = self.values_checked_this_session = self.modules_built_this_session = 0
        self.last_output, self.axioms = "", []
        self.config_path = self.directory / "session.json"
        self.journal_path = self.directory / "receipts.jsonl"
        if self.config_path.exists():
            self._restore()
        else:
            self._bootstrap()

    def _compile(self, module, source, dependencies=None):
        if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", module):
            raise KernelError("invalid internal module name")
        if re.search(r"(?<![\w])(sorry|sorryAx|admit|axiom|native_decide|implemented_by|"
                     r"extern|unsafe|opaque|partial)(?![\w])|debug\.skipKernelTC", source):
            raise KernelError("prohibited proof token")
        with tempfile.TemporaryDirectory(prefix="pending-", dir=self.directory) as pending:
            pending = Path(pending)
            (pending / f"{module}.lean").write_text(source)
            env = {**os.environ, "LEAN_PATH": str(self.directory)}
            self.lean_processes += 1
            proc = subprocess.run([self.lean, "-DwarningAsError=true", "-o", f"{module}.olean", f"{module}.lean"],
                                  cwd=pending, env=env, capture_output=True, text=True, timeout=120)
            output = proc.stdout + proc.stderr
            self.last_output = output
            if proc.returncode or re.search(r"error:|warning:|sorryAx", output):
                raise KernelError(f"Lean rejected {module}:\n{output}")
            axioms = set()
            for group in re.findall(r"depends on axioms: \[([^]]*)\]", output):
                axioms.update(item.strip() for item in group.split(",") if item.strip())
            if not axioms <= {"propext", "Quot.sound"}:
                raise KernelError(f"forbidden dependency: {sorted(axioms)}")
            for name in dependencies or ():
                if not re.search(r"'" + re.escape(name) + r"' (?:does not depend on any axioms|depends on axioms:)", output):
                    raise KernelError(f"missing dependency census for {name}")
            files = {}
            for extension in ("lean", "olean"):
                source_path = pending / f"{module}.{extension}"
                target = self.directory / source_path.name
                if target.exists():
                    if target.read_bytes() != source_path.read_bytes():
                        raise KernelError("refusing to replace a retained proof artifact")
                else:
                    with target.open("xb") as stream:
                        stream.write(source_path.read_bytes())
                files[target.name] = digest(target)
            return {"files": files, "axioms": sorted(axioms), "output": output}

    @staticmethod
    def _semantics(module):
        return f"""theorem semantics (env : Pipeline.Environment) :
    ∃ result, Pipeline.source env [] history = some result ∧
      Pipeline.target env [] history = some result ∧ result.length = history.length :=
  Pipeline.checked_program_correct certified env
end {module}
#print axioms {module}.history_length
#print axioms {module}.certified
#print axioms {module}.semantics
"""

    def _bootstrap(self):
        if any(self.directory.iterdir()):
            raise KernelError("unrecognized nonempty proof directory")
        files = {}
        for module in ("Incremental", "Pipeline", "Evaluation"):
            built = self._compile(module, (self.proof_root / f"{module}.lean").read_text())
            files.update(built["files"])
            self.fixed_modules_built += 1
        base = """import Evaluation
namespace IncrementalReceipt0
def history : List Pipeline.Row := []
theorem history_length : history.length = 0 := rfl
theorem certified : Pipeline.check 0 history = true := rfl
""" + self._semantics(self.module)
        built = self._compile(self.module, base,
                              [f"{self.module}.{name}" for name in ("history_length", "certified", "semantics")])
        files.update(built["files"])
        self.fixed_modules_built += 1
        self.axioms = built["axioms"]
        with self.config_path.open("x") as stream:
            json.dump({"scope": self.scope, "files": files, "axioms": self.axioms}, stream, sort_keys=True)
            stream.write("\n")
        self.journal_path.touch(exist_ok=False)

    def _check_files(self, files):
        for name, expected in files.items():
            if Path(name).name != name or digest(self.directory / name) != expected:
                raise KernelError("retained proof artifact integrity mismatch")

    def _restore(self):
        config = json.loads(self.config_path.read_text())
        if config["scope"] != self.scope:
            raise KernelError("proof source/toolchain scope changed; use a new proof session")
        self._check_files(config["files"])
        self.axioms = config["axioms"]
        if not set(self.axioms) <= {"propext", "Quot.sound"}:
            raise KernelError("forbidden base axiom metadata")
        with self.journal_path.open("rb") as stream:
            for line in stream:
                if not line.endswith(b"\n"):
                    raise KernelError("truncated proof receipt journal")
                receipt = json.loads(line)
                checksum = receipt.pop("checksum")
                if hashlib.sha256(canonical(receipt)).hexdigest() != checksum:
                    raise KernelError("proof receipt checksum mismatch")
                if receipt["previous"] != self.module or receipt["start"] != self.count or receipt["prefix"] != self.prefix:
                    raise KernelError("proof receipt chain mismatch")
                if receipt["module"] != f"IncrementalReceipt{self.receipts + 1}":
                    raise KernelError("nonconsecutive proof receipt module")
                self._check_files(receipt["files"])
                if not set(receipt["axioms"]) <= {"propext", "Quot.sound"}:
                    raise KernelError("forbidden retained axiom metadata")
                rows, executions = self._validate({**receipt, "format": "incremental-linked-integer-blocks-v1", "observations": {}})
                source, _ = self._module_source(receipt["module"], rows, executions)
                if (self.directory / f"{receipt['module']}.lean").read_text() != source:
                    raise KernelError("retained proof source does not certify the recorded artifacts")
                self._accept(receipt)
                self.replayed_receipts += 1

    def _accept(self, receipt):
        for row in receipt["rows"]:
            self.tasks[row["task"]] = len(self.rows)
            self.rows.append(row)
        self.count, self.prefix = receipt["end"], receipt["tail"]
        for row in receipt["execution_rows"]:
            self.execution_tasks[row["task"]] = len(self.executions)
            self.executions.append(row)
            self.execution_modules.append(receipt["module"])
        self.execution_count, self.execution_prefix = receipt["execution_end"], receipt["execution_tail"]
        self.module, self.axioms = receipt["module"], receipt["axioms"]
        self.receipts += 1

    def _validate(self, snapshot):
        if snapshot.get("format") != "incremental-linked-integer-blocks-v1":
            raise KernelError("unknown compiler bridge format")
        if snapshot.get("start") != self.count or snapshot.get("prefix") != self.prefix:
            raise KernelError("compiler prefix does not match retained proof")
        rows = clone(snapshot.get("rows"))
        if not isinstance(rows, list) or snapshot.get("end") != self.count + len(rows):
            raise KernelError("compiler suffix length mismatch")
        added, added_tasks, prefix = [], set(), self.prefix
        for offset, row in enumerate(rows):
            index = self.count + offset
            if row.get("id") != index:
                raise KernelError("compiler rows must append consecutive completion indices")
            task = natural(row.get("task"), "compiler task")
            if task in self.tasks or task in added_tasks:
                raise KernelError("a completed compiler task cannot be published twice")
            if row.get("checked") is not True:
                raise KernelError("compiler row has no successful local certificate check")
            natural(row.get("certificate"), "certificate task")
            natural(row.get("check"), "check task")
            if not isinstance(row.get("premises"), list):
                raise KernelError("premises must be an ordered list")
            parents = []
            for position in row["premises"]:
                natural(position, "premise")
                if position >= index:
                    raise KernelError("compiler premise is not an earlier completed row")
                parents.append(self.rows[position] if position < self.count else added[position - self.count])
            if row.get("links") != [parent["task"] for parent in parents]:
                raise KernelError("task IDs do not match completed-row premise projection")
            if row.get("check_parents") != [parent["check"] for parent in parents]:
                raise KernelError("certificate composition omitted or changed a parent")
            artifact = row.get("artifact")
            if artifact != {"source": row.get("operation"), "links": row.get("links"), "code": row.get("code")}:
                raise KernelError("exported operation, links, or code differ from compiler artifact")
            render_row(row)
            descriptor = {"stage": "compile", "payload": row["operation"], "deps": row["links"], "scope": row["scope"]}
            prefix = hashlib.sha256(canonical({"previous": prefix, "task": task,
                                               "descriptor": descriptor, "value": artifact})).hexdigest()
            added.append(row)
            added_tasks.add(task)
        if snapshot.get("tail") != prefix:
            raise KernelError("compiler artifact suffix does not match journal completion chain")
        if snapshot.get("execution_start") != self.execution_count or snapshot.get("execution_prefix") != self.execution_prefix:
            raise KernelError("execution prefix does not match retained proof")
        executions = clone(snapshot.get("execution_rows"))
        if not isinstance(executions, list) or snapshot.get("execution_end") != self.execution_count + len(executions):
            raise KernelError("execution suffix length mismatch")
        added_executions, added_execution_tasks = [], {}
        execution_prefix = self.execution_prefix
        for offset, row in enumerate(executions):
            index = self.execution_count + offset
            if row.get("id") != index:
                raise KernelError("execution rows must append consecutive completion indices")
            task = natural(row.get("task"), "execution task")
            if task in self.execution_tasks or task in added_execution_tasks:
                raise KernelError("a completed execution task cannot be published twice")
            compiled_at = natural(row.get("compiler_row"), "execution compiler row")
            if compiled_at >= self.count + len(added):
                raise KernelError("execution refers to an absent compiler row")
            compiled = self.rows[compiled_at] if compiled_at < self.count else added[compiled_at - self.count]
            descriptor = row.get("descriptor", {})
            if descriptor.get("stage") != "execute" or descriptor.get("scope") != compiled["scope"]:
                raise KernelError("execution scope differs from its checked compiler artifact")
            parents = []
            for position in row.get("parents", []):
                natural(position, "execution parent")
                if position >= index:
                    raise KernelError("execution parent is not an earlier completed row")
                parents.append(self.executions[position] if position < self.execution_count
                               else added_executions[position - self.execution_count])
            if descriptor.get("deps") != [compiled["task"], compiled["check"], *[parent["task"] for parent in parents]]:
                raise KernelError("execution task IDs differ from its projected all-parent proof")
            if [parent["compiler_row"] for parent in parents] != compiled["premises"]:
                raise KernelError("execution arguments differ from the compiler's ordered links")
            if any(parent["descriptor"]["scope"] != descriptor["scope"] for parent in parents):
                raise KernelError("execution composes different scopes")
            payload = descriptor.get("payload")
            if not isinstance(payload, dict) or set(payload) != {"inputs"} or not isinstance(payload["inputs"], dict):
                raise KernelError("malformed captured input payload")
            op = compiled["operation"]
            if op["op"] == "input":
                if set(payload["inputs"]) != {op["name"]}:
                    raise KernelError("captured input does not match the compiled input name")
                integer(payload["inputs"][op["name"]])
            elif payload["inputs"]:
                raise KernelError("a non-input block has undeclared environment inputs")
            integer(row.get("value"))
            execution_prefix = hashlib.sha256(canonical({"previous": execution_prefix, "task": task,
                                                         "descriptor": descriptor, "value": row["value"]})).hexdigest()
            added_execution_tasks[task] = index
            added_executions.append(row)
        if snapshot.get("execution_tail") != execution_prefix:
            raise KernelError("execution values do not match journal completion chain")
        for observed in snapshot.get("observations", {}).values():
            index = natural(observed.get("row"), "observed output row")
            if index >= self.count + len(added):
                raise KernelError("observed output is absent from certified prefix")
            row = self.rows[index] if index < self.count else added[index - self.count]
            if observed.get("compile_task") != row["task"] or observed.get("scope") != row["scope"]:
                raise KernelError("observed output refers to a different compiler identity")
            if observed["scope"] != snapshot["scope"]:
                raise KernelError("historical proof cannot label a different active scope current")
            if type(observed.get("value")) is not int or observed.get("value") != observed.get("executed"):
                raise KernelError("observed execution is missing or differs from recomputation")
            position = self.execution_tasks.get(observed.get("execute_task"), added_execution_tasks.get(observed.get("execute_task")))
            if position is None:
                raise KernelError("observed execution has no value proof")
            result = self.executions[position] if position < self.execution_count else added_executions[position - self.execution_count]
            if result["compiler_row"] != index or result["value"] != observed["value"]:
                raise KernelError("observed value differs from the proven execution invocation")
        return rows, executions

    def _value_source(self, module, rows, executions):
        source, names = [], []
        for row in executions:
            index, compiled_at = row["id"], row["compiler_row"]
            compiled = self.rows[compiled_at] if compiled_at < self.count else rows[compiled_at - self.count]
            op = compiled["operation"]
            code = "[" + ", ".join(instruction(item) for item in compiled["code"]) + "]"
            parents = [f"{self.execution_modules[parent] if parent < self.execution_count else module}.value_{parent}"
                       for parent in row["parents"]]
            proofs = " ".join(parent + "_correct" for parent in parents)
            if op["op"] == "const":
                tree, theorem = f".literal {integer(op['value'])} {code}", "literal_correct"
            elif op["op"] == "input":
                captured = row["descriptor"]["payload"]["inputs"][op["name"]]
                tree, theorem = f".input {string(op['name'])} {integer(captured)} {code}", "input_correct"
            else:
                tree, theorem = f".{op['op']} {' '.join(parents)} {code}", f"{op['op']}_correct"
            source.append(f"def value_{index} : Evaluation.Tree := {tree}\n"
                          f"theorem value_{index}_correct : Evaluation.Correct value_{index} {integer(row['value'])} :=\n"
                          f"  Evaluation.{theorem} {proofs} (by decide) (by decide)\n")
            names.append(f"{module}.value_{index}_correct")
        return "".join(source), names

    def _module_source(self, module, rows, executions):
        values_source, values_names = self._value_source(module, rows, executions)
        if rows:
            compiler_source = ("def delta : List Pipeline.Row := [\n" + ",\n".join(render_row(row) for row in rows) + "\n]\n"
                  f"theorem delta_checked : Pipeline.check {self.count} delta = true := by decide\n"
                  f"def history : List Pipeline.Row := {self.module}.history ++ delta\n"
                  f"theorem history_length : history.length = {self.count + len(rows)} :=\n"
                  f"  Pipeline.extension_length {self.module}.history_length\n"
                  f"    (show delta.length = {len(rows)} from by decide)\n"
                  "theorem certified : Pipeline.check 0 history = true :=\n"
                  f"  Pipeline.certify_extension {self.module}.certified {self.module}.history_length delta_checked\n")
        else:
            compiler_source = (f"def history : List Pipeline.Row := {self.module}.history\n"
                               f"theorem history_length : history.length = {self.count} := {self.module}.history_length\n"
                               f"theorem certified : Pipeline.check 0 history = true := {self.module}.certified\n")
        names = [f"{module}.{name}" for name in ("history_length", "certified", "semantics")]
        if rows:
            names.append(f"{module}.delta_checked")
        source = (f"import {self.module}\nnamespace {module}\n" + compiler_source + values_source
                  + self._semantics(module) + (f"#print axioms {module}.delta_checked\n" if rows else "")
                  + "".join(f"#print axioms {name}\n" for name in values_names))
        return source, names + values_names

    def certify(self, snapshot):
        rows, executions = self._validate(snapshot)
        if not rows and not executions:
            return {"new_rows": 0, "new_modules": 0, "reused_prefix_rows": self.count,
                    "total_rows": self.count, "module": self.module, "axioms": self.axioms,
                    "new_value_proofs": 0, "total_value_proofs": self.execution_count,
                    "lean_processes": 0, "output": "Reused compiler and captured-input value proofs; no new rows.\n"}
        module = f"IncrementalReceipt{self.receipts + 1}"
        source, names = self._module_source(module, rows, executions)
        built = self._compile(module, source, names)
        receipt = {"module": module, "previous": self.module, "start": self.count,
                   "end": self.count + len(rows), "prefix": self.prefix, "tail": snapshot["tail"],
                   "execution_start": self.execution_count, "execution_end": self.execution_count + len(executions),
                   "execution_prefix": self.execution_prefix, "execution_tail": snapshot["execution_tail"],
                   "execution_rows": executions, "rows": rows, "files": built["files"], "axioms": built["axioms"]}
        receipt["checksum"] = hashlib.sha256(canonical(receipt)).hexdigest()
        with self.journal_path.open("ab") as stream:
            stream.write(canonical(receipt) + b"\n")
            stream.flush()
            os.fsync(stream.fileno())
        old_count = self.count
        self._accept(receipt)
        self.rows_checked_this_session += len(rows)
        self.values_checked_this_session += len(executions)
        self.modules_built_this_session += 1
        return {"new_rows": len(rows), "new_modules": 1, "reused_prefix_rows": old_count,
                "total_rows": self.count, "module": self.module, "axioms": self.axioms,
                "new_value_proofs": len(executions), "total_value_proofs": self.execution_count,
                "lean_processes": 1, "output": built["output"]}

    def metrics(self):
        return {"total_rows": self.count, "total_receipts": self.receipts,
                "total_value_proofs": self.execution_count,
                "fixed_modules_built_this_session": self.fixed_modules_built,
                "receipt_modules_built_this_session": self.modules_built_this_session,
                "rows_checked_this_session": self.rows_checked_this_session,
                "values_checked_this_session": self.values_checked_this_session,
                "lean_processes_this_session": self.lean_processes,
                "replayed_receipts": self.replayed_receipts, "scope": self.scope}
