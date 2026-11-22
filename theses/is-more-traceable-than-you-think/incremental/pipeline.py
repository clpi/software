"""An incrementally compiled integer-expression DAG and explicit proof DAG.

This finite reference pipeline is not an integration with production Idol.
Compiler blocks link child artifacts instead of copying their code. Certificates
contain local symbolic stack traces and child certificate IDs. An independent
checker validates each trace, its specified operation, and every child receipt.
Input values are explicit dependencies of recomputation/execution only; compiler
correctness is symbolic in named inputs and child values.
"""
from __future__ import annotations

from collections import ChainMap, defaultdict, deque
import hashlib
from pathlib import Path
import platform
import sys
from typing import Any

from .engine import Engine, Context, Result, canonical, clone, difference, same_identity

STAGES = ("recompute", "compile", "certificate", "check", "execute")
ARITY = {"const": 0, "input": 0, "add": 2, "mul": 2, "neg": 1}


def implementation() -> dict:
    here = Path(__file__).resolve().parent
    pipeline = hashlib.sha256((here / "pipeline.py").read_bytes()).hexdigest()
    return {"engine": hashlib.sha256((here / "engine.py").read_bytes()).hexdigest(),
            "compiler": pipeline, "checker": pipeline,
            "toolchain": {"python": platform.python_version(), "implementation": sys.implementation.name}}


def default_scope() -> dict:
    actual = implementation()
    return {"contract": "pure-exact-integers-v1", "target": "linked-stack-blocks-v1",
            "compiler": actual["compiler"], "engine": actual["engine"],
            "checker": "independent-local-symbolic-stack-checker-v1",
            "toolchain": actual["toolchain"], "implementation": actual,
            "environment": {"system": platform.system(), "machine": platform.machine(),
                            "inputs": "explicit per-leaf task payload", "effects": "none"}}


def _integer(value):
    if type(value) is not int:
        raise ValueError("only exact integer values are supported")
    return value


def normalize(name: str, definition: dict) -> dict:
    if not isinstance(name, str) or not name:
        raise ValueError("source names must be nonempty strings")
    if not isinstance(definition, dict) or definition.get("op") not in ARITY:
        raise ValueError("unsupported source definition")
    op = definition["op"]
    if op in ("const", "input"):
        if set(definition) != {"op", "value"}:
            raise ValueError("leaf definitions require exactly op and value")
        return {"op": op, "value": _integer(definition["value"])}
    if set(definition) != {"op", "args"}:
        raise ValueError("operator definitions require exactly op and args")
    args = definition["args"]
    if not isinstance(args, list) or len(args) != ARITY[op] or any(not isinstance(a, str) for a in args):
        raise ValueError("incorrect ordered source argument list")
    return {"op": op, "args": list(args)}


def specification(name: str, definition: dict) -> dict:
    op = definition["op"]
    if op == "input":
        return {"op": op, "name": name}
    if op == "const":
        return {"op": op, "value": definition["value"]}
    return {"op": op}


def direct(source: dict, arguments: list[int], inputs: dict[str, int]) -> int:
    op = source["op"]
    if len(arguments) != ARITY[op]:
        raise ValueError("source arity mismatch")
    if op == "const":
        return source["value"]
    if op == "input":
        return _integer(inputs[source["name"]])
    if op == "add":
        return arguments[0] + arguments[1]
    if op == "mul":
        return arguments[0] * arguments[1]
    return -arguments[0]


def execute_block(code: list, arguments: list[int], inputs: dict[str, int]) -> int:
    stack = []
    for instruction in code:
        op = instruction[0]
        if op == "PUSH" and len(instruction) == 2:
            stack.append(_integer(instruction[1]))
        elif op == "INPUT" and len(instruction) == 2:
            stack.append(_integer(inputs[instruction[1]]))
        elif op == "READ" and len(instruction) == 2:
            index = instruction[1]
            if type(index) is not int or not 0 <= index < len(arguments):
                raise ValueError("bytecode read outside declared premises")
            stack.append(arguments[index])
        elif op == "NEG" and len(instruction) == 1 and stack:
            stack.append(-stack.pop())
        elif op in ("ADD", "MUL") and len(instruction) == 1 and len(stack) >= 2:
            right, left = stack.pop(), stack.pop()
            stack.append(left + right if op == "ADD" else left * right)
        else:
            raise ValueError("malformed bytecode or stack underflow")
    if len(stack) != 1:
        raise ValueError("bytecode must return exactly one value")
    return stack[0]


def _recompute(context: Context) -> Result:
    payload = context.task.payload
    values = [dep.value for dep in context.dependencies]
    return Result(direct(payload["source"], values, payload["inputs"]), 1 + len(values))


def _compile(context: Context) -> Result:
    source = context.task.payload
    op = source["op"]
    if op == "const":
        code = [["PUSH", source["value"]]]
    elif op == "input":
        code = [["INPUT", source["name"]]]
    elif op == "neg":
        code = [["READ", 0], ["NEG"]]
    elif op == "add":
        code = [["READ", 0], ["READ", 1], ["ADD"]]
    elif op == "mul":
        code = [["READ", 0], ["READ", 1], ["MUL"]]
    else:
        raise ValueError("unknown compiler operation")
    if len(context.dependencies) != ARITY[op]:
        raise ValueError("compiler arity mismatch")
    block = {"source": source, "links": list(context.task.deps), "code": code}
    return Result(block, 1 + len(code) + len(context.task.deps))


def _generate_trace(code: list, arity: int) -> list:
    """Certificate producer; the verifier below has its own transition rules."""
    stack, trace = [], [[]]
    for instruction in code:
        op, *operands = instruction
        if op == "PUSH":
            stack.append(["literal", operands[0]])
        elif op == "INPUT":
            stack.append(["input", operands[0]])
        elif op == "READ":
            if not 0 <= operands[0] < arity:
                raise ValueError("certificate read out of bounds")
            stack.append(["argument", operands[0]])
        elif op == "NEG":
            stack.append(["neg", stack.pop()])
        else:
            right, left = stack.pop(), stack.pop()
            stack.append([op.lower(), left, right])
        trace.append(clone(stack))
    return trace


def _certificate(context: Context) -> Result:
    compiled, *parents = context.dependencies
    block = compiled.value
    trace = _generate_trace(block["code"], ARITY[context.task.payload["op"]])
    result = {"compile": compiled.task.id, "source": context.task.payload,
              "block": block, "parents": [dep.task.id for dep in parents], "trace": trace}
    return Result(result, 1 + len(block["code"]) + len(parents))


def _verify_trace(code: list, trace: list, source: dict, arity: int):
    """Independent local checker: validates transitions and the exact claim."""
    if not isinstance(trace, list) or len(trace) != len(code) + 1 or trace[0] != []:
        raise ValueError("invalid certificate trace shape")
    state = []
    for position, instruction in enumerate(code):
        if not isinstance(instruction, list) or not instruction:
            raise ValueError("invalid instruction")
        command = instruction[0]
        if command == "READ":
            if len(instruction) != 2 or type(instruction[1]) is not int or not 0 <= instruction[1] < arity:
                raise ValueError("unjustified dependency read")
            following = state + [["argument", instruction[1]]]
        elif command == "PUSH":
            if len(instruction) != 2 or type(instruction[1]) is not int:
                raise ValueError("invalid integer literal")
            following = state + [["literal", instruction[1]]]
        elif command == "INPUT":
            if len(instruction) != 2 or not isinstance(instruction[1], str):
                raise ValueError("invalid input name")
            following = state + [["input", instruction[1]]]
        elif command == "NEG":
            if len(instruction) != 1 or len(state) < 1:
                raise ValueError("invalid unary stack transition")
            following = state[:-1] + [["neg", state[-1]]]
        elif command == "ADD" or command == "MUL":
            if len(instruction) != 1 or len(state) < 2:
                raise ValueError("invalid binary stack transition")
            rule = "add" if command == "ADD" else "mul"
            following = state[:-2] + [[rule, state[-2], state[-1]]]
        else:
            raise ValueError("unsupported instruction in certificate")
        if trace[position + 1] != following:
            raise ValueError("certificate transition does not follow the instruction")
        state = following
    operation = source["op"]
    if operation == "const":
        expected = ["literal", source["value"]]
    elif operation == "input":
        expected = ["input", source["name"]]
    elif operation == "neg":
        expected = ["neg", ["argument", 0]]
    elif operation == "add":
        expected = ["add", ["argument", 0], ["argument", 1]]
    elif operation == "mul":
        expected = ["mul", ["argument", 0], ["argument", 1]]
    else:
        raise ValueError("unsupported source claim")
    if state != [expected]:
        raise ValueError("compiled instruction block does not implement the specified operation")


def _check(context: Context) -> Result:
    compiled, certified, *parents = context.dependencies
    source = context.task.payload
    block, certificate = compiled.value, certified.value
    if compiled.task.stage != "compile" or certified.task.stage != "certificate":
        raise ValueError("checker requires actual compiler and certificate artifacts")
    if compiled.task.payload != source or block["source"] != source:
        raise ValueError("compiler source identity mismatch")
    if block["links"] != list(compiled.task.deps) or len(parents) != ARITY[source["op"]]:
        raise ValueError("compiler dependency identity or arity mismatch")
    if certificate["compile"] != compiled.task.id or certificate["block"] != block or certificate["source"] != source:
        raise ValueError("certificate does not describe the actual compiled artifact")
    if certificate["parents"] != [parent.value["certificate"] for parent in parents]:
        raise ValueError("certificate parent identities do not match checked parents")
    if block["links"] != [parent.value["compile"] for parent in parents]:
        raise ValueError("ordered compiler premises do not match checked premises")
    for parent in parents:
        if parent.task.stage != "check" or parent.value.get("accepted") is not True:
            raise ValueError("every premise needs an accepted check receipt")
    _verify_trace(block["code"], certificate["trace"], source, len(parents))
    receipt = {"accepted": True, "compile": compiled.task.id,
               "certificate": certified.task.id, "parents": [dep.task.id for dep in parents],
               "claim": "local symbolic block correspondence composed through every checked child"}
    return Result(receipt, 1 + len(block["code"]) + len(parents))


def _execute(context: Context) -> Result:
    compiled, checked, *parents = context.dependencies
    if checked.value.get("accepted") is not True or checked.value["compile"] != compiled.task.id:
        raise ValueError("execution requires an accepted receipt for this artifact")
    block = compiled.value
    values = [parent.value for parent in parents]
    value = execute_block(block["code"], values, context.task.payload["inputs"])
    return Result(value, len(block["code"]) + len(values))


def _factor(context: Context) -> Result:
    factors, offset, assignments = [], 0, 1
    for dimension in context.task.payload["dimensions"]:
        size = dimension["size"]
        if type(size) is not int or size <= 0:
            raise ValueError("each independent factor needs at least one alternative")
        selected = context.dependencies[offset:offset + size]
        if len(selected) != size or any(dep.task.stage != "check" or dep.value.get("accepted") is not True for dep in selected):
            raise ValueError("every factor alternative requires its own checked compiler artifact")
        factors.append({"name": dimension["name"], "alternatives": [
            {"compile": dep.value["compile"], "check": dep.task.id} for dep in selected]})
        assignments *= size
        offset += size
    if offset != len(context.dependencies):
        raise ValueError("factor dependency count mismatch")
    return Result({"representation": "independent-cartesian-tuples", "factors": factors,
                   "choice_assignments": assignments, "materialized_tuples": 0,
                   "claim": "independent coordinate choices only; no interaction or output enumeration claim"},
                  1 + len(context.dependencies))


def runners():
    return {"recompute": _recompute, "compile": _compile,
            "certificate": _certificate, "check": _check, "execute": _execute, "factor": _factor}


def make_engine(journal_path, scope: dict | None = None, **kwargs):
    complete = default_scope()
    if scope is not None:
        complete.update(clone(scope))
    complete["implementation"] = implementation()
    return Engine(journal_path, complete, runners(), **kwargs)


class Program:
    """Named mutable heads over immutable artifact DAGs.

    Edits traverse the reverse dependency cone of changed source names.
    Only startup reconstructs indices from all active source definitions.
    A source/binding transaction is one appended event; task nodes created
    before that event are harmless unattached history if planning fails.
    """

    def __init__(self, engine: Engine, definitions: dict[str, dict] | None = None):
        self.engine = engine
        self.definitions = clone(engine.sources)
        self.dependents = defaultdict(set)
        self.artifacts = {}
        self.proofs_by_compile = {}
        self.last_affected = []
        self.planned_nodes = 0
        self.validation_visits = 0
        self.reverse_edge_visits = 0
        self.planning_argument_reads = 0
        for name, definition in self.definitions.items():
            for argument in definition.get("args", []):
                self.dependents[argument].add(name)
            self.artifacts[name] = {stage: engine.bindings[f"{name}/{stage}"] for stage in STAGES}
        for node in engine.by_stage.get("check", []):
            task = engine.tasks[node]
            self.proofs_by_compile[task.deps[0]] = (task.deps[1], node)
        # Validate the whole retained view once; hot operations use this marker.
        current_scope = canonical(engine.scope)
        self._artifact_scope = (current_scope if all(
            canonical(engine.tasks[node].scope) == current_scope
            for bundle in self.artifacts.values() for node in bundle.values()) else None)
        self.apply(definitions if definitions is not None else {})

    def _validate_changes(self, changes: dict[str, dict], candidate: dict[str, dict]):
        for name, definition in changes.items():
            for argument in definition.get("args", []):
                if argument not in candidate:
                    raise ValueError(f"unknown source premise {argument}")
        done, active = set(), set()

        for root in changes:
            if changes[root].get("args", []) == self.definitions.get(root, {}).get("args", []):
                continue
            stack = [(root, False)]
            while stack:
                name, exiting = stack.pop()
                if exiting:
                    active.remove(name)
                    done.add(name)
                    continue
                if name in active:
                    raise ValueError("cyclic source graph: no seeded topological derivation")
                if name in done:
                    continue
                self.validation_visits += 1
                active.add(name)
                stack.append((name, True))
                for argument in reversed(candidate[name].get("args", [])):
                    stack.append((argument, False))

    def apply(self, definitions: dict[str, dict]):
        changes = {name: normalize(name, value) for name, value in definitions.items()}
        changes = {name: value for name, value in changes.items() if self.definitions.get(name) != value}
        candidate = ChainMap(changes, self.definitions)
        self._validate_changes(changes, candidate)
        scope = self.engine.scope
        scope_identity = canonical(scope)
        if self._artifact_scope != scope_identity:
            scope = clone(scope)
            scope["implementation"] = implementation()
            scope_identity = canonical(scope)
        scope_changed = self._artifact_scope != scope_identity
        if not changes and not scope_changed:
            if not same_identity(self.engine.scope, scope):
                self.engine.set_scope(scope)
            self.last_affected = []
            return {"affected": [], "planned": 0}
        touched = {argument for name, definition in changes.items()
                   for argument in [*self.definitions.get(name, {}).get("args", []),
                                    *definition.get("args", [])]}
        reverse_changes = {argument: set(self.dependents.get(argument, set())) for argument in touched}
        reverse = ChainMap(reverse_changes, self.dependents)
        for name, definition in changes.items():
            for previous in self.definitions.get(name, {}).get("args", []):
                reverse[previous].discard(name)
            for argument in definition.get("args", []):
                reverse[argument].add(name)
        if scope_changed:
            # Plan the edited candidate once, including its unchanged parents.
            affected = set(candidate)
        else:
            affected = set(changes)
            pending = deque(sorted(changes))
            while pending:
                name = pending.popleft()
                for user in sorted(reverse.get(name, set())):
                    self.reverse_edge_visits += 1
                    if user not in affected:
                        affected.add(user)
                        pending.append(user)
        if not same_identity(self.engine.scope, scope):
            self.engine.set_scope(scope)
        artifacts, order = self._plan(candidate, affected)
        bindings = {f"{name}/{stage}": node for name, bundle in artifacts.items() for stage, node in bundle.items()}
        self.engine.commit_update(changes, bindings)
        self.definitions.update(changes)
        self.dependents.update(reverse_changes)
        self.artifacts.update(artifacts)
        # Advance only after the source/binding transaction has succeeded.
        self._artifact_scope = scope_identity
        self.last_affected = order
        self.planned_nodes += len(order)
        return {"affected": order, "planned": len(order)}

    def _plan(self, definitions: dict, affected: set):
        produced, order = {}, []
        outstanding = {name: len(set(definitions[name].get("args", [])) & affected) for name in affected}
        local_users = defaultdict(set)
        for name in affected:
            for argument in definitions[name].get("args", []):
                self.planning_argument_reads += 1
                if argument in affected:
                    local_users[argument].add(name)
        ready = deque(sorted(name for name, count in outstanding.items() if count == 0))
        while ready:
            name = ready.popleft()
            definition = definitions[name]
            children = [produced[argument] if argument in produced else self.artifacts[argument]
                        for argument in definition.get("args", [])]
            source = specification(name, definition)
            inputs = {name: definition["value"]} if definition["op"] == "input" else {}
            bundle = {}
            bundle["recompute"] = self.engine.intern("recompute", {"source": source, "inputs": inputs},
                                                       [child["recompute"] for child in children])
            bundle["compile"] = self.engine.intern("compile", source, [child["compile"] for child in children])
            bundle["certificate"] = self.engine.intern("certificate", source,
                [bundle["compile"], *[child["certificate"] for child in children]])
            bundle["check"] = self.engine.intern("check", source,
                [bundle["compile"], bundle["certificate"], *[child["check"] for child in children]])
            bundle["execute"] = self.engine.intern("execute", {"inputs": inputs},
                [bundle["compile"], bundle["check"], *[child["execute"] for child in children]])
            produced[name] = bundle
            self.proofs_by_compile[bundle["compile"]] = (bundle["certificate"], bundle["check"])
            order.append(name)
            for user in sorted(local_users[name]):
                outstanding[user] -= 1
                if outstanding[user] == 0:
                    ready.append(user)
        if len(produced) != len(affected):
            raise ValueError("source planning did not produce a complete topological order")
        return produced, order

    def edit(self, name: str, definition: dict):
        return self.apply({name: definition})

    def change_scope(self, scope: dict):
        complete = clone(scope)
        complete["implementation"] = implementation()
        self.engine.set_scope(complete)
        return self.apply({})

    def run(self, outputs: list[str]) -> dict:
        if self._artifact_scope != canonical(self.engine.scope):
            self.change_scope(self.engine.scope)
        roots = []
        for name in outputs:
            if name not in self.artifacts:
                raise ValueError(f"unknown output {name}")
            roots.extend(self.artifacts[name][stage] for stage in ("recompute", "execute", "check"))
        values = self.engine.demand(roots)
        result = {}
        for index, name in enumerate(outputs):
            interpreted, executed, receipt = values[index * 3:index * 3 + 3]
            if interpreted != executed:
                raise ValueError("compiled execution disagrees with direct source interpretation")
            result[name] = {"value": interpreted, "executed": executed, "check": receipt}
        return result

    def factor_product(self, alternatives: dict[str, list[str]]) -> dict:
        names = list(dict.fromkeys(name for choices in alternatives.values() for name in choices))
        self.run(names)
        payload = {"dimensions": [{"name": dimension, "size": len(choices)}
                                  for dimension, choices in alternatives.items()]}
        deps = [self.artifacts[name]["check"] for choices in alternatives.values() for name in choices]
        root = self.engine.intern("factor", payload, deps)
        return {"task": root, **self.engine.demand([root])[0]}

    def metrics(self) -> dict:
        result = self.engine.metrics()
        result.update({"source_nodes_planned": self.planned_nodes,
                       "source_validation_visits": self.validation_visits,
                       "source_reverse_edge_visits": self.reverse_edge_visits,
                       "source_argument_reads": self.planning_argument_reads})
        return result

    def export_bridge(self, since: int = 0, outputs: list[str] | None = None,
                      include_environment: bool = True, execution_since: int = 0) -> dict:
        """Export completed compiler and captured-input execution suffixes.

        Rows use stable completion-order indices. Every linked child completed
        first. No symbolic expression or proof subtree is expanded. Export is
        an explicit audit operation; it does not execute pending compiler work.
        """
        completed = self.engine.completed_by_stage.get("compile", [])
        executions = self.engine.completed_by_stage.get("execute", [])
        if not 0 <= since <= len(completed):
            raise ValueError("invalid compiler prefix cursor")
        if not 0 <= execution_since <= len(executions):
            raise ValueError("invalid execution prefix cursor")
        rows = []
        for node in completed[since:]:
            task = self.engine.tasks[node]
            block = self.engine.results[node]
            certificate, checked = self.proofs_by_compile.get(node, (None, None))
            rows.append({"id": self.engine.completed_position[node], "task": node,
                         "operation": task.payload, "premises": [self.engine.completed_position[dep] for dep in task.deps],
                         "code": clone(block["code"]), "links": list(task.deps), "scope": clone(task.scope),
                         "artifact": clone(block),
                         "certificate": certificate, "check": checked,
                         "check_parents": list(self.engine.tasks[checked].deps[2:]) if checked is not None else [],
                         "checked": checked in self.engine.results if checked is not None else False})
        execution_rows = []
        for node in executions[execution_since:]:
            task = self.engine.tasks[node]
            execution_rows.append({"id": self.engine.completed_position[node], "task": node,
                                   "descriptor": clone(task.descriptor()),
                                   "compiler_row": self.engine.completed_position[task.deps[0]],
                                   "parents": [self.engine.completed_position[dep] for dep in task.deps[2:]],
                                   "value": self.engine.results[node]})
        environment = ({name: definition["value"] for name, definition in self.definitions.items()
                        if definition["op"] == "input"} if include_environment else None)
        selected = outputs if outputs is not None else (sorted(self.artifacts) if include_environment else [])
        observations = {}
        for name in selected:
            bundle = self.artifacts[name]
            observations[name] = {"compile_task": bundle["compile"],
                                  "scope": clone(self.engine.tasks[bundle["compile"]].scope),
                                  "row": self.engine.completed_position.get(bundle["compile"]),
                                  "recompute_task": bundle["recompute"], "execute_task": bundle["execute"],
                                  "value": self.engine.results.get(bundle["recompute"]),
                                  "executed": self.engine.results.get(bundle["execute"])}
        return {"format": "incremental-linked-integer-blocks-v1", "start": since,
                "prefix": self.engine.completed_chain["compile"][since],
                "tail": self.engine.completed_chain["compile"][len(completed)],
                "end": len(completed), "rows": rows, "environment": environment,
                "execution_start": execution_since, "execution_end": len(executions),
                "execution_prefix": self.engine.completed_chain["execute"][execution_since],
                "execution_tail": self.engine.completed_chain["execute"][len(executions)],
                "execution_rows": execution_rows, "observations": observations,
                "scope": clone(self.engine.scope), "metrics": self.metrics(),
                "kernel_proof": "not supplied by Python; independent Lean bridge required"}


def cold_oracle(definitions: dict[str, dict], outputs: list[str]) -> dict[str, int]:
    """Independent cold interpreter, rebuilding all requested ancestors."""
    values = {}
    active = set()

    for root in outputs:
        stack = [(root, False)]
        while stack:
            name, expanded = stack.pop()
            if name in values:
                continue
            definition = definitions[name]
            op = definition["op"]
            if op not in ("const", "input", "neg", "add", "mul"):
                raise ValueError("unsupported cold source operation")
            if not expanded:
                if name in active:
                    raise ValueError("cyclic cold source graph")
                active.add(name)
                stack.append((name, True))
                for argument in reversed(definition.get("args", [])):
                    stack.append((argument, False))
                continue
            if op == "const" or op == "input":
                result = definition["value"]
            elif op == "neg":
                result = -values[definition["args"][0]]
            elif op == "add":
                result = values[definition["args"][0]] + values[definition["args"][1]]
            else:
                result = values[definition["args"][0]] * values[definition["args"][1]]
            active.remove(name)
            values[name] = result
    return {name: values[name] for name in outputs}
