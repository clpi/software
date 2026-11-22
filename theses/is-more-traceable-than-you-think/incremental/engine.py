"""A single-writer append-only task DAG with exact, collision-safe interning.

A digest selects a bucket; canonical descriptor bytes decide identity. Every
premise is an earlier task ID, and ordered duplicates are preserved. Cached
results are immutable journal records. The generic engine assumes runners are
pure and declare every semantic dependency in payload, ordered premises, or
scope. The reference pipeline supplies implementation identities itself.
"""
from __future__ import annotations

from collections import Counter, defaultdict
from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
from typing import Any, Callable, Iterable


def canonical(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"),
                      ensure_ascii=False, allow_nan=False).encode("utf-8")


def same_identity(left: Any, right: Any) -> bool:
    return canonical(left) == canonical(right)


def clone(value: Any) -> Any:
    return json.loads(canonical(value))


@dataclass(frozen=True)
class Task:
    id: int
    stage: str
    payload: Any
    deps: tuple[int, ...]
    scope: Any

    def descriptor(self) -> dict:
        return {"stage": self.stage, "payload": self.payload,
                "deps": list(self.deps), "scope": self.scope}


@dataclass(frozen=True)
class Dependency:
    task: Task
    value: Any


@dataclass(frozen=True)
class Context:
    task: Task
    dependencies: tuple[Dependency, ...]


@dataclass(frozen=True)
class Result:
    value: Any
    work: int = 1


class Engine:
    """Durable task/result indices, with no journal replay on a hot update.

    One writer owns a journal. Restart replay is explicit and linear in journal
    records. A malformed or truncated journal is refused; it is never repaired
    by deleting history. Local journal integrity and runner purity are trusted
    boundaries, not authentication claims.
    """

    def __init__(self, journal_path, scope: dict, runners: dict[str, Callable],
                 digest: Callable[[bytes], str] | None = None):
        self.path = Path(journal_path)
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.scope = clone(scope)
        self.runners = dict(runners)
        self.digest = digest or (lambda value: hashlib.sha256(value).hexdigest())
        self.tasks: list[Task] = []
        self.results: dict[int, Any] = {}
        self.bindings: dict[str, int] = {}
        self.sources: dict[str, Any] = {}
        self.buckets: dict[str, list[tuple[bytes, int]]] = defaultdict(list)
        self.by_stage: dict[str, list[int]] = defaultdict(list)
        self.completed_by_stage: dict[str, list[int]] = defaultdict(list)
        self.completed_chain: dict[str, list[str]] = defaultdict(lambda: [""])
        self.completed_position: dict[int, int] = {}
        self.executed = Counter()
        self.attempted = Counter()
        self.failed = Counter()
        self.reused = Counter()
        self.work = Counter()
        self.interned = Counter()
        self.intern_reused = Counter()
        self.events = 0
        self.replay_events = 0
        self.dependency_visits = 0
        self.shared_visits = 0
        self.key_comparisons = 0
        self.descriptor_bytes = 0
        self._tail = ""
        if self.path.exists():
            with self.path.open("rb") as stream:
                for line in stream:
                    if not line.endswith(b"\n"):
                        raise ValueError("truncated journal: append-only recovery requires a verified complete record")
                    record = json.loads(line)
                    checksum = record.pop("checksum")
                    if checksum != hashlib.sha256(canonical(record)).hexdigest():
                        raise ValueError("journal record checksum mismatch")
                    if record["previous"] != self._tail:
                        raise ValueError("journal chain mismatch")
                    self._ingest(record["event"])
                    self._tail = checksum
                    self.replay_events += 1
        self._stream = self.path.open("ab")

    def close(self):
        self._stream.close()

    def __enter__(self):
        return self

    def __exit__(self, *_):
        self.close()

    def set_scope(self, scope: dict):
        self.scope = clone(scope)

    def _append(self, event: dict):
        record = {"previous": self._tail, "event": event}
        checksum = hashlib.sha256(canonical(record)).hexdigest()
        record["checksum"] = checksum
        self._stream.write(canonical(record) + b"\n")
        self._stream.flush()
        os.fsync(self._stream.fileno())
        self._ingest(event)
        self._tail = checksum

    def _ingest(self, event: dict):
        kind = event["kind"]
        if kind == "task":
            description = clone(event["descriptor"])
            node = event["id"]
            if type(node) is not int or node != len(self.tasks):
                raise ValueError("task IDs must be append-only consecutive indices")
            deps = description["deps"]
            if any(type(dep) is not int or dep < 0 or dep >= node for dep in deps):
                raise ValueError("every premise must refer to an earlier task")
            raw = canonical(description)
            bucket = str(self.digest(raw))
            if bucket != event["bucket"]:
                raise ValueError("journal task digest mismatch")
            for previous, _ in self.buckets[bucket]:
                self.key_comparisons += 1
                if previous == raw:
                    raise ValueError("duplicate structural task record")
            task = Task(node, description["stage"], description["payload"],
                        tuple(deps), description["scope"])
            self.tasks.append(task)
            self.buckets[bucket].append((raw, node))
            self.by_stage[task.stage].append(node)
            self.interned[task.stage] += 1
        elif kind == "result":
            node = event["task"]
            if type(node) is not int or not 0 <= node < len(self.tasks):
                raise ValueError("result refers to an unknown task")
            task = self.tasks[node]
            if node in self.results:
                raise ValueError("a task result may only be published once")
            if any(dep not in self.results for dep in task.deps):
                raise ValueError("result publication requires every premise result")
            if type(event["work"]) is not int or event["work"] < 0:
                raise ValueError("work must be a nonnegative integer")
            self.results[node] = clone(event["value"])
            self.completed_position[node] = len(self.completed_by_stage[task.stage])
            self.completed_by_stage[task.stage].append(node)
            chain = self.completed_chain[task.stage]
            chain.append(hashlib.sha256(canonical({
                "previous": chain[-1], "task": task.id,
                "descriptor": task.descriptor(), "value": self.results[node]
            })).hexdigest())
            self.executed[task.stage] += 1
            self.work[task.stage] += event["work"]
        elif kind == "update":
            for name, node in event["bindings"].items():
                if type(node) is not int or not 0 <= node < len(self.tasks):
                    raise ValueError("binding refers to an unknown task")
                self.bindings[name] = node
            self.sources.update(clone(event["sources"]))
        else:
            raise ValueError(f"unknown journal event: {kind}")
        self.events += 1

    def intern(self, stage: str, payload: Any, deps: Iterable[int] = ()) -> int:
        if stage not in self.runners:
            raise ValueError(f"no runner for stage {stage}")
        deps = tuple(deps)
        if any(type(dep) is not int or not 0 <= dep < len(self.tasks) for dep in deps):
            raise ValueError("every premise must be an already interned task")
        description = clone({"stage": stage, "payload": payload,
                             "deps": list(deps), "scope": self.scope})
        raw = canonical(description)
        self.descriptor_bytes += len(raw)
        bucket = str(self.digest(raw))
        for previous, node in self.buckets[bucket]:
            self.key_comparisons += 1
            if previous == raw:
                self.intern_reused[stage] += 1
                return node
        node = len(self.tasks)
        self._append({"kind": "task", "id": node,
                      "descriptor": description, "bucket": bucket})
        return node

    def commit_update(self, sources: dict[str, Any], bindings: dict[str, int]):
        for node in bindings.values():
            if type(node) is not int or not 0 <= node < len(self.tasks):
                raise ValueError("binding refers to an unknown task")
        changed_sources = {name: clone(value) for name, value in sources.items()
                           if name not in self.sources or not same_identity(self.sources[name], value)}
        changed_bindings = {name: node for name, node in bindings.items()
                            if self.bindings.get(name) != node}
        if changed_sources or changed_bindings:
            self._append({"kind": "update", "sources": changed_sources,
                          "bindings": changed_bindings})

    def bind(self, name: str, node: int):
        self.commit_update({}, {name: node})

    def demand(self, roots: Iterable[int]) -> list[Any]:
        roots = tuple(roots)
        if any(type(node) is not int or not 0 <= node < len(self.tasks) for node in roots):
            raise ValueError("demand refers to an unknown task")
        seen = set()
        for root in roots:
            stack = [(root, False)]
            while stack:
                node, expanded = stack.pop()
                task = self.tasks[node]
                if node in seen:
                    self.shared_visits += 1
                    continue
                if node in self.results:
                    self.reused[task.stage] += 1
                    seen.add(node)
                    continue
                if not same_identity(task.scope, self.scope):
                    raise ValueError("cannot execute an unresolved historical task under a different scope")
                if not expanded:
                    stack.append((node, True))
                    for dep in reversed(task.deps):
                        self.dependency_visits += 1
                        stack.append((dep, False))
                    continue
                dependencies = tuple(
                    Dependency(Task(dep, self.tasks[dep].stage,
                                    clone(self.tasks[dep].payload), self.tasks[dep].deps,
                                    clone(self.tasks[dep].scope)), clone(self.results[dep]))
                    for dep in task.deps)
                context = Context(Task(task.id, task.stage, clone(task.payload),
                                       task.deps, clone(task.scope)), dependencies)
                self.attempted[task.stage] += 1
                try:
                    produced = self.runners[task.stage](context)
                    result = produced if isinstance(produced, Result) else Result(produced)
                    value = clone(result.value)
                    if type(result.work) is not int or result.work < 0:
                        raise ValueError("runner work must be a nonnegative integer")
                except Exception:
                    self.failed[task.stage] += 1
                    raise
                self._append({"kind": "result", "task": node,
                              "value": value, "work": result.work})
                seen.add(node)
        return [clone(self.results[node]) for node in roots]

    def metrics(self) -> dict:
        return {"executed": dict(self.executed), "reused": dict(self.reused),
                "attempts_this_session": dict(self.attempted), "failures_this_session": dict(self.failed),
                "work": dict(self.work), "interned": dict(self.interned),
                "intern_reused": dict(self.intern_reused),
                "tasks": len(self.tasks), "results": len(self.results),
                "events": self.events, "replay_events": self.replay_events,
                "dependency_visits": self.dependency_visits,
                "shared_visits": self.shared_visits,
                "key_comparisons_this_session": self.key_comparisons,
                "descriptor_bytes_this_session": self.descriptor_bytes,
                "journal_bytes": self.path.stat().st_size,
                "hot_history_scans": 0}


def difference(after: dict, before: dict) -> dict:
    result = {}
    for key, value in after.items():
        if isinstance(value, dict):
            previous = before.get(key, {})
            result[key] = {name: count - previous.get(name, 0)
                           for name, count in value.items() if count != previous.get(name, 0)}
        elif isinstance(value, int):
            result[key] = value - before.get(key, 0)
    return result
