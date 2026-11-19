# Software persistence is minimal

The claim: redundant computation and Pareto-optimal
compression of persistent data to its minimum representation
are provable — rigorously, incrementally, certifiably, and
machine-checkably — over a hypergraph of recorded
interactions, including functional representation and
semi-persistence. This repository carries the proved model:
a Lean development in which derivability from persistent
state, certificate checking, finite candidate spaces,
domination, minimum-by-construction choice, composition of
part minima, and version readability are all theorems, with
standing controls exhibiting exactly where each
load-bearing condition bites.

## Contents

- `defs.md` — every term of the model defined at
  implementer resolution, each tied to its Lean counterpart.
- `spec.md` — the claim in its author's terms, the
  executable method with the measure each step carries,
  the theorem inventory at its honest strength, and a
  falsification protocol for every claim not proven
  outright.
- `proof/Core.lean` — the model: derivability, certificates,
  representations and minima, composition, semi-persistence.
- `proof/Controls.lean` — four standing controls, each a
  proved negation over concrete numbers.
- `proof/check.sh` — the family gate.

## The gate

`proof/check.sh` compiles every Lean file under `proof/`
with warnings as errors, rejects every proof escape token,
and enforces that every printed axiom lies in the allowed
set {propext, Classical.choice, Quot.sound}. At the landed
pin it passes cold; the printed axioms actually used are
exactly {propext, Quot.sound}, and several theorems depend
on no axioms at all. The gate log is `proof/CHECK.log`.
Toolchain: Lean 4.19.0 (`proof/lean-toolchain`).
