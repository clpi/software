# software-checking-is-choral

Checking that splits across independent checkers, with the verdicts
joined, accepts exactly what the whole check accepts.

## The claim

A proof estate's cold gate can be split by derivation cone: the
development's modules are partitioned into cones from the real
dependency graph, each cone is checked by a different checker
running the pinned toolchain, the cones exchange their checked
artifacts along every cross-cone dependency, and the joined verdict
— every cone accepts, and the joined axiom audit — is the whole
gate's verdict and audit, exactly.

## What is proved here

The proof core (proof/Choral.lean, pinned Lean 4.19.0, core only)
models a development as modules with local check outcomes, a
dependency list per module, and a rank function that decreases
along every dependency — the level assignment of the real import
graph is such a rank. Against that model it proves:

- `conepoint`: a cone's values equal the whole check's values on
  every module of the cone, when the cone's boundary — the values
  it reads for out-of-cone dependencies — agrees with the whole
  check outside the cone.
- `joinediff`: the joined verdict over a covering family of three
  cones is the whole verdict, in both directions. Coverage is the
  only demand on the family; the verdict join needs no
  disjointness.
- `auditpoint` and `auditjoin`: a module's audit agrees between
  the cone environment and the whole environment, and the audit
  list of a concatenated module list is the concatenation of the
  cone audit lists.

Two standing controls (proof/Controls.lean) witness that the two
premises are load-bearing: with a false boundary, a cone fails a
module the whole check passes (`boundarymatters`); with a family
that does not cover the development, the joined verdict holds
while the whole verdict fails, even with the honest boundary
(`covermatters`).

Axiom audit at the founding pin: `fueleval` and `wholefold` depend
on no axioms; `conepoint`, `joinediff`, `auditpoint`, and
`auditjoin` depend on propext and Quot.sound only; the controls
depend on propext only. Nothing depends on Classical.choice, and
nothing is admitted by sorry. The gate (proof/check.sh) compiles
every file cold with warnings as errors and fails on any printed
principle outside {propext, Classical.choice, Quot.sound}.

## Premises

- The rank premise: the dependency graph is acyclic, witnessed by
  a rank function decreasing along every dependency. Lean import
  graphs are acyclic by construction, and the level assignment
  computed from the graph is the witness.
- The boundary premise: the values a cone reads outside itself are
  the whole check's values there. Operationally this is the join's
  contract — the artifacts a cone receives along a cross-cone
  dependency are the producing cone's own checked outputs, carried
  unchanged.
- The audit premise: a module's audit reads the checking
  environment only at the module and its dependencies. The estate's
  axiom audit has this shape: a check file's report is computed
  from the declarations it names and what they rest on.
- Each checker runs the toolchain the subject development pins.
  This is an operational premise of the experiment, not a premise
  of the theorems.

## The instance

instances/ holds the cone partition of the estate's largest proof
gate — the Lean development of clpi/idol-semi (the SemperProofs and
Conform libraries) — at its two successive proof-tree heads,
computed from the real import graph and verified for coverage:
every module in exactly one cone, every cross-cone dependency
enumerated. instances/PARTITION.md states the method and the
figures.

## What is not claimed

- The split gate over that instance has not been run. No wall-clock
  figure, speedup, or fraction is stated anywhere in this repo;
  the experiment's runs are future work with a named blocker,
  recorded in the research register that commissioned this repo.
- The theorems are about the model. That the model fits a real
  gate is argued per gate in the spec (SPEC.md): the whole check's
  build verdict is the conjunction of per-module elaborations over
  dependency artifacts, and the audit is per check file. The fit is
  a premise of the experiment, not a theorem of this repo.
- No other development's partition is computed here.
