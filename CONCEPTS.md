# Concept index

One canonical definition per concept lives in `shared/core` (Lake package `software-core`,
library `SoftwareCore`). Every thesis that defines its own version is tied to it by a bridge in
`shared/core/bridges/`: the bridge imports the thesis's own module, compiled from the thesis's own
source, and proves the two equivalent. `shared/core/check.sh` builds all of them and checks axioms
(only propext, Classical.choice, Quot.sound allowed). A variant that is not the same concept is
listed as different, with the reason.

## Closure: `SoftwareCore.Derives B R` (least set containing roots B, closed under rules R)

| Thesis variant | Status | Bridge theorem |
|---|---|---|
| optimality `Qualification.Derives` (also the identical copies in testing-is-redundant, benchmarking-is-redundant-and-suboptimal) | equivalent | `Bridge.Qualification.derives_iff` |
| frontier-is-solvable `Canon.Derives` (also the identical copy in redundant-compute-expands/proof) | equivalent | `Bridge.Canon.derives_iff`, `hypergraph_derives_iff` |
| compilers-lose-info `CompilersLoseInfo.Derives g` | equivalent with B = g.roots, R = g.edges | `Bridge.CompilersLoseInfo.derives_iff` |
| is-incrementally-safe `Family.Saturation.Derives base rules` | equivalent with R = `ofPairs rules` | `Bridge.Saturation.derives_iff` |
| optimality `PortableAdapter.Derives roots edges` | equivalent with R = `ofRecords Edge.premises Edge.conclusion edges` | `Bridge.PortableAdapter.derives_iff` |

## Closedness: `SoftwareCore.Closed R X`

| Thesis variant | Status | Bridge theorem |
|---|---|---|
| optimality `Qualification.Closed` (and its two copies) | equivalent | `Bridge.Qualification.closed_iff` |
| is-quantifiable `Spine.Closed s` | equivalent with R = `ofRecords` of s.rules, X = membership in s.seeds | `Bridge.Spine.closed_iff` |
| redundant-compute-expands `ClosureWorklist.Closed es known` | equivalent with R = `ofPairs es` | `Bridge.ClosureWorklist.closed_iff` |
| is-more-traceable-than-you-think `HeadedReturn.Closed lift` | different concept: every lifted edge's head is a node of the lifted graph, not rule closure | none |

## Pareto order: `SoftwareCore.NoWorse x y`, `SoftwareCore.Dominates x y` on cost vectors `I → α`

| Thesis variant | Status | Bridge theorem |
|---|---|---|
| frontier-is-solvable `NoWorse cost`, `Dominates cost` (Int) | equivalent | `Bridge.Frontier.noWorse_iff`, `dominates_iff` |
| is-reversible resolution-lab `Weak`, `Dominates` (Nat) | equivalent | `Bridge.CompositionalPruning.weak_iff`, `dominates_iff` |
| persistence-is-minimal `Dominates axes` | equivalent with I = the named axes | `Bridge.Persistence.dominates_iff` |
| is-quantifiable `Pareto.noWorse`, `Pareto.dominates` (Nat × Nat) | equivalent with the pair read as a two-axis vector | `Bridge.QuantifiablePareto.noWorse_iff`, `dominates_iff` |
| doesnt-need-review `Chain.Optimality.noWorse` (Nat × Nat) | same shape as is-quantifiable's; not bridged yet: its module imports is-composable through Lake | none yet |
| benchmarking-is-redundant-and-suboptimal `Dominates` | different: also requires coverage (`Covers`) | none |
| fuzzing-is-suboptimal `Dominates` | different: coverage inclusion plus one scalar cost | none |
| doesnt-have-to-regress `Bound.noWorse` | different: interval bounds, Bool | none |
| is-quantifiable `Interface.noWorse` | different: measures plus behavior | none |

## Gates and engines

| Kind | One copy | Used by |
|---|---|---|
| Family Lean gate `proof/check.sh` | `shared/gates/proof-check.sh` | 8 theses (links) |
| Solver gate | `shared/gates/proof-check-solver.sh` | checking-is-choral, qualification-is-two-sided |
| Lake gate `check.sh` | `shared/gates/lake-check.sh` | doesnt-have-to-regress, is-composable, is-incrementally-certifiable |
| Twin gate | `shared/gates/twin-check.sh` | estate-is-censused, proofs-are-portable |
| Incremental engine | `shared/incremental/gate.py`, `frontier.py`, `fuzz_s1.py` | redundant-compute-expands, is-reversible, is-a-parametric-language-model, has-a-highest-minimal-axis |
| Certificate checker | `shared/gates/check.py` | certification-is-monotone, proofs-are-portable |
| Lean files Lake cannot link | 3 groups kept as guarded copies | `consolidation/copies.tsv`, checked by `consolidation/check-copies.py` |
