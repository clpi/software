# software-frontier-is-solvable

Lean 4.19.0 statements for a directed hypergraph of program states, the behaviors an environment dial leaves visible, a four-color qualification of those states, and the Pareto frontier of finite test schedules. Dominance and the frontier are the ones proved in `clpi/software-optimality` at `16a6c690cf4ec4dedda34328e165da995d7592ae`. That package pins `clpi/software-is-quantifiable` at `f370992611d8c722e4897e67dbb8eaecf3d872ed`. This repository pins both, and `lake-manifest.json` resolves each package to that single commit.

`ThreeValuedGate.frontier_no_dominator`, `unknown_blocks_dominance`, `unknown_blocks_dominance_canonical`, and `known_agrees_canonical` are imported and applied. They are not re-proved here. Schedule dominance is `Interface.dominates` on the gate's measure space, which `CanonicalDominance` identifies with the one-axis profile order and which `known_agrees_canonical` identifies with the three-valued gate on fully known natural readings.

## What is proved

A directed hypergraph has states as vertices and hyperedges as transitions from a set of states to a set of states, labeled by an e-class and a knowledge threshold. Its incidence matrix is a function of vertex and edge. `Hyper.roundtrip` shows that decoding that function recovers a bounded hypergraph exactly.

`Hyper.Observed.mask` keeps an edge when the dial is at least the edge's threshold. `subset` says the masked graph's incidences are incidences of the complete graph. `monotone` says raising the dial never drops an incidence that was already visible.

`Hyper.Paint.color` is a total function into `intended`, `stray` (observed, not intended), `gap` (intended, not observed), and `unknown`. `meant` is true only for `intended`. A state colored `unknown` is not a member of `qualified`. `Solve.Sched.gapblocks` sends that missing reading through `unknown_blocks_dominance` and `unknown_blocks_dominance_canonical`, so it is not a dominating improvement. `Red.shifts` is the concrete counterexample: scoring the unknown job as intended changes the frontier. `Red.agrees` is that filled scoring, through `known_agrees_canonical` and `CanonicalDominance.one_iff`. `Red.rejects` is a dominated schedule reported as the frontier; `FiniteFrontier.certificate` is false. `Red.guarded` is `frontier_no_dominator` on the filled space.

A schedule is a `FiniteSchedules.Schedule`: one venue and start for each test. Feasibility, including precedence and no overlap on a venue, is `FiniteSchedules.Feasible`. `Solve.Sched.acyclic` adds that a forward precedence list is a DAG. The carrier of a `ThreeValuedGate.FiniteSpace` is `Fin` of the feasible list, so `nothingOutside` and `noCoverageGaps` hold for that finite set. Readings are three fully known naturals: behaviors clarified (maximize), makespan (minimize), and the number of venues used (minimize).

`Solve.main` is the exhaustive solver on any such space. Its output is `FiniteFrontier.frontier` under `dominatesB`. Every output point is free of `ComparisonContract` dominance by `frontier_no_dominator`, and free of `Interface.dominates` by `known_agrees_canonical`. Every point free of `Interface.dominates` is emitted, and so is its reading vector. `Solve.checked` is the certificate checker accepting that frontier. `Solve.named` returns, for a dominated point, one feasible point that dominates it. `Solve.cardsound` says every frontier card carries that acceptance and names no dominator.

`Solve.Bench.corollary` is the same theorem when the first axis is variance reduction from the venue of each placement. `Fuzz.expect` is the weighted sum of a stated finite distribution. There is no fuzzing optimality corollary.

`Frontier.lean` remains the earlier qualification-frontier development. It is not the dominance used for schedules.

## Limits

Multi-objective scheduling with precedence on parallel machines is NP-hard in general, so this exact solver enumerates the finite feasible set and is exponential in that set. A faster heuristic is admitted only when its output is checked against this frontier on the instance, by `Solve.accept` or an equivalent certificate. "Optimal for arbitrary software" means exact for every finite instance extracted from it. Nothing is claimed about programs that have not been cut down to a finite `FiniteSpace`, about costs that are not the supplied readings, or about candidates outside that space.

No regret bound is proved for fuzzing. An expectation computed from a stated finite distribution can be placed in a reading and then falls under `Solve.main` only as that deterministic vector. That is not a bound on the regret of an adaptive fuzzer, and it is not stated as a corollary.

The exhaustive listing is the reference. It does not claim a polynomial algorithm, a universal optimum outside the enumerated feasible list, or that a physical measurement equals the integer reading supplied to the gate.

## Reproduce

```sh
lake build -R -KwarningAsError=true
```

`./check.sh` runs that command after rejecting `sorry`, `admit`, `axiom`, and `native_decide`. The build prints `#print axioms` for `Solve.main`. The five `#eval` lines in `Instances.lean` are a precedence chain, three venues, a variance-reduction bench, a fuzz expectation used only as a numeric axis, and a dial-0 coloring of the demo hypergraph together with a two-test precedence schedule.
