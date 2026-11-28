# Witnessed saturation inside the bound

Everything here is stated inside the finite resolved bound: a finite
set of terms, a finite rule set, finite witness points, finite fuel.

## The answer

Inside the bound, the bounded decider (`--engine decide`) beats every
other engine here: on every suite it finds every join any engine finds,
and it uses no more operations, time or memory than any of them (38 of
38 comparisons, gate `decider at least as good as every engine`).

It is the simplest possible procedure for this job. Both terms go into
one hash-consed DAG, identical roots join with no work, and otherwise
every resolved point is evaluated bottom-up, with the shared subterms
evaluated once, stopping at the first point that differs.

What holds by construction, and what is only measured:

- **Joins, proved.** It joins `o(a)` and `o(b)` exactly when they agree
  on every resolved point (`boundedexact`). Any engine sound for a
  meaning the observer reads can only state joins it already holds,
  whether of observed terms (`decidermax`) or of raw terms
  (`decidercovers`). So no sound procedure finds a join it misses.
- **Allocation, by construction.** It allocates no rewrite nodes.
- **Operations against the witness search and saturation with
  falsification, by construction.** Both start with the same
  early-exit evaluation loop on the same points; the decider stops
  there, and its shared DAG never evaluates more nodes than the tree.
- **Operations against plain greedy and plain saturation, measured.**
  These use no evaluations, so the margin is not structural. The
  closest is greedy with the generative rule: 6,784 against 7,571
  operations.
- **Time and memory, measured.** Margins on the small suites are a few
  milliseconds and mostly process startup.

What it gives up: its joins are of observed terms at the resolved
points. A join of raw terms that must survive widening the bound still
needs a rewriting derivation, and those engines stay available for that.
Its cost grows with points times DAG size, so a bound with far more
points than the 64 here is unmeasured.

The earlier comparison (no single procedure dominant) was among the
rewriting engines and the plain evaluator; the decider replaces the
plain evaluator and moves the frontier to one point.

Every procedure here only appends joins on witnesses, so the graph
stays sound and grows monotonically whatever the search does, and the
partition does not depend on the order witnesses arrive (`soundiff`,
`joinssound`, `orderfree`, with `Ops.joingrows`).

## Proved (`../proof/Saturation.lean`, on the canonical `Core` and `Ops`)

| Theorem | Statement |
|---|---|
| `soundiff` | A valid graph is sound for a meaning exactly when every join entry is: heuristics, beams, schedules and fuel cannot affect soundness |
| `joinsound`, `joinssound` | Any run of joins on equal-meaning witnesses keeps the graph valid and sound |
| `orderfree` | Same join entries up to membership, same equivalences: arrival order changes what a bounded search finds, never what the graph says given the same witnesses |
| `appliedsound` | Joins of observer-applied terms never leak across observers |
| `boundedexact` | With every agreeing pair joined, `o(a)` and `o(b)` stand together exactly when their keys agree: exhaustive evaluation is complete and sound inside the bound |
| `saturationmax` | Every equivalence a search states from rule instances the saturated graph holds stands in the saturated graph |
| `fuelbound` | Steps costing at least one unit, paid from a budget plus capped refunds, number at most budget plus cap: the dividend cannot make a search run forever |
| `sumperm` | Reordering operands never changes a sum: AC sorting is a sound witness |
| `decidermax`, `decidercovers` | Whatever a sound engine joins, of observed or raw terms, the bounded decider joins at every observer that reads the meaning |

All 17 use only propext and Quot.sound; the thesis gate passes.

## Measured

Corpus: 1,415 obligations harvested from 140 Idol source files in
idol-lib (pin in `results/pins.txt`) by symbolic execution of
straight-line blocks and of loop bodies unrolled 1, 2 and 4 times
(`harvest.py`). 12 agree on the 64 witness points; 1,403 are refuted
by them. The agreeing ones include adler32's four-way unrolled block
against four iterations of its tail loop. Plus targeted suites for
each mechanism (`suites.py`, 38 rows), which are tests written for
the mechanism, not samples of real code.

Same contract for every engine: same rows, same rules (including the
AC and linear macros), same witness points, same fuel ceiling (the
baselines get the witness search's budget plus its dividend cap).

### Real code (1,415 rows)

One shared cost unit for every engine: node evaluations plus rewrite
match steps plus rewrite allocations (the independent audit on fresh
points is not counted).

| Engine | joins | operations | time | peak memory |
|---|---|---|---|---|
| Bounded decider | 12 | 24,585 | 0.037 s | 2.9 MB |
| Plain evaluation (no sharing) | 12 | 42,606 | 0.037 s | 3.0 MB |
| Saturation + witness falsification | 11 | 43,889 | 0.050 s | 3.3 MB |
| Witness-guided search | 11 | 55,995 | 0.077 s | 3.2 MB |
| Plain greedy + backoff | 3 | 2,819,850 | 5.46 s | 3.6 MB |
| Saturation, same budget | 11 | 3,168,215 | 2.91 s | 9.8 MB |
| Saturation to the bound (100k nodes) | 11 | 320,126,465 | 127.8 s | 2.5 GB |

The 12th real join (leb128: `v // 128` against an expression with
`%` and `//`) needs division rules the rule set does not have, so no
rewriting engine finds it; the decider joins it because the two sides
agree on every resolved point.

### Mechanism suites (38 rows)

| Suite | decider | witness | greedy | saturate (budget) | saturate (bound) |
|---|---|---|---|---|---|
| AC sums and products, 6 to 20 operands | 8/8 | 8/8 | 0/8 | 8/8 | 8/8 |
| Factoring join explosion | 8/8 | 5/8 | 5/8 | 6/8 | 8/8 |
| Valleys (must pass a larger term) | 6/6 | 6/6 | 5/6 | 6/6 | 6/6 |
| Meet in the middle | 3/3 | 3/3 | 1/3 | 3/3 | 3/3 |
| Refuted near-misses pruned | 5/5 | 5/5 | 0/5 | 0/5 | 0/5 |

Operations over all 38 rows: decider 41,316, witness 92,475, greedy
90,735, saturation to the bound 200,780.

With the generative rule `a -> (a+1)-1` switched on, plain greedy
proves 13 of 14 on the generative, cycle and valley rows against the
witness search's 10: the search loses valleys when the generative
rule competes for its beam. The decider joins 14 of 14 with 6,784
operations against greedy's 7,571; it uses no rules, so the generative
rule cannot slow it.

### Divergence mechanisms

| Mechanism | Without the fix | With it |
|---|---|---|
| Generative rule | saturation reaches a fixpoint on 0/5 rows, 39,435 nodes (5/5 and 142 nodes without the rule) | witness search stays inside budget plus cap on every row (max 90 nodes) |
| AC blowup | saturation without AC recognition: 6/8, 64,139 nodes | witness search: 8/8, 434 nodes |
| Join explosion | witness search 5/8 at 13,373 match steps | saturation to the bound 8/8 at 76,668: here the search is cheaper and saturation is stronger |
| Cycles | naive provenance (every re-derivation kept): cyclic on 8 of 14 rows, 4,000,064 walk steps, 3,999,958 double credits | first-parent-min-depth: acyclic on 14/14, 135 walk steps, 0 double credits |

In a hash-consed e-graph, wrapping and peeling rules on a cycle such
as `x = f(x)` saturate by themselves; the danger shows up in walks
over terms and derivations, which is what the cycle gate tests.

### Components (each switched off, everything else on)

| Component | Suite | joins on / off | fuel on / off | verdict |
|---|---|---|---|---|
| Hard behavioral falsification | real | 11 / 0 | 3,167 / 3,449,385 | helps (it also steers anti-unification) |
| Anti-unification focus | real | 11 / 11 | 3,167 / 4,890 | helps (fuel) |
| AC multiset recognition | AC | 8 / 4 | 475 / 16,475 | helps |
| Linear-form recognition (added, not in the design) | real | 11 / 10 | 3,167 / 8,679 | helps |
| Bidirectional cones | real | 11 / 3 | 3,167 / 10,493 | helps |
| Bridge quota (80/20 beam) | valleys | 6 / 1 | 5,970 / 20,203 | helps |
| Provenance credit + UCB1 | all suites | 30 / 29 | 21,390 / 25,165 | helps, slightly |
| Merge dividend | all suites | 30 / 30 | 21,390 / 21,204 | no benefit measured |
| Depth fuel | all suites | 30 / 30 | same | no effect measured |
| Entropy tiebreak | all suites | 30 / 31 | 21,390 / 18,237 | hurts |

Provenance: 16-byte `ProvNode` (checked at startup), per-epoch arena,
BASE sentinel, overflow slab for three-premise rules, first parent
wins unless strictly shallower, deepest-first walk with decay 0.85,
bridge bonus 1.5, collision bonus 2, flushed into the rule table at
epoch end. Largest arena seen: 1,976 bytes. Credit reached inner bridge
rules through congruence (171.9 units). Overhead with identical
decisions, median of 5 runs over the real corpus: 32.0 ms with
provenance against 32.3 ms without in the latest run (25.5 against 25.0
in the first), so the overhead is within run-to-run noise.

## Not established

- The suites are written for their mechanisms; only the real corpus
  samples code, and it is one library (idol-lib) in one language.
- Witness rows are property-test points generated per row, not
  recorded executions or release diffs.
- Real joins are straight-line arithmetic only: the harvester skips
  branches, stores, strings and calls with side effects.
- The decider's wins on the small suites are a few milliseconds and
  mostly process startup; each configuration was timed once.
- The estate's existing equivalence witnesses are spelling-level (the
  registry joins byte-identical texts); on these obligations they find
  0 of 12 by construction. idol-lib's redundant campaign has no
  expression-equivalence procedure to run here, so it is not compared.
- The dividend and depth fuel showed no benefit on these suites, and
  the entropy tiebreak made results worse. They stay in the code
  because they were specified, with their measured effect stated.
- Rust and Python mirror the Lean definitions by reading, not proof.

## Reproduce

```
IDOL_LIB=/path/to/idol-lib sh run.sh   # builds wsat (std only), harvests, runs everything, gates
python3 gate.py results                # gates over the committed results
```
