# software

Machine-checked claims about software, in Lean 4.19.0: when testing, review, benchmarking and
fuzzing are redundant, when releases compose without regressing, when compute and search can be
made incremental, and when a Pareto frontier of programs can be solved exactly. Each claim comes
with its premises stated, executable reference checks, and receipts you can rerun.

This repo merges 32 earlier `clpi/software-*` repos into one. Each lives under `theses/<name>/`
with its full git history. Definitions that several repos wrote separately (derivation, closure,
no-worse, domination) now have one canonical form in `shared/core`, and each repo's own version
is proved equivalent to it (`CONCEPTS.md`).

## Read the claims carefully

The theorems check, with no `sorry`, no custom axioms and no `native_decide`; every axiom used is
within `propext`, `Classical.choice` and `Quot.sound`. What a theorem means is what its statement
and premises say. Most results are conditional: "redundant" means redundant given a stated closure
and stated valid evidence, "optimal" means nondominated within a stated finite candidate set under
a stated cost model. Each thesis README lists which claims are proven, which rest on a premise and
which were disproved.

## Check it yourself

You need Lean `v4.19.0` (`lean` and `lake` on `PATH`) and Python 3.

```sh
./run-gates.sh                      # every gate: copies check, shared core and bridges, every thesis
./run-gates.sh optimality           # one thesis
bash shared/core/check.sh           # canonical definitions plus all equivalence bridges
python3 consolidation/check-copies.py .
```

At the merge, 90 thesis gates gave the same exit code here as in the original repos (81 pass;
9 need inputs the caller supplies or files that were never committed, and fail the same way in
the originals). Results: `consolidation/gates-results-reconciled.tsv`.

## Layout

| Path | What is there |
|---|---|
| `theses/<name>/` | one former repo, unchanged except that byte-identical copies became links into `shared/` |
| `shared/core/` | Lake package `software-core`: canonical `Derives`, `Closed`, `NoWorse`, `Dominates`, and bridges proving each thesis's own version equivalent |
| `shared/gates/`, `shared/incremental/` | the one copy of each gate script and of the incremental engine used by several theses |
| `CONCEPTS.md` | every concept, its canonical form, each variant and its bridge, or why it is a different concept |
| `CONSOLIDATION.md` | how the repos overlapped, what was merged, what was tried and reverted |
| `consolidation/` | the merge tooling, commit maps from old to new hashes, inventory of every file, theorem, gate and receipt |

Branches and pull-request heads of the old repos are kept as `archive/<name>/...`; old tags as
`<name>/<tag>`. The pre-reconcile snapshot is tagged `import`, and
`consolidation/verify.py SRC REPO MAPS --ref import` proves every old commit, ref, file and
theorem is here, by git object hash.

## Theses

| Thesis | Theorems | About |
|---|---:|---|
| `optimality` | 846 | qualification closure, compounding and finite Pareto selection; the shared foundation |
| `doesnt-have-to-regress` | 435 | non-regression gates for releases, with audits of the interfaces they rely on |
| `redundant-compute-expands` | 422 | redundant compute under expansion-only growth of a behavioral hypergraph; admission, worklists, synthesis |
| `is-quantifiable` | 363 | quantified qualification: measures, coverage, intervals and Pareto points |
| `is-more-traceable-than-you-think` | 307 | an append-only dependency hypergraph across recomputation, compilation, certification and execution |
| `is-incrementally-safe` | 287 | incremental admission that stays safe; saturation order independence |
| `frontier-is-solvable` | 263 | exact insertion and retraction for a finite Pareto frontier over a canonical hypergraph |
| `redundancy-is-equivalence` | 217 | redundant computation as equivalence of behavior |
| `is-incrementally-certifiable` | 187 | conditional sequence guarantees for incremental certification, with counterexamples |
| `is-composable` | 149 | release admission and composition along dependencies |
| `doesnt-need-review` | 126 | when review is implied by independent baseline evidence |
| `is-reversible` | 94 | the reversible search space for theorem completion over derivations |
| `emergence-is-decidable` | 77 | emergence from actor interactions as a decidable quantity |
| `pareto-is-provable` | 77 | Pareto optimality obligations proved for the general definitions |
| `is-bidirectional` | 73 | contracts checked in both directions |
| `has-a-highest-minimal-axis` | 67 | a qualified parametric system with a highest minimal axis |
| `is-solvable` | 53 | witness-compounding search and resolution |
| `persistence-is-minimal` | 53 | minimal persistence under redundant computation and Pareto selection |
| `compilers-lose-info` | 41 | compilers as maps that forget derivation structure |
| `is-a-parametric-language-model` | 40 | a deterministic, parametric language model |
| `benchmarking-is-redundant-and-suboptimal` | 37 | conditional redundancy and dominance of benchmarks |
| `testing-is-redundant` | 34 | a hand-written test is redundant exactly when its scoped obligation is already closed |
| `fuzzing-is-suboptimal` | 28 | conditional suboptimality of evidence-generation plans |
| `profiling-is-synthesizable` | 20 | profiling synthesized incrementally |
| `certification-is-monotone` | 19 | monotone certification across releases |
| `qualification-is-two-sided` | 19 | every qualified configuration has a dual unqualified witness |
| `losses-are-compositional` | 18 | structural loss fixing composes |
| `is-a-closed-loop` | 17 | continuous synthesis of the whole proof estate |
| `checking-is-choral` | 14 | checking split across independent checkers |
| `tensors-are-editable` | 14 | transition semantics for editable tensors |
| `estate-is-censused` | 5 | estate-wide accounting of provable results |
| `proofs-are-portable` | 4 | a release artifact carrying its own certificate |

Theorem counts are `theorem` and `lemma` declarations at the merge (`consolidation/manifest.tsv`).

No license file was present in any of the original repos, and none is added here.
