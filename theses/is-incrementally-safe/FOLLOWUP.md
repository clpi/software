# Full-snapshot follow-up on 4a17787

This patch builds on the concurrent RepoSpec/worklist/TaintFree correction, not on the earlier stale checker. No remote edits were made by the repair worker.

## Preserved

* The worklist reachability implementation and its cycle/dense-graph examples.
* RepoSpec as the independent source of dependencies, classifications, allowance, required observations, budgets and cost weights.
* Applicant metadata is ignored, with the existing `check_submitter_invariant` re-proved for the hardened checker.
* The honest name `TaintFree` for label confinement; no relabeling of this property as relational information-flow security.
* The original submitted counterexample file, verbatim under `audit/fixtures/Counterexamples-de1b30716e2b.lean.txt`.

## Canonical admission changes

`RepoSpec.symbols` is now mandatory: it is the authoritative domain of the qualification. Existing repository examples/specs explicitly enumerate their symbols. `check spec base delta` keeps its call signature but scans the entire domain and enforces:

1. Changed keys are unique and in-domain. Every trusted dependency endpoint is in-domain.
2. The finite worklist result contains each direct observation and is closed under every trusted dependency. This checked envelope closes the missing reverse bridge to the inductive `Reaches` relation; no traversal-completeness premise is assumed from a fuel bound.
3. Required observations are retained on every symbol, even when the delta is empty or the required symbol lies outside its cone.
4. Forbidden symbols have no reachable observations, including transitive dependencies.
5. Every reachable observation is allowed and satisfies taint confinement, including unchanged baseline symbols.
6. The existing modeled cost is within RepoSpec bounds.

An unsafe baseline, missing baseline obligation, duplicate update, unknown update, malformed graph, or transitive forbidden observation now refuses. Lawful cycles and retained required observations still accept. The old implementation remains named `checkConeOnly`, documented as an incomplete diagnostic, not a release-admission API; all its characterization theorem names have `coneOnly_` prefixes. Canonical `check_accept_iff`, `accepted_envelope`, `accepted_reachability`, `accepted_required`, and `accepted_forbidden_no_reaches` describe the stronger checker.

## Temporal and relational opt-in

`RunAdmission.check` independently checks input-indexed finite run sets against ordered trace predicates and equality of low-observation sets for policy-selected pairs of inputs. Tests reject a door-opening ordering violation, reject a secret leak, accept nondeterministic noise, and reject deletion of a required response trace. This is an explicit opt-in interface, not an implicit extension of the observation-list checker.

Its `accepted_ordered_traces` and `accepted_relational` theorems connect executable acceptance to those finite model obligations. `transfer_relational` exposes a correspondence hypothesis for actual execution semantics. It does not manufacture correspondence from content hashes or sampled runs.

## Exact limits

* Domain completeness, dependency/behavior extraction, policy authentication, and correspondence of observations to the release are external integration obligations. An applicant must not choose the authoritative RepoSpec or run Policy. An empty authorized domain makes its universal checks vacuous; this is not a claim about an entire executable.
* Required observation/trace membership preserves modeled possibilities, not inevitable eventual response, fairness, or universal liveness.
* Run noninterference is possibilistic. Duplicate trace multiplicity, probabilities and timing distributions are not represented unless the observation model explicitly includes them. Empty/erasing low views are policy choices, not discovered security guarantees.
* Cost is the weighted count of submitted observations under `obsCost`. The two bound fields are retained for compatibility. Their names do not make the cost actual runtime or compute use. Satisfying both bounds does not prove Pareto optimality.
* NodeKind remains metadata: all represented node kinds receive the same checks. This does not prove complete extraction from a repository's code/configuration/context/data.
* This is a correctness-first full-domain reference checker. Its runtime is not an incremental-speed claim. A faster incremental implementation needs a snapshot-bound valid-baseline receipt and a checked completeness theorem for affected scope.

## Audit and reproducibility

`Counterexamples` is now a default Lake target instead of silently omitted. The active audit uses the new RepoSpec interface and expects C1-C3 refusals; C4-C6 remain checked demonstrations of the limits of profile-only semantics. The original pinned text is not rewritten.

Lean 4.19.0:

```
set -euo pipefail
./verify-followup.sh
```

The script builds the default targets and Counterexamples explicitly, checks modified/new proof modules with warnings as errors, and rejects proof escape hatches. `FOLLOWUP-BUILD.log` records the run; `FOLLOWUP-SHA256.txt` records the reviewed Lean/config hashes. The new bridge proofs use only Lean's standard foundational axioms (printed in the audit), no custom axioms or sorry.

## Additional scope controls from independent review

* Empty authorized symbol domains accept vacuously, even if an unlisted symbol's baseline is unsafe. Scope completeness must be authenticated by the caller; domain enumeration is not source extraction.
* Bounds apply to changed observations, not total baseline cost. An unchanged costly baseline can accept at zero change budget. No total-resource or improvement claim follows.
* Required lists have set-membership semantics, not multiplicity semantics. Repeating one required entry does not demand two distinct occurrences or receipts.
* RunAdmission is an opt-in check, not automatically conjuncted with the profile checker. A caller requiring temporal or information-flow guarantees must invoke it against a corresponding authenticated run model, or construct an explicit combined gate.
* Its noninterference condition ignores occurrence frequencies. Distinct distributions with identical supports may pass.

The test script now injects and verifies rejection of four proof-escape scanner controls, three compiler controls (sorry, admit, type error), and the obsolete unsafe-baseline admission claim. It is not merely a regex policy asserted without execution.
