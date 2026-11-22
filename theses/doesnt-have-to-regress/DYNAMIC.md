# Incremental, reversible, greedy release evolution

The static admission contract is necessary but insufficient for a working
release process. This extension implements proof reuse, incremental
recertification, checked contract evolution, reversible state edits, retained
candidate search and an executable command stream. The original definition
audit remains in [AUDIT.md](AUDIT.md); this document states the additional
claims and their limits.

The guarantee is relative to the represented contract and observations. It
does not establish that submitted observations faithfully describe a binary,
its deployment, its environment or all possible executions.

## 1. Incremental recertification and proof construction

`Dynamic/Incremental.lean` decomposes `Audit.replacement` into atomic judgments.
For each protected key these check the old and new required capabilities, the
old and new permitted outcomes, and the two-coordinate cost comparison. Two
additional judgments check the old and new contexts. The aggregate has exactly
`2 + 5 * q.keys.length` judgment occurrences.

Each stored entry contains its exact structural inputs, its Boolean verdict,
and a kernel-checked equality between that verdict and its evaluator. The
`Judgment` proposition gives the leaf's semantic meaning; `Evidence.proof`
provides a proof or a proof of its negation. Both accepted and rejected
judgments can be reused. Reusing a failed capability check cannot turn it into
a success.

These are proof-producing Lean definitions whose reflection, transport and
composition are kernel-checked at the source pin. The compiled executable
erases proof fields and constructs its caches internally; it does not launch
a new Lean kernel process for every JSON event or import arbitrary serialized
proof claims. Its certified computation and a per-event external proof
verification service are different interfaces.

The inputs include the expected and observed contexts, stable protected key,
and the actual relevant lists or cost pair. Reuse requires equality of the
whole stamp. There is no unproved hash-collision assumption, trusted revision
label, trusted dirty-file list or caller-supplied impact cone.

`recertify` derives all current obligations from the current contract and
release pair. For each occurrence it either transports an existing proof
across exact stamp equality or produces a new proof. The aggregate proof is
reconstructed from those leaves. Newly evaluated entries append to the proof
archive; existing proofs are not overwritten. An earlier proof can become
useful again when its exact inputs return.

| Claim | Kernel theorem |
|---|---|
| Atomic judgments express their intended predicates | `Incremental.evaluate_iff` |
| Derived tasks are exactly the full replacement check | `Incremental.tasks_exact` |
| Cached recertification equals full fresh replacement | `Incremental.verdict_eq`, `resultProof` |
| Every lookup transports a proof of the requested judgment | `Incremental.reuse_transport`, `Evidence.correct` |
| The proof archive only grows by suffixes | `Incremental.recertify_prefix` |
| Repeating the same query performs zero new leaf evaluations | `Incremental.recertify_repeat` |
| Evaluations plus reuse equal all current task occurrences | `Incremental.recertify_counts` |
| Archive growth equals the number of new evaluations | `Incremental.recertify_growth` |

The standing one-key controls make the work claim concrete:

| Query | New leaf evaluations | Reused occurrences | Verdict |
|---|---:|---:|---|
| Cold qualifying replacement with identical capability/outcome projections | 4 | 3 | accept |
| Exact repeat | 0 | 7 | accept |
| Change only the candidate cost | 1 | 6 | accept |
| Add an unmet requirement | 1 | 6 | refuse |
| Repeat that failed query | 0 | 7 | refuse |
| Add a protected key with identical local data | 3 | 9 | accept |

These are theorem-checked evaluation counts, not elapsed-time benchmarks.
The implementation still enumerates all obligations, scans the cache and
compares structural inputs. With a list archive of length `H` and `T` task
occurrences, lookup can require `O(T * H)` stamp comparisons, plus the costs of
those comparisons and newly evaluated predicates. The full aggregate scan
remains. This is incremental predicate evaluation and proof reuse, not a
proof of end-to-end `O(delta)` runtime. List reorderings may conservatively
miss reuse despite denoting the same set.

The proof architecture is a finite dependency structure: local judgments feed
the aggregate admission proof. It does not discover arbitrary physical or
program-analysis dependencies. If a program edit invalidates a measurement,
the producer must provide the changed observation or context. A stale but
unchanged input record still describes the old mathematical problem.

## 2. Dynamic contracts without erasing commitments

`Dynamic/Evolution.lean` gives ordinary contract evolution an executable
meaning. `strengthens old next` requires:

1. The comparison context is unchanged.
2. Every previously protected key remains protected.
3. Every prior required capability remains required at its original key.
4. At old keys the new permitted-outcome envelope is contained in the old one.

Keys may be added, requirements may accumulate, and envelopes may narrow.
The check runs on every proposed contract transition. The process cannot
manufacture apparent progress by deleting a difficult key, forgetting a
promise or silently allowing a forbidden outcome.

The concrete command adapter requires complete new-key cells for every
archived artifact before it accepts a scope expansion and automatically
rescans that archive. It refuses absent observations rather than inventing
empty capabilities or zero costs. This is an additional executable readiness
condition: the abstract evolution theorem does not require every archived
candidate to have complete observations. Old artifacts need row coverage,
not satisfaction of newly created promises.

Feature adoption uses a two-phase condition:

```
replacement oldContract oldRelease newRelease
and strengthens oldContract newContract
and certified newContract newRelease
```

It does **not** require `oldRelease` to satisfy promises first introduced by
`newRelease`. The `feature_can_create_its_own_promise` control admits a feature
under the old obligations and records it in the same transition; its companion
proves that the old release fails the future promise.

| Claim | Kernel theorem |
|---|---|
| Strengthening preserves the meaning of old certification | `Evolution.stronger_certified` |
| Admission under a stronger contract implies admission under the older one | `Evolution.stronger_replacement` |
| Checked strengthening and admission compose | `Evolution.strengthens_trans`, `admissible_trans` |
| All earlier contracts remain satisfied along a checked evolving sequence | `Evolution.historical_contracts_preserved` |
| Cached dynamic admission is exactly the two-phase rule | `Engine.adopt_exact`, `adopt_safe` |

A newly protected key establishes its initial cost baseline at admission. No
claim is made about its costs before it was protected. That distinction is a
standing independent control, not an implicit historical guarantee.

A changed physical or measurement context is a separate comparison epoch.
The executable requires explicit observations for the current incumbent and
every archived artifact identity in the new context. It retains the old
observations and proofs, preserves the existing key/requirement/envelope
contract, and starts comparison from the same incumbent artifact identity.
It then recertifies and searches using the new observations.

There is no cross-context dominance theorem without a justified transport
relation. Merely changing a context label is not evidence about the physical
environment. Widening an old outcome envelope or withdrawing a promise is
also not ordinary strengthening. Such a policy change cannot be presented as
preservation of the old contract.

## 3. Greedy search, live arrivals and retained alternatives

`Dynamic/Greedy.lean` uses the strict part of the admission preorder:

```
strictImproves q old candidate =
  replacement q old candidate && !replacement q candidate old
```

All protected capabilities and outcomes must be valid and every protected
cost coordinate must be no worse. Strictness requires a strict gain on at
least one protected key and coordinate. No sum or scalar score can compensate
for worsening another protected coordinate.

The greedy fold inspects a finite supplied catalogue in order and takes a
candidate whenever it strictly improves the incumbent. It returns a certified
replacement and a result that no candidate in that catalogue strictly
dominates. This is a maximal result in the supplied catalogue, not a unique
global optimum. Incomparable candidates can make order matter.

`Dynamic/Engine.lean` runs this same fold using cached recertification in both
directions. `Engine.sweep_exact` proves equality with the fresh reference fold;
the cache cannot change the selected release. The public `Engine.select`
first certifies the baseline and returns `none` when it is invalid, including
when the candidate list is empty. Its safety theorem requires only successful
return, not an unchecked caller assertion of baseline eligibility.

| Claim | Kernel theorem |
|---|---|
| Cached selection equals fresh selection | `Engine.choose_exact`, `sweep_exact` |
| Successful checked selection is non-regressing | `Engine.select_safe` |
| The result is maximal among the supplied candidates | `Greedy.sweep_maximal`, `Engine.select_maximal` |
| A catalogue containing a strict improvement yields strict progress | `Greedy.sweep_progress` |
| Under a fixed contract, a new arrival suffix can be processed incrementally | `Greedy.sweep_append`, `arrive_maximal` |
| Rejected and unselected candidates remain archived | `Greedy.arrive_keeps_archive` |
| A full reconsideration restores maximality under the current contract | `Greedy.reconsider_safe` |
| Repeating a completed fixed-contract scan is selection-idempotent | `Greedy.rescan_idempotent` |
| An arrival sequence remains pairwise non-regressing | `Greedy.timeline_chain` |

The archive is essential. A candidate tied on the old protected scope can
become strictly better when another key becomes protected. Rescanning only
new arrivals after that change misses it. Controls also show revival after a
general policy change; the latter is not confused with permitted cumulative
strengthening.

If a proposed stronger contract is refused, its materialized candidate is
still retained. The adapter rescans the archive under the unchanged contract
so that a useful candidate is not stranded by the rejected policy proposal.
`refused-selected` reports that distinction: the contract was refused, while
an admissible improvement was selected under the existing obligations.

An explicit publication or rollback may be weakly non-regressing without
being a strict optimization. For example, adding an optional capability at
equal represented costs is allowed by `Engine.deploy` but ignored by strict
greedy selection. `Engine.deploy_safe` likewise blocks an invalid baseline
and derives safety from successful return.

### Interacting edits

Greed over individual edits can miss a beneficial combination. The controls
construct two edits that each worsen the baseline alone but improve it
together. That failure is retained.

`Greedy.bundles` supplies a bounded recovery mechanism: for `n` supplied edits,
it enumerates the `2^n` include/exclude combinations in the declared execution
order. `bundle_count` proves the count; `every_bundle_choice_present` proves
coverage of that space; `bundle_greedy_maximal` proves maximality over the
resulting catalogue. The control demonstrates recovery of the two-edit
synergy.

This does not cover arbitrary edit synthesis, unbounded repetition or all
permutations of noncommuting edits. Covering those requires a larger explicit
search space and its cost. The command-stream executable accepts materialized
release candidates; the bundle enumerator is a library API.

## 4. Reversible edits and accountable history

`Dynamic/History.lean` defines patches of `{key, before, after}` edits over a
pure keyed state. Applying a patch checks unique keys and each before-value.
The inverse reverses the edit order and swaps before/after. The kernel proves
the immediate round trip and that unedited keys are unchanged.

Events carry a stable identifier and the complete patch payload. Successful
new events append. An exact repeated identifier/payload is idempotent; a
conflicting payload with the same identifier is refused. Undo appends another
event rather than erasing the original. `undoRecorded` additionally requires
the referenced source event to exist.

| Claim | Kernel theorem |
|---|---|
| Checked patch followed by its inverse restores the pure state | `History.apply_inverse_roundtrip` |
| Unedited keys are unchanged | `History.applied_patch_preserves_unedited_key` |
| Successful submission preserves the history prefix | `History.submission_keeps_history_prefix` |
| Replaying the same event is idempotent | `History.submission_idempotent` |
| Reusing an identifier with a different payload is rejected | `History.conflicting_key_payload_refused` |
| Replaying a consistent journal reproduces the current state | `History.submission_preserves_replay` |
| Recorded undo uses the actual source inverse | `History.undo_recorded_event_uses_exact_inverse` |
| Current-contract rollback must pass current admission | `History.rollback_recertifies_current_contract`, `Engine.deploy_safe` |
| Non-regression in both directions forces equal represented costs | `History.reversible_nonregression_has_equal_represented_costs` |

Before-value checks express value freshness, not causal version freshness.
The retained ABA control performs `0 -> 7 -> 8 -> 7` and shows that the first
inverse `7 -> 0` can apply again. A requirement forbidding intervening writes
needs versioned state or an explicit expected journal head. The current
theorem does not pretend to establish that property.

Structural reversibility also does not imply that every historical release
may be republished. Reversing a strict optimization worsens a protected cost.
Restoring a pre-feature release can violate a subsequently recorded promise.
Both refusals are standing controls. Equal-cost equivalent rollback is
allowed. Irreversible external effects, database migrations, sent messages
and observations of physical systems are not undone by a pure state inverse.

## 5. Executable boundary and recurring checks

`DynamicCli.lean` reads a restricted JSON command stream using the same total
parser as the legacy executable, factored into `GateExe/Parser.lean`. It
validates unique protected and cell keys, nonempty scope, complete protected
key coverage and unambiguous artifact identity bindings. Commands exercise
queries, arrivals, reconsideration, recorded undo, current-contract rollback, cumulative
contract changes and explicit context epochs. Exact command payload replay
is distinct from reusing the same event identifier for a different request.

The CLI adapter and JSON-to-model correspondence are executable code checked
by standing scenario and malformed-input controls; there is not a separate
whole-parser/interpreter semantic-refinement theorem. The admission,
incremental proof reuse, greedy selection, cumulative preservation and pure
journal theorems apply to their actual called Lean functions. Deployment of a
real artifact remains an application premise.

Run:

```sh
lake build
lake exe dynamic examples/dynamic-stream.json
./check.sh
```

The root gate discovers every Lean file, including controls and files not
listed as Lake roots. It compiles with warnings as errors, scans authored
proof escapes, audits every proposition-valued declaration's transitive
axioms, checks the exact dependency pins, runs the old examples and the new
command stream, and rejects source/configuration changes during checking.
Custom proof axioms, admitted proofs and authored escape mechanisms remain
forbidden. Standard foundational axioms and compiler-generated nonlogical
runtime declarations are counted separately.

The pinned GitHub Actions workflow is configured to invoke this same gate on
pushes and pull requests with no reused build cache, and to retain its logs and
source receipt. The composable prerequisite is private, so hosted execution
requires a `FAMILY_READ_TOKEN` secret with read access to that repository;
the workflow explicitly checks out its immutable pin with that credential.
The public prerequisite is fetched by the gate. Runner availability and this
credential are operational prerequisites, not Lean theorems or assumed CI
success. A workflow that never starts its steps is not a passing gate.
Repository-level branch protection and any external deployment system must
actually require the check; a workflow file alone cannot impose that policy.

Independent source challenge and an independent clean exact-pin rebuild are
both required for closure. A build of a working tree, a test against a moving
branch, a parent's receipt or this document's existence is not that evidence.

## 6. Unchanged application premises and open boundaries

The additional proofs remove the need to assume that a cache is fresh, that a
caller supplied a complete changed-file list, that greedy search is already
maximal, or that ordinary contract changes preserve old obligations. The
algorithms check or establish those finite-model facts themselves.

They do not remove the premises of faithful capability and outcome
extraction, operational linkage, physical cost evidence, complete protected
scope, authentic comparable contexts or correspondence between the checked
artifact and deployment. Observation labels are not attestations. Proof
reuse reuses evidence about the model; it does not regenerate a stale
measurement by logic alone.

Timing deadlines, event order, probabilistic guarantees, environmental
quantification and ongoing availability need explicit richer observations
and semantics. The inherited two natural-number minimizing coordinates do
not acquire those meanings automatically. An invalid baseline blocks
publication; a finite search may find no strict improvement; unlimited
archiving consumes storage; exhaustive edit combinations are exponential.
Those are the concrete costs and limits of this process.
