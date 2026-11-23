# Definition audit: software does not have to regress

## Verdict and audited revisions

At the requested revision, `24d36c13414867e59ae67ccf47f83cc250ce55af`, the repository has exactly one file, a README. It has no formal statement, theorem, toolchain, or check gate. At that pin the name is an unsupported thesis, and the empty proof estate is a defect.

The live head inspected for this work was `858a85e383fbecc9826186aee2cc0101aea5ea62`. It is no longer empty: it contains a finite release gate and proofs of its policy. This audit preserves that development, adds standing counterexamples, and states a separate, stronger contract. It does not retroactively credit the historical pin.

**The name survives only as a conditional release-policy claim:** under a specified, faithfully represented qualification and comparison contract, publication can be restricted to a certified incumbent or a candidate that retains required capabilities, permits only approved outcomes, and worsens no protected cost. An invalid incumbent must block this policy. Strict progress, perpetual availability, and a physically universal optimum do not follow.

The entire current `acceptsRelease` predicate must not be called “superset-of-qualified.” The imported quantifiable pin already checks context equality and componentwise cost as well as qualification retention. The historical subset model and the current retention model are different generations. [Audit/SOURCES.md](Audit/SOURCES.md) gives their exact pins and source locations.

## 1. Establish what each set means

The original direction dispute hides two different quantifiers:

- A **required capability** is something the implementation must provide, with the intended input and outcome guarantees.
- A **possible outcome** is something an implementation may do and therefore must be permitted.

“Nothing required disappears” is a lower inclusion. “Nothing forbidden appears” is an upper inclusion. Neither determines the other. A list containing a successful response is not evidence that every response is successful.

For a simplified single behavior universe, write required set Q, permitted envelope A, and candidate behavior set B. The admissible sandwich is Q ⊆ B ⊆ A. The old implementation's behavior set is not automatically either Q or A.

The checked contract separates capability and outcome types instead of pretending that a may-outcome is a guaranteed capability. For each protected key k, it has:

- Q(k): the previously qualified positive obligations, using upstream `PriorQualification`;
- P(r,k): the candidate's offered capabilities, using upstream `BehaviorSubmission`;
- A(k): the independently approved possible-outcome envelope;
- T(r,k): the candidate's declared possible outcomes;
- c(r,k): the upstream `Point` of two minimizing natural-number cost coordinates.

Keys preserve the chosen API, input/workload, and environment identity. The context value binds the comparison contract. Its equality is a declared-scope check, not a proof of physical comparability.

## 2. Candidate readings and minimal misjudgments

All numeric coordinates below are minimized. Zeros are abstract model values. “Improvement” or “regression” names a stated obligation or protected coordinate, not a subjective preference. Minimality is with respect to the indicated universe, qualification, and catalogue assumptions.

### R1. Behavioral refinement: B(new) ⊆ B(old)

**Smallest false acceptance:** one required behavior r.

- Q = {r}; B(old) = {r}; B(new) = ∅.
- Subset accepts.
- The only required capability disappears.

No nonempty behavior universe smaller than one can exhibit a lost capability. `subset_deletes_only_requirement` checks the two directions using the actual retention predicate with reversed arguments.

**Smallest false rejection:** B(old) = ∅; B(new) = {f}, where f is an approved feature. Subset refuses the addition. This needs one behavior. The nonempty-baseline variant {r} → {r,f} needs two. Both are retained controls.

**Survival argument:** subset is useful for preserving a genuinely downward-closed property of a complete possible-outcome set, given that the old set satisfies that property. It does not establish positive capability, termination, availability, relational security, or cost preservation. The empty implementation exposes why that restricted result is insufficient.

### R2. Required-behavior retention: Q ⊆ B(new)

**Smallest false acceptance with nonempty qualification:**

- Q = A = B(old) = {ok}.
- B(new) = {ok,bad}, where bad is forbidden.
- Retention accepts: ok remains.
- Safety regresses: bad becomes possible.

Two behaviors are necessary when one must remain qualified and a distinct forbidden one must appear. If empty qualification is permitted, the absolute minimum is ∅ → {bad} with Q = A = ∅.

The stronger actual upstream `acceptsRelease` also accepts the nonempty example when context and costs are equal: its inputs have no independent allowed-outcome envelope. More sharply, the target's existing strict `accepts` calls the new bad behavior a strict gain. These are concrete controls, not criticisms inferred from names.

**Dead-behavior correction:** removing genuinely unreachable and unobservable implementation code leaves an extensional observable behavior set unchanged. Qualified retention cannot reject that deletion on behavior grounds. A recorded d ∈ Q that disappears is either a protected obligation being removed, an obsolete qualification requiring explicit migration, or an implementation artifact incorrectly treated as observable semantics. Calling d “dead” does not discharge its qualification.

With Q = {r}, removing an unqualified d from {r,d} → {r} passes qualified retention. Treating every old observation as required unnecessarily refuses it. If Q = {r,d}, refusal is correct under that frozen contract.

**Survival argument:** fixed qualification containment is exactly the positive-obligation half, conditional on truthful capability declarations and sound qualification. It is not a safety envelope or a physical capability proof.

### R3. Candidate is Pareto-nondominated

**Smallest trade-off with the incumbent included in the catalogue:**

- old = (0,1); new = (1,0).
- Catalogue = {old,new}.
- Both are nondominated.
- Replacing old with new worsens the first protected coordinate.

Two distinct points and two varying coordinates are necessary here. On one minimizing coordinate, “old does not strictly dominate new” is equivalent to new ≤ old; `one_axis_nondomination_is_no_worse` establishes that boundary. Without the incumbent in the comparison catalogue, even the singleton frontier {1} can replace an old cost 0.

Adjacent nondominance is also not transitive: (0,1) → (1,0) → (0,2) passes the adjacent nondominance test, but the first point dominates the last. A trade-off can be traversed back and forth without any strict monotone progress.

**Survival argument:** frontier membership correctly describes the available trade-offs inside the declared eligible catalogue. It does not justify replacing a particular deployed incumbent. Catalogue completeness and eligibility remain separate obligations.

### R4. Every release is independently admitted under the same safe profile and cost budget

This is directly supported by the historical vocabulary:

`admits safe bound a := c safe a.profile ∧ paretoLE a.cost bound`.

**Smallest false acceptance:** keep behavior and safety identical; use one varying cost.

- Budget = 1.
- old cost = 0; new cost = 1.
- Both are admitted.
- The new release is strictly worse than the actual incumbent.

The other cost coordinate can be fixed at zero. An unchanged ceiling does not compare successive releases. The downward-closure component cannot supply the missing cost comparison.

**Survival argument:** this reading establishes admissibility within a fixed permitted region. It becomes a nonregression gate only after adding a comparison with the actual incumbent and the required positive obligations. It is not a release-order theorem by itself.

### R5. Pairwise componentwise cost nonregression

**Smallest false acceptance:** one required capability and one varying cost.

- old provides r at cost 1.
- new provides nothing at cost 0.
- Every cost coordinate improves or stays equal.
- Required functionality is lost.

This reading correctly supplies the cost half. It survives in conjunction with semantic admission and a common comparison scope; it does not replace them.

A scalar weighted score is still weaker than componentwise protection. Any compensated loss on a protected coordinate remains a regression under a no-trade-off contract, however attractive the sum.

### R6. New frontier covers the old frontier

Use the stronger set-level statement:

For every old option x, there exists one new option y that is no worse than x on every protected coordinate.

**Minimal frontier/deployment distinction:**

- Old frontier = {(0,1)}.
- New frontier = {(0,1),(1,0)}.
- The retained old point witnesses coverage.
- Deployment selects (1,0), which regresses on the first coordinate.

Coverage preserves an available choice. A dispatcher or deployment decision must select that protected choice under the actual workload, and its own overhead belongs in the comparison.

The witness must be the same candidate for all coordinates. Old (1,1) and candidates (0,2),(2,0) show why “for each axis, there exists a good candidate” cannot replace “there exists one candidate good on every axis.”

**Survival argument:** frontier coverage is a valid archive or choice-set guarantee. It is not a deployed-release guarantee unless joined to a checked selection policy. The distinction also rules out claiming success merely because a former binary remains somewhere in storage.

### R7. Equality of the recorded observations

Equality is a valid preservation rule for everything actually represented by the observation map. It does not repair an incomplete observation map.

Two ordered executions [stop,open] and [open,stop] have the same event-membership set. They differ on the order obligation. Two executions with the same returned value can differ on a deadline or on an environment-sensitive obligation.

`erased_property_has_no_exact_checker` proves the general limit: if two executions have the same projection but opposite truth values for a property, no Boolean checker of that projection can characterize that property exactly. This is an impossibility of exact classification after information erasure. A sound incomplete checker may still refuse or abstain.

Equality also freezes all observed feature additions and deletions. It is useful for observationally equivalent optimization; it cannot be the only accepted form of feature evolution.

## 3. Why simply conjoining the old directions fails

If Q = B(old), then

Q ⊆ B(new) ⊆ B(old)

forces B(new) = B(old) extensionally. `frozen_sandwich_is_membership_equality` proves this. This can be an intentional compatibility contract, but it prohibits all new observed behavior and protects every old observed defect as if it were required.

The repair is to distinguish the required floor Q from the approved envelope A. In particular, A may permit a feature before it is implemented, and Q need not contain optional implementation details. An envelope expansion requires a contract decision; it cannot be chosen silently by the candidate.

## 4. The surviving contract

Within a fixed contract C and its selected keys, a replacement old → new must satisfy:

1. The incumbent and candidate are both certified in C.
2. For every protected k, Q(k) ⊆ P(new,k).
3. For every protected k, T(new,k) ⊆ A(k).
4. For every protected k, c(new,k) ≤ c(old,k) componentwise.
5. Capability identities, key identities, context, cost-coordinate meanings, and evidence interpretation retain their declared meaning.

Items 1–4 are the finite checked relation in `Audit/Contract.lean`. Item 5 is partly represented by keys and context equality and partly a model-to-implementation obligation. There is no hidden theorem that authenticates these declarations.

The formal cost adapter uses the family's existing two-coordinate `Point` at each key. It proves the result for any finite list of protected keys and the represented coordinates. A claim about a wider physical metric space requires a coverage-preserving adapter and evidence; the theorem does not silently quantify over omitted metrics.

The new policy is an executable finite library definition. The legacy `gate` stream executable still uses the original profile policy; it has not acquired an outcome-envelope input or an implementation evidence extractor. No production deployment integration is claimed.

The construction reuses upstream `PriorQualification`, `BehaviorSubmission`, `noQualifiedBehaviorLost`, `noWorse`, and `acceptsRelease` at the pinned dependency. `replacement_uses_family_admission` proves the bridge. It adds an explicit permitted-outcome check instead of inventing another competing positive-qualification definition.

### Proved policy consequences

- `replacement_iff`: the finite checker exactly matches its stated conjunction.
- `replacement_preserves_requirements_and_envelope`: accepted replacement retains the qualified capabilities, stays inside the allowed outcome envelope, and does not worsen the represented costs.
- `replacement_trans`: the relation is transitive under one fixed contract.
- `shipped_chain`: a stream started from a certified baseline and using the guarded policy is nonregressing between every earlier and later shipped release under that contract.
- `no_strict_reverse_dominance`: an earlier represented cost point cannot strictly dominate an accepted later one.
- `deployed_safe`: whenever the public `deploy` wrapper returns an artifact, that artifact satisfies the replacement relation. Baseline validity is checked by the wrapper, not assumed from its caller.
- `invalid_baseline_blocks_deployment`: if the incumbent is no longer certified, the policy returns no deployment.
- `recordPromises_certified_iff`: adding promises to qualification requires the existing contract plus evidence that those promises are offered.
- `recorded_promises_preserved`: both previously qualified and newly recorded obligations must remain offered.

The internal `ship` helper can retain an invalid baseline if misused; its theorem requires certification. The public deployment wrapper closes that publication gap. A standing control records both sides of this boundary.

### New promises must accumulate

With fixed Q = {r}, {r} → {r,f} → {r} passes required retention. Once f is promised, the release process must record it.

The protocol is: admit the feature under the existing contract; certify the resulting release against Q plus the newly approved promises; use that expanded qualification for subsequent replacements. Expanding Q before feature admission wrongly demands that the old incumbent already have the new feature.

The fixed-contract sequence theorem does not by itself prove an arbitrary changing-contract sequence. The append operation and its preservation theorem establish the qualification update step. Arbitrary deletion of obligations, changed contexts, changed envelopes, or new metrics require a separately justified contract migration.

### What “doesn't have to” costs

Keeping a certified incumbent proves weak feasibility only while retaining it remains legal, executable, deployable, and eligible in the current context. If those facts cease to hold, this policy may block.

The construction does not prove that a distinct safe improvement exists. A finite catalogue containing only the incumbent is the smallest countermodel to mandatory strict progress. Nor does it prove that a checker can decide every real program property or that it can keep operating under every changing external requirement.

There is a conditional progress result already in the older finite gate: `ascend_ships_of_exists` ships an improvement if an acceptable one exists in its supplied catalogue. Its relation is the older one; it is not automatically a theorem about the new outcome-envelope contract.

## 5. Per-release enforcement cost

| Check | What the process must actually establish |
|---|---|
| Contract continuity | Pin qualification, approved outcomes, keys, identities, units, metric directions, workload, environment, measurement interpretation and deployed baseline. Reject missing or misaligned records. Recheck the incumbent when these conditions change. |
| Positive obligations | Discharge each required capability against the candidate under its declared scope. A successful observation, or a capability ID in a list, is not universal evidence. Keep newly promised obligations in cumulative qualification. |
| Negative obligations | Establish that every relevant possible outcome is permitted. A finite sample cannot establish this for an unbounded execution space without an abstraction or coverage argument. |
| Costs | Compare every protected coordinate with the deployed incumbent in the same scope. Passing an old budget, improving a sum, or being nondominated is insufficient. Include dispatcher, migration, monitoring and verification overhead when they are inside the claimed scope. |
| Timing interpretation | Say whether a coordinate means a deterministic value, a specified statistic, an upper bound, or every possible realization. Decreasing interval endpoints is not universal run-by-run dominance. |
| Composition and reuse | Check integrated behavior and costs, or supply a sound composition and dependency argument. Rechecking only a cone is justified only when the cone includes every semantic dependency, including configuration, data and environment. |
| Publication | Bind the evidence to the exact built artifact and configuration selected for deployment. Retaining a good alternative in an archive is insufficient. |
| Refusal | Keep a still-certified incumbent or return a blocked decision. Refusal and downtime themselves need a modeled obligation if perpetual availability is promised. |

For the concrete list-based checker, let q(k), p(k), t(k), a(k) be the lengths of qualification, offered capabilities, possible outcomes and permitted outcomes. Its membership work is O(sum over k of q(k)p(k) + t(k)a(k)), plus linear traversal and two coordinate comparisons per key; certification of the baseline adds its corresponding checks. Equality itself is not assumed constant-cost for arbitrary types. Indexed finite sets can reduce membership work, but evidence production is not accounted for by these lookup counts.

There is no universal low cost for producing sound, complete behavior or cost evidence for arbitrary software. The finite gate is decidable because it compares supplied finite data. A complete Boolean gate for an arbitrary relation would decide that relation; the existing `complete_gate_decides` makes this boundary explicit.

An exact finite frontier over N candidates and d represented coordinates can use O(N²d) pairwise comparisons. Frontier selection is optional for no-regression admission: comparing one candidate with the incumbent requires only its semantic obligations and coordinate guard. Proving a catalogue Pareto-optimal is not proving global physical optimality.

### Interval claims must be named precisely

The original gate compares both endpoints, so [10,20] → [8,18] passes while an old run at 10 and a new run at 18 regress. Its own `accepted_not_per_execution` already proves that failure.

For independently varying realizations within bounds, the upstream sufficient condition is candidate upper ≤ incumbent lower on every protected coordinate. That condition is deliberately stronger and may refuse real improvements when intervals overlap. Coupled-run or statistical claims need their own evidence and semantics.

Narrowing uncertainty is also a different order: [0,2] → [1,1] improves the upper bound and the information interval but fails the original both-endpoints-decrease gate. The audit keeps that control so “information improvement,” “bound improvement,” and “execution improvement” cannot be substituted for one another.

## 6. What is outside the proved observation and interpretation

The accurate statement is projection-relative. Lean can represent more than these files represent, and current siblings have already repaired some historical omissions.

| Concern | Historical projection limit | Current family status / remaining obligation |
|---|---|---|
| Ordering, repetition and causality | Membership-only traces identify [stop,open] and [open,stop]; sets also erase multiplicity. | Current safe `OrderedIncrement` models input-indexed ordered traces and prefix safety. This target's legacy profile gate does not import that semantics. The new generic Outcome type permits an adapter, but no implementation-to-trace completeness theorem is supplied here. |
| Timing and deadlines | Untimed outcomes cannot distinguish timely from late executions. A scalar cost represents only its specified quantity. | Cost points and interval separation exist. Deadline semantics, joint timing, queueing, jitter and tail distributions require their own representation and faithful evidence. |
| Environment dependence | Unindexed observations cannot distinguish changed hardware, load, configuration, data, deployment or external services. | Context keys, comparison contracts and context dependency nodes exist. Key equality and a graph edge do not authenticate physical scope or prove dependency completeness. |
| Progress and availability | Possible successful outcomes do not guarantee termination, fairness, eventual response or continued service. | Blocking or retaining an incumbent is not a liveness theorem. Infinite executions and progress assumptions need an explicit model. |
| Probabilities and risk | Ordinary behavior sets erase frequencies and correlations. Equal support can hide much worse failure probability. | Statistical estimates need declared sampling, uncertainty, distribution or adversary assumptions; deterministic point comparisons do not provide them. |
| Relational security | A single-execution allow-list does not encode all relationships across executions. | Current safe work models noninterference and disproves generic preservation under trace deletion. That result cannot be inferred from historical subset refinement. |
| Whole-system interaction | Per-symbol observations can omit contention, cache effects, shared state, scheduling and nonlinear resource interactions. | Supply a justified composition law or protect whole-system observations as additional keys. Summing local costs is not automatically faithful. |
| Physical and deployment fidelity | A declaration can claim a capability with no corresponding execution, omit a bad outcome, assign false costs or describe a different binary. | These remain explicit application premises. No equality, subset, closure, or Pareto relation over false data repairs them. |

**Does the name promise these?** Unqualified, it naturally invites a whole-software reading that includes user-visible ordering, latency, environment and availability regressions. The formal result does not earn that reading. The README must carry the scope qualification as part of the claim itself.

## 7. Proof strength and application-premise ledger

| Claim | Status at the new source | Evidence / condition |
|---|---|---|
| Historical name has a proof at 24d36c134148 | REFUTED | Exact tree is README only. |
| Subset, retention, frontier membership, fixed-budget admission, or cost comparison alone imply full nonregression | REFUTED | Named controls in `Audit/Readings.lean`; each has a minimal stated universe. |
| Old subset plus retaining all old behavior permits arbitrary feature evolution | REFUTED | Frozen sandwich equals observational equality. |
| Checked scoped replacement preserves its modeled obligations and costs | PROVEN IN MODEL | `Audit/Contract.lean`, with upstream qualification and cost definitions at immutable pins. |
| Every successful `deploy` returns a certified nonregressing artifact | PROVEN IN MODEL | `deployed_safe`; invalid baseline blocks. |
| Fixed-contract guarded release streams do not regress against earlier releases | PROVEN IN MODEL | `shipped_chain`, with a certified initial state. |
| New promises automatically become protected | REFUTED | Fixed-Q loss control; append-and-certify protocol is required. |
| Every improvement exists or must be discovered | NOT CLAIMED | Strict progress needs a witness/catalogue/search argument. Stasis can be the only safe choice. |
| The abstract model faithfully describes all promised software behavior and costs | PREMISE | Capability fidelity, outcome completeness, execution linkage, scope coverage, context and cost authenticity, composition, governance and deployment correspondence. |
| The current target proves arbitrary timing/order/environment/liveness guarantees | NOT CLAIMED | Requires the corresponding richer model and implementation bridge. |
| Exact classification can recover an erased property | REFUTED | `Audit/Projection.lean`; conservative abstention remains possible. |

`replacement_iff` and the field projections are checker exactness/decomposition results, not independent proofs that real software cannot regress. The sequence theorem supplies actual compositional content: local checked transitions imply all-pairs modeled nonregression. None of the application premises is disguised as a field that already asserts the desired physical conclusion.

## 8. Standing controls and gate

The in-tree controls include minimal reading failures, independent conjunct-removal attacks, optional feature changes, accumulated qualification, identity relocation, empty scope, unlinked capability declarations, invalid-baseline refusal, and information-erasure limits. The independent review is recorded in [Audit/REVIEW.md](Audit/REVIEW.md).

The strengthened `./check.sh` inventories every repository Lean file, compiles each with warnings as errors, checks immutable dependency pins, audits transitive proof axioms, scans prohibited source escapes, and runs rejection controls. It also retains the existing executable stream and worked-example checks. The JSON reader is a restricted stream reader, not a proof of arbitrary JSON schema correctness.

Lean's three standard foundational axioms are reported separately from custom proof axioms. Compiler-generated nonlogical runtime specializations are not silently described as zero authored escapes; they are separately enumerated. The gate's own negative controls include the quote-character scanner bypass found during independent review.

The closure claim is limited to the exact publication pin that has passed both the publisher's gate and an independent clean recheck. A successful historical log, or a run whose sources changed during checking, is not such a receipt.
