# Incremental certification across releases: a proof and falsification duet

## Voice One — the claim, the sources, and the first obligation

**The unrestricted description is false under the audited admission rule.**
Individual admission does not imply improvement across releases. The repaired
claim is conditional temporal nonregression, with exact conditions for strict
improvement and a separate positive behavior obligation. Those conditions are
proved sufficient and, where stated below, necessary.

The historical repository pin is
[`f3b9f896ac76a95e7104c98af66e41413e7e5b2d`](https://github.com/clpi/software-is-incrementally-certifiable/tree/f3b9f896ac76a95e7104c98af66e41413e7e5b2d).
It contains only `README.md`, whose claim is that incremental monotonic
certification is extensive and yields Pareto-optimal dominance across releases.
There is no theorem at that pin. The present work does not retroactively attach
a theorem to it.

The copied model is recovered from
[`software-is-incrementally-safe@de1b30716e2b758141d5940056f37cd678464032`](https://github.com/clpi/software-is-incrementally-safe/tree/de1b30716e2b758141d5940056f37cd678464032).
That copy explicitly names the audited certifiable pin in `siblingPin`.
`Legacy/README.md` records its exact file blobs and the namespace-only
transformation used to compile it beside the current family interface.

The integration base is the later certifiable
[`master@3690167318cf4d41b51d0945f4fccc7f043e8412`](https://github.com/clpi/software-is-incrementally-certifiable/tree/3690167318cf4d41b51d0945f4fccc7f043e8412).
It already contains `pareto_monotone_chain` for exactly three cost points,
with an explicit catalogue and coverage premises for its optimality conclusion.
The new arbitrary-sequence results retain that work and remove those unrelated
premises from temporal nonregression.

### Definitions used without changing their meaning

| Definition | Exact source |
|---|---|
| Historical `Profile`, `profileLE`, profile order laws | Safe repository at `de1b30716e2b758141d5940056f37cd678464032`, `SoftwareIsComposable.lean`, blob `251c0824e8bc48a82bc69a640cbd54d7aff86f63` |
| Historical `c`, `Cost`, `paretoLE`, `paretoDominates`, `Admission`, `admits`, `admitted_downward` | Same safe pin, `SoftwareIsIncrementallyCertifiable.lean`, blob `28f33d5fefa1a54e426a5ef45030be2f64794dee` |
| Current `MeasureSpace`, `Profile`, `noWorse`, `dominates`, `releaseLe`, `releaseDominates`, `frontier` | `software-is-quantifiable@430340295c52a015772022b2b663d01120a3a747`, `SoftwareIsQuantifiable/Interface.lean` |
| Current two-cost `costSpace` and `profileOf` | Same quantifiable pin, `SoftwareIsQuantifiable/Pareto.lean` |
| Current derivation closure, old three-point catalogue/frontier vocabulary and bridges | `software-optimality@b52c3170a6e108345bd5ada44ca7355dae55b395`; unchanged dependency of the integration base |
| Current composable dependency | `software-is-composable@476059c25b93679919238ae4293c6b0b4befe486` |

Historical `c` is downward closure of observation sets. Current `certClose` is
`Qualification.Derives`, a rule-derivation closure. This work does not identify
them. `LegacyBridge.weak_iff_canonical` and `strict_iff_canonical` prove the
historical cost comparisons agree with the current canonical two-cost interface;
there is no unproved identification of their different behavior models.

Write a historical release as `a_n = (p_n, k_n)`, with
`k_n = (time_n, compute_n)`. Smaller is better in both cost coordinates. The
actual definitions are:

\[
p\le_{\mathrm{profile}}q \iff \forall o,\ p(o)\Rightarrow q(o),
\]
\[
c(S)(p)\iff\exists q,\ S(q)\land p\le_{\mathrm{profile}}q,
\]
\[
x\le_P y\iff x_t\le y_t\land x_c\le y_c,
\]
\[
x<_P y\iff x\le_P y\land(x_t<y_t\lor x_c<y_c),
\]
\[
\operatorname{Admits}(S,B,a_n)
\iff c(S)(p_n)\land k_n\le_P B.
\]

The minimum temporal interpretation of the description is the proposed theorem:

\[
\left(\forall n,\operatorname{Admits}(S,B,a_n)\right)
\Longrightarrow\left(\forall i\le j,\ k_j\le_P k_i\right).\tag{Rejected T0}
\]

Strict improvement for every `i < j`, and global Pareto optimality over every
feasible implementation, would be stronger claims. Neither follows merely from
the closure laws or downward closure of admission.

## Voice Two — attack 1: admitted regression

Choose one unchanged, nonempty behavior profile `p`, safe predicate `S(q) := q=p`,
and a fixed budget `B=(2,2)`. Let:

| Release | Behavior | Cost | Admitted? |
|---|---|---|---|
| `a_0` | `p` | `(1,1)` | Yes |
| `a_1` and every later release | `p` | `(2,2)` | Yes |

Extensiveness supplies `c(S)(p)`. Both cost vectors meet the fixed budget. Yet
`(1,1) <_P (2,2)`, and `(2,2) <=_P (1,1)` is false. Each singleton candidate set
has its only element undominated internally, so its own frontier does not rescue
the claim: the later singleton frontier is strictly dominated by the earlier one.

**Verdict: T0 is refuted, even with fixed scope, nonempty unchanged behavior,
and a fixed budget.**

Standing controls in `Audit/DuetControls.lean`:
`every_regressing_release_admitted`, `earlier_strictly_dominates_later`,
`regression_keeps_nonempty_behavior`,
`singleton_release_points_are_undominated`, and
`admission_does_not_imply_release_monotonicity`.

## Voice One — answer 1: the exact missing transition condition

I concede T0. A budget comparison is not a predecessor comparison. The missing
condition is:

\[
\forall n,\quad k_{n+1}\le_P k_n.\tag{CostStep}
\]

This is an explicit extra transition condition, not a consequence of admission.
The strongest general local-to-global result here is an equivalence:

\[
\boxed{(\forall n,\ k_{n+1}\le_P k_n)
\iff(\forall i\le j,\ k_j\le_P k_i).}\tag{T1}
\]

`LegacySequence.cost_adjacent_iff_global` proves T1. No safety predicate,
admission premise, profile restriction, nonempty requirement, catalogue, or
generator coverage premise occurs in it.

**Proof.** For fixed `i`, induct on `i <= j`. The base case is
`paretoLE_refl`. If `k_j <=_P k_i`, compose it with
`k_(j+1) <=_P k_j` using `paretoLE_trans`. Conversely, the all-pairs condition
applied to `i=n`, `j=n+1` gives CostStep. Thus CostStep is exactly the missing
local obligation for all-pairs nonregression; no weaker unrestricted condition
can imply all-pairs nonregression while allowing a failing adjacent pair.

Admission has a separate propagation theorem. If `a_0` is admitted and every
step satisfies both:

\[
p_{n+1}\le_{\mathrm{profile}}p_n,
\qquad k_{n+1}\le_P k_n,
\]

then `LegacySequence.admitted_sequence` proves every release admitted by
induction using the existing `admitted_downward` lemma. `release_sequence`
combines this with T1 and no strict reverse dominance.

If each release is independently rechecked, the downward profile condition is
unnecessary. `rechecked_sequence` instead takes the individual admission results
and CostStep, permitting newly added optional behavior when the next release
passes admission. It also incorporates the fixed positive requirements described
below.

**Named correction:** the theorem is about **guarded temporal nonregression**.
It is not improvement inferred from the original state-admission predicate.

## Voice Two — attack 2: a cycle called improvement

There are two different attacks.

First, can different cost vectors form a cycle under `paretoLE`? No. The actual
definition compares natural numbers componentwise, even though the old export
only packaged reflexivity and transitivity. Mutual comparison forces equal time
and equal compute. This attack fails against the actual cost relation.

Second, can different releases with equal costs pass admission, change behavior,
and return to their starting release? Yes. The control `equalCostCycle` has
complete behavior, then a proper subset, then the complete behavior again, with
cost `(1,1)` throughout. All releases are individually admitted; every adjacent
cost comparison holds; the middle release is distinct; the sequence returns.
No step is a strict cost improvement. A constant sequence is an even smaller
counterexample to inferring strict progress from weak comparison.

**Verdict: distinct-cost cycles are impossible; equal-cost cycles and stuttering
refute any claim that every weakly admitted step is strict progress.**

Standing controls: `stuttering_is_admitted_and_weak_but_not_strict`,
`every_equal_cost_cycle_release_admitted`, and
`equal_cost_cycle_is_weak_and_returns_but_is_not_strict`.

## Voice One — answer 2: strictness exactly characterized

`LegacySequence.paretoLE_antisymm` proves the missing antisymmetry lemma by
applying natural-number antisymmetry to both coordinates.
`strict_iff_no_reverse` proves:

\[
x<_P y\iff x\le_P y\land\neg(y\le_P x).
\]

The strict sequence theorem is exact, not merely sufficient. Under CostStep,
for every `i <= j`:

\[
\boxed{k_j<_P k_i\iff
\exists k,\ i\le k<j\land k_{k+1}<_P k_k.}\tag{T2}
\]

This is `LegacySequence.strict_interval_iff`.

**Proof, right to left.** T1 provides `k_j <=_P k_(k+1)` and
`k_k <=_P k_i`. Composing the witnessed strict coordinate decrease with those
weak comparisons preserves a strict decrease.

**Proof, left to right.** Induct over the finite interval. A weak adjacent cost
comparison is either strict or equality (`strict_or_eq_of_le`). A strict final
edge is the witness. An equal final edge reduces endpoint strictness to the
shorter interval. The empty interval cannot be strict.

`strict_interval_no_return` rules out returning to the starting cost after a
strict step. `return_forces_constant_interval` proves the stronger converse
description of a weak cycle: if endpoint costs are equal, every intermediate cost
is equal to them.

**Named correction:** weak comparison certifies nonregression; strict progress
requires a strict witness. Artifact inequality is not such a witness. No claim
of strict progress at every release, or indefinitely, is made.

## Voice Two — attack 3: remove a required behavior

Let observations be `Bool`. The old release offers both `false` and `true` at
cost `(1,1)`. Let the safe predicate name that complete profile. The next release
offers only `false` at cost `(0,0)`; an alternative offers nothing at all with the
same cheaper cost.

Both next releases are admitted by the original `admitted_downward`, and both
strictly improve the recorded costs. Nevertheless the previously available
`true` observation has disappeared. Downward closure is working exactly as
defined: every offered observation remains allowed. It cannot establish that
every needed observation remains offered.

**Verdict: the attack succeeds even after adding CostStep and demanding a strict
cost improvement. Behavior preservation needs its own positive condition.**

Standing controls: `behavior_deletion_is_admitted_with_strict_cost_win`,
`behavior_deletion_violates_preservation`, and
`empty_behavior_is_admitted_with_strict_cost_win`.

## Voice One — answer 3: retain fixed qualified obligations

Fix a requirement predicate `Q : Observation -> Prop` outside candidate control.
Define:

\[
\operatorname{HoldsRequired}(Q,a)
\iff\forall o,\ Q(o)\Rightarrow a.profile(o),
\]
\[
\operatorname{KeepsRequired}(Q,a,b)
\iff\forall o,\ Q(o)\land a.profile(o)\Rightarrow b.profile(o).
\]

Initial coverage plus adjacent `KeepsRequired` proves coverage at every release,
by direct induction. `required_adjacent_iff_global` also proves the reverse
implication. This preserves only the declared requirements; requiring every
optional observation to remain forever would add an unnecessary hypothesis.

The separately named new transition guard is:

\[
\begin{aligned}
\operatorname{GuardedStep}(S,B,Q,a,b)\iff {}&
\operatorname{Admits}(S,B,b)\\
&\land b.cost\le_P a.cost\\
&\land\operatorname{KeepsRequired}(Q,a,b).
\end{aligned}
\]

Historical `admits` is unchanged. Given initial admission and initial required
coverage, `LegacySequence.guarded_sequence` proves for every guarded sequence:

\[
\begin{gathered}
\forall n,\ \operatorname{Admits}(S,B,a_n)
\land\operatorname{HoldsRequired}(Q,a_n),\\
\forall i\le j,\quad k_j\le_P k_i
\quad\land\quad\neg(k_i<_P k_j).
\end{gathered}\tag{T3}
\]

T2 applies to the same costs. `empty_profile_refused` proves that a nonempty
required set excludes the empty-behavior candidate. With an empty required set,
positive preservation is vacuous; no theorem claims otherwise.

Direct negative controls prove this guard rejects the cost-regression edge and
both behavior-deletion candidates when `true` is fixed as required. The candidate
cannot rescue itself by declaring a smaller `Q` because the theorem holds one
`Q` fixed across the sequence.

**Named limitation:** deriving the authoritative requirement set from real
software and proving that its formal observations represent the required
behavior are application premises. These order-theoretic results do not derive
that extraction automatically.

## Voice Two — attack 4: stronger words than the model supports

I tested the active canonical interface as well as the historical copy.

1. **New-symbol strictness.** Start with symbol `A` costing `5`; add `B` costing
   `10`; then improve `B` to `9` while `A` stays at `5`. Every canonical
   `releaseLe` step holds. The last release strictly dominates its immediate
   predecessor on `B`, but does not strictly improve any metric of the initial
   release, which contains only `A`. Therefore legacy T2 cannot be copied
   wholesale to canonical `releaseDominates` when symbols may be added.
2. **List identity.** Swapping two uniquely named profiles yields unequal lists
   with mutual canonical `releaseLe`. Mutual comparison must not be reported as
   equality of release lists or implementation identities.
3. **Global optimality.** The admitted monotone history `(2,2) -> (1,1) ->
   (1,1) -> ...` remains dominated by the unvisited admitted point `(0,0)`.
   Even a flawless temporal guard cannot turn a visited-history frontier into
   the frontier of all feasible implementations.
4. **Comparison scope.** The generic sequence theorem fixes the measure space,
   axis polarities, and symbol identity relation. Changing these between steps
   is outside its premise. Existing `axes_change_hides_regression` remains a
   control against comparing incompatible coordinate selections.

**Verdict: all three explicit overclaims have checked counterexamples. The
fixed-space theorem survives; broader claims require separately stated evidence.**

Standing controls include
`Canonical.strict_step_on_added_symbol_does_not_improve_initial_metrics`,
`Canonical.reordered_release_is_equivalent_but_not_equal`, and
`strict_improvement_does_not_establish_global_optimality` in
`Audit/DuetControls.lean`.

## Voice One — answer 4: the arbitrary canonical release theorem

The active theorem uses the existing
`SoftwareIsQuantifiable.Interface.releaseLe`, without redefining it. It requires
unique symbols in each release, complete alignment with a fixed measure space,
and a same-symbol no-worse representative for every incumbent profile. Its
`noWorse` relation includes preservation of an incumbent's `observed=true` bit.

For an arbitrary sequence `R : Nat -> Release Symbol Measure`, let:

\[
\operatorname{Adjacent}(M,R)
\iff\forall n,\ \operatorname{releaseLe}_M(R_{n+1},R_n).
\]

`ReleaseSequence.adjacent_iff_all_pairs` proves:

\[
\operatorname{Adjacent}(M,R)
\iff\forall i\le j,\ \operatorname{releaseLe}_M(R_j,R_i).\tag{T4}
\]

The proof uses canonical `releaseLe_trans`; reflexivity follows from the
well-formedness already included in an adjacent certificate. This handles
arbitrarily many releases, arbitrary symbol types, and arbitrary finite measure
spaces with their declared minimize/maximize polarities.

`no_regression` excludes earlier strict canonical release dominance over any
later release. `observed_behavior_retained` carries each earlier observed symbol
forward with the same symbol, an observed bit still true, and no worse readings.
This does not establish initial positive coverage: empty releases can weakly
compare with empty releases, and an initially false observed bit may remain
false. Those cases are standing controls. Initial required coverage remains a
separate obligation; T3 includes it explicitly.

For canonical profile frontiers, `frontier_covered` proves:

\[
q\in\operatorname{frontier}_M(R_i),\ i\le j
\Longrightarrow
\exists p\in\operatorname{frontier}_M(R_j),\ p\le_M q.\tag{T5}
\]

The canonical order compares profiles of the same symbol. T5 is coverage of
those profiles; it is not a comparison between arbitrary whole architectures.

Let `History R n` concatenate the finite releases `R_0,...,R_n`.
`latest_on_history_frontier` proves every profile in `R_n` is on this history's
frontier. Earlier profiles cannot dominate it: an earlier dominator would itself
have a no-worse representative in the latest release; uniqueness of symbol
identities identifies that representative with the purportedly dominated
profile, contradicting strictness.

For general release strictness, `StrictRefinement later earlier` is explicitly
defined as `releaseLe later earlier` together with failure of the reverse
comparison. `strict_refinement_persists` and `strict_refinement_no_return` prove
that a strict refinement anywhere in a weak chain survives to the endpoints and
prevents a return. `metric_dominance_strict` proves canonical metric dominance
implies this strict refinement. The reverse implication is not claimed: adding
a symbol can be a strict refinement without improving an old metric.

`mutually_no_worse_same_profiles` proves mutual comparison yields the same
profile membership, allowing a different list order. This is the appropriate
equivalence at this representation, not equality of source artifacts.

Finally, `stepCheck` is an executable finite decision of the existing canonical
`releaseLe`; `stepCheck_exact` proves both directions of its contract.
`checked_sequence` turns successful adjacent checks into T4 and no reverse
dominance. The supplied proof does not claim the older CLI has automatically
started running this extra guard: invoking it is a separate integration
obligation for any release pipeline making this certification claim.

**Named correction:** history-frontier membership and temporal nonregression
replace unqualified global Pareto optimality. Global optimality still requires
a declared feasible candidate universe and a proved coverage argument. A budget,
a frontier of visited candidates, or a chain certificate is not that argument.

## Voice Two — independent verification and residual premises

The independent counterexample pass checked the actual pinned historical
definitions, then attempted the repaired theorem and the canonical extension.
The repaired statements withstand the controls above. The final independent
recheck must be associated with the exact commit reported with this deliverable;
an author's successful local compilation alone is not closure of the work order.

The repository gate checks every repository Lean file, including the historical
models, both audit modules, the new controls, and examples. Build configuration
is recorded in `lakefile.toml` and included in the gate-input hashes. The earlier
Lean build configuration generated a custom Lake metadata assumption; moving
configuration to TOML removes that file from the proof language without adding
an exception to the logical axiom audit.
Intentional failure inputs use a non-`.lean` fixture extension and are tested as
expected failures. The gate enforces warnings as errors, scans proof escapes,
and inspects compiled declaration dependencies. See `CHECK_CONTROLS.md` for its
precise trust boundary and checks. The normal Lean logical axioms are explicitly
distinguished from custom assumptions; "zero custom axioms" does not mean
"a new foundation with no Lean axioms."

The following claims remain application premises, not conclusions of these
theorems:

| Premise | Evidence needed before applying the theorem to software |
|---|---|
| Faithful costs and scope | Evidence binding readings to the exact release, workloads, environments, units, and fixed comparison axes |
| Faithful behaviors | A justified correspondence between formal observations or observed bits and required program behavior |
| Authoritative obligations | A fixed or independently authorized requirement set, with initial coverage and checked retention |
| Pipeline enforcement | The running admission pipeline actually rejects failed predecessor comparisons and failed retention checks |
| Global candidate coverage | A declared feasible universe and proved coverage if global Pareto optimality is claimed |

## Voice One — final statement of exactly what is proven

At the new checked code pin, the proof establishes:

- Historical admission alone does **not** imply release-sequence improvement.
  The counterexample is itself a checked theorem.
- Adjacent two-cost nonregression is exactly equivalent to nonregression between
  every chronologically ordered pair. Existing downward-admission premises
  propagate admission; separately rechecked admission needs no downward profile
  restriction.
- In that weak two-cost chain, endpoints strictly improve exactly when an
  intervening adjacent step strictly improves. A returning cost interval must
  have been constant throughout.
- Initial coverage and fixed required-observation retention prevent capability
  deletion. The new, separately named `GuardedStep` combines those obligations
  with unchanged historical admission and cost comparison.
- Under the current canonical interface, successful adjacent comparisons imply
  arbitrary-length all-pairs nonregression, observed-symbol preservation,
  frontier coverage, and latest-profile membership in the visited-history
  frontier. Strict refinement cannot cycle; it remains distinct from strict
  improvement of an original symbol's metrics.

No result at the historical README-only pin has changed. No theorem here proves
unconditional improvement, strict improvement at every release, global
optimality over an unproved candidate universe, arbitrary workload performance,
or fidelity of the formal inputs to deployed software.
