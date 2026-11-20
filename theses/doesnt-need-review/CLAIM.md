# When a named review is redundant

Status: **formal statement, not a completed proof or an instantiated omission
certificate**. The three proposed statements are defined as `Prop` values in
[`statement/ReviewStatement.lean`](statement/ReviewStatement.lean), so their
actual imports, types, and quantifiers are checked without accepting an
unfinished proof. Their status is SPECIFIED. The next proof work is to inhabit
these propositions and discharge application premises at an exact pin.

The audit's inspected repository pin was
`ae5f3918f7689267d07044a00e6a11b071510bba`. This statement is based on the later
target head `1d504014be0c727b3f12e4d8e17f47dfceb118b6`; the existing narrow
proofs are preserved. A check of the present statement does not retroactively
change the claim at either earlier pin.

## 1. Claim and unit of omission

For a particular review activity `r`, artifact/configuration, assurance epoch,
and independently declared objective set, review is technically redundant when
removing that activity preserves the qualification of every relevant objective
and preserves candidate admission and the frontier under the same contract.
Prospective omission additionally requires independent evidence for those
objectives and a complete bound on admissible review outcomes. Practical
permission to omit the activity requires the applicable assurance process to
allow its replacement, with required independence and tool assurance retained.

This claim distinguishes three questions:

1. **Retrospective redundancy:** did a completed review add any relevant
   qualification or change a declared decision at this pin?
2. **Prospective technical omission:** can every admissible outcome of the
   review be shown incapable of changing those objectives or decisions, using
   evidence available independently of the review?
3. **Permissible omission:** does the named standard/edition, integrity level,
   objective, and accepted assurance plan permit this activity to be omitted or
   replaced by the supplied evidence?

An answer to the first does not prove the second or third. “Review” here is the
named verification activity with specified objectives, not all communication,
design exploration, knowledge transfer, requirements discovery, or approval.
If any of those functions is an objective of the activity, it must be included
in the declared scope or retained separately; it cannot silently disappear.

## 2. Imported authority, at exact pins

No qualification, admission, or Pareto semantics are reimplemented here.
`Q`, `BasisConservative`, `SameRelevant`, `RespectsRelevant`, and `SameDecisions`
only name statements assembled from the imported definitions. The complete
declaration/path map is in [`imports.lock.json`](imports.lock.json).

**QPIN** = `clpi/software-is-quantifiable` at
[`d88acbdc3ba78fff994067d2c73bcc01622b3f61`](https://github.com/clpi/software-is-quantifiable/tree/d88acbdc3ba78fff994067d2c73bcc01622b3f61).

**OPIN** = `clpi/software-optimality` at
[`0bbc1f3b8aa38afe17e02ccbd7ddd0e7722b3cb0`](https://github.com/clpi/software-optimality/tree/0bbc1f3b8aa38afe17e02ccbd7ddd0e7722b3cb0).
OPIN's own package pins QPIN. The separate statement package pins both directly.

| Vocabulary | Imported definitions | Exact file and pin | Meaning used here |
|---|---|---|---|
| Qualification and closure | `Qualification.Derives`, `Qualification.Closed` | [`Qualification.lean`, OPIN](https://github.com/clpi/software-optimality/blob/0bbc1f3b8aa38afe17e02ccbd7ddd0e7722b3cb0/Qualification.lean) | Least finite-premise derivability closure; atoms keep their exact scope, polarity, lineage, and support meaning. |
| Closure evidence | `Qualification.least`, `closed`, `monotone`, `soundness`; `ExecutableClosure.checkedClose`, `checkedClose_admitted` | `Qualification.lean`, [`ExecutableClosure.lean`, OPIN](https://github.com/clpi/software-optimality/blob/0bbc1f3b8aa38afe17e02ccbd7ddd0e7722b3cb0/ExecutableClosure.lean) | Proof or finite checked closure; soundness separately requires valid roots and valid rules. |
| Event admission and live support | `Admission.Key`, `Payload`, `Event`, `admitted`, `live`, `normalized` | [`Admission.lean`, OPIN](https://github.com/clpi/software-optimality/blob/0bbc1f3b8aa38afe17e02ccbd7ddd0e7722b3cb0/Admission.lean) | Membership plus authorization; live claims also exclude authorized withdrawal and incompatible same-key payloads. |
| Authoritative graph view | `AdmissionHypergraph.Decoder`, `graph`, `ScopedAtom`, `scopedGraph`; `HypergraphIncremental.Hypergraph`, `derives` | [`AdmissionHypergraph.lean`, OPIN](https://github.com/clpi/software-optimality/blob/0bbc1f3b8aa38afe17e02ccbd7ddd0e7722b3cb0/AdmissionHypergraph.lean), `HypergraphIncremental.lean` | Roots/rules derive from live admitted evidence. The decoder is not automatically faithful. |
| Receipt qualification | `ScopedEvidence.Scope`, `Requirement`, `Receipt`, `Policy`, `qualify` | [`ScopedEvidence.lean`, OPIN](https://github.com/clpi/software-optimality/blob/0bbc1f3b8aa38afe17e02ccbd7ddd0e7722b3cb0/ScopedEvidence.lean) | Exact scope/round, required receipts, nonempty obligations, uniqueness, observed pass, and bounded present measurements. |
| Candidate admission and frontier | `ScopedFrontier.Contract`, `Subject`, `Input`, `admitted`, `dominates`, `select`, `selected_exact`; `FiniteFrontier.frontier` | [`ScopedFrontier.lean`, OPIN](https://github.com/clpi/software-optimality/blob/0bbc1f3b8aa38afe17e02ccbd7ddd0e7722b3cb0/ScopedFrontier.lean), `FiniteFrontier.lean` | Contract-owned qualification followed by Pareto nondomination in the named catalogue. |
| Quantified preservation and economics | `SoftwareIsQuantifiable.Interface.Profile`, `aligned`, `noWorse`, `dominates`, `frontier` | [`SoftwareIsQuantifiable/Interface.lean`, QPIN](https://github.com/clpi/software-is-quantifiable/blob/d88acbdc3ba78fff994067d2c73bcc01622b3f61/SoftwareIsQuantifiable/Interface.lean) | Behavior preservation and ordered metric comparison are distinct obligations; missing coordinates do not count as improvement. |
| Execution evidence coverage | `SoftwareIsQuantifiable.Coverage.recorded`, `missing`, `scopedMissing`, `scoped_audit_complete`, `PlatformPremise`, `ScopedPlatformPremise` | [`SoftwareIsQuantifiable/Coverage.lean`, QPIN](https://github.com/clpi/software-is-quantifiable/blob/d88acbdc3ba78fff994067d2c73bcc01622b3f61/SoftwareIsQuantifiable/Coverage.lean) | Recorded, validator-accepted witnesses for an independently supplied scoped roster; real roster completeness and platform mediation remain premises. |

The original package still uses `software-is-composable` at
`033c12c01299a9b28983bee410c230641adc7d1e`, which depends on quantifiable at
`37917a4195efb1d0423a422ee954d767a9be1cd3` and vendors some optimality module
names. Those older definitions justify only the retained legacy lemmas. They
are not substituted for OPIN/QPIN in this statement. Separate Lake environments
prevent two files named `Qualification` from silently becoming one authority.

## 3. Qualification theorem, without a review-bit assumption

Let `A` be the family's scoped atom type, and let `(B₀,R₀)` and `(B₁,R₁)` be
the normalized live root/rule bases without and with the named review. Define,
using the imported operation only,

\[
Q_i(a) := \operatorname{Qualification.Derives}(B_i,R_i,a).
\]

**F1 — full closure characterization (SPECIFIED):**

\[
\begin{aligned}
(\forall a,\ Q_0(a)\leftrightarrow Q_1(a))\quad\Longleftrightarrow\quad&
(\forall a,\ B_1(a)\Rightarrow Q_0(a))\ \land\ \operatorname{Closed}(R_1,Q_0)\\
&\land\ (\forall a,\ B_0(a)\Rightarrow Q_1(a))\ \land\ \operatorname{Closed}(R_0,Q_1).
\end{aligned}
\]

This is a certificate obligation on roots and inference rules, not a premise
that a reviewer agrees with a checker. Each direction can be established by
`Qualification.least`; necessity uses root inclusion and closure. It permits
changes in both bases, including correctly normalized withdrawals, provided
their entire qualification consequences agree. No graph reachability
projection turns a joint premise list into independent sufficient evidence.

For a positive extension `B₀ ⊆ B₁`, `R₀ ⊆ R₁`, the last two certificate
obligations follow from monotonicity. For fixed rules and added review atoms
`V`, with `B₁(a) := B₀(a) ∨ V(a)`, the exact condition reduces to
`∀ a, V a → Q₀ a`. This special case is retrospective unless proved uniformly
for every admissible review outcome before doing the review.

Full closure equality is deliberately stronger than objective-relative
redundancy. A fresh review receipt with a new support identity may add
provenance while supplying no new objective evidence. Its history remains
append-only. In particular, F1 does **not** promise equality of
`Admission.admitted` event sets. Candidate admission below is the distinct
`ScopedFrontier.admitted` definition.

## 4. Weaker hypotheses for a declared objective boundary

Let `K : A → Prop` be the independently fixed relevant slice: all required
objective atoms and all positive, negative, scope, conflict, and availability
facts that can affect the declared decisions. It must not be chosen after
seeing an inconvenient review outcome. Keep the same projector

```lean
project : (A → Prop) → ScopedFrontier.Subject → ScopedFrontier.Input
```

and require the noninterference certificate

\[
\forall X,Y,\ [\forall a\in K,\ X(a)\leftrightarrow Y(a)]
\Rightarrow \operatorname{project}(X)=\operatorname{project}(Y).
\]

**F2 — relevant qualification suffices (SPECIFIED):** if `Q₀` and `Q₁` agree
on `K`, then for the same contract `k` and exact ordered catalogue `C`:

\[
\begin{aligned}
\forall s,\quad
\operatorname{admitted}(k,s,\operatorname{project}(Q_0,s))
&=\operatorname{admitted}(k,s,\operatorname{project}(Q_1,s)),\\
\operatorname{select}(k,C,\operatorname{project}(Q_0))
&=\operatorname{select}(k,C,\operatorname{project}(Q_1)).
\end{aligned}
\]

F1 supplies a sufficient route for any fixed projector. F2 also allows new
irrelevant provenance without demanding full-closure equality. Certifying
noninterference and relevance completeness is essential: an arbitrary constant
projector would make decisions equal while ignoring all requirements.

There is no new frontier algorithm here. `select` is the imported filter of
admitted subjects followed by the imported frontier. The exact list equality
uses the same ordered catalogue. Reordered catalogues justify membership
equality through `selected_order_independent`, not necessarily equal list
serialization. A search expansion is a new qualification. Global optimality
requires the separate upstream coverage/feasibility premises; it is not a
consequence of unchanged frontier membership.

### How a finite instance is checked

Use `ExecutableClosure.checkedClose` independently on each normalized basis,
require successful results, and compare the resulting memberships on `K`.
Its `checkedClose_admitted` theorem supplies equivalence to `Derives` for the
encoded roots/rules and checks bounded roots and rule heads. It does not prove
that the supplied rules, universe, interpretation, or review outcome inventory
captures reality. Those are P2–P7 below. Infinite domains need a symbolic
certificate; a timeout or incomplete enumeration is not a proof of absence.

Prospective evidence must cover **every admissible outcome** `o`, with bases
`(B₁ o,R₁ o)`. A finite outcome model can be exhaustively checked; a symbolic
model needs a uniform proof. Declaring only an approving outcome admissible is
not a coverage argument. Outcomes that discover missing requirements or an
invalid environment assumption defeat the applicability premise and reopen
the qualification rather than being filtered out as inconvenient.

## 5. When review is still load-bearing

An actual load-bearing witness is a review contribution that supplies otherwise
missing relevant support, changes a required decision, exposes a false validity
or fidelity premise, or satisfies an otherwise unmet mandatory process
objective. For example, in a positive fixed-rule extension, an atom
`a` with `V a`, `K a`, and `¬Q₀ a` witnesses a relevant qualification change.
For arbitrary normalized bases, `K a ∧ ¬(Q₀ a ↔ Q₁ a)` witnesses it directly.

**Failure to establish a premise is weaker:** it blocks omission, but does
not prove a human reviewer would find a problem. The gate must report
`unestablished` separately from `load-bearing`. A qualification rejection or
empty frontier is not a successful release.

All rows below are **application obligations**. The named family checkers
exist at the imported pins; no evidence package for a particular regulated
deployment is supplied by this statement.

| ID | Checkable condition that blocks omission; load-bearing witness when available | Discharging evidence, or explicit premise |
|---|---|---|
| P1: independence of the baseline | The purported replacement depends directly or transitively on `r`, its approval, its discovered fact, or a certificate supported only by it. | Provenance/dependency gate removes the review and all support paths that require it; independently supported facts may remain. Bind the resulting roots, rules, and authorization snapshot. Independence of the actual ingestion boundary remains a premise. |
| P2: complete objectives and review outcomes | An applicable requirement, hazard, failure mode, integration effect, human/process function, or admissible adverse outcome is absent. A newly identified objective is a load-bearing witness. | Independently approved objective and outcome inventory, total traceability mapping, nonempty objective set, and proof that all relevant decision inputs are in `K`. Real-world completeness is an explicit premise unless separately proved. Test coverage alone does not establish it. |
| P3: requirements-to-model fidelity | A property is weaker than intended, units differ, an antecedent is unreachable/contradictory, or a requirement was copied from the same erroneous implementation. | Independent model-fidelity argument, requirement/property traceability, abstraction/refinement obligations, satisfiability and nonvacuity checks, and justified environment assumptions. Unformalized stakeholder intent remains a premise. Review that finds such a mismatch is load-bearing. |
| P4: model-to-code/environment fidelity | The proof/model refers to different source, object code, configuration, libraries, hardware, scheduler, compiler, or environment than the subject being released. | Authenticated artifact/configuration bindings, build and translation/refinement certificates, dependency and integration accounting, and model/runtime correspondence. Unsupported translation, hash collision/binding, or physical-environment assumptions remain premises. Hash equality alone does not establish semantic fidelity or authentic artifact identity. |
| P5: authentic, live, scoped evidence and actual coverage | A record is unrecorded, unauthorized, stale, from another scope/round, withdrawn, conflicting, or duplicated; a real execution is absent from the roster. | `Admission.live`/`normalized`, faithful `AdmissionHypergraph` decoding, `ScopedEvidence.qualify`, and `Coverage.scopedMissing = []` with `scoped_audit_complete`. Authentication, roster completeness, occurrence identity, sensor placement and platform mediation remain explicit premises. A matching witness value alone is insufficient. |
| P6: root/rule truth and tool assurance | An accepted root is false, a rule is unsound, a solver result lacks checked evidence, or a needed tool qualification case is absent. | `validRoots : ∀ a, B₀ a → TrueAt a` and `validRules : Qualification.Closed R₀ TrueAt`; checked proof certificates, pinned trusted checker/kernel, and the applicable tool qualification/validation case for its actual intended use. Repository hygiene is not DO-330 qualification. Empirical/calibration and trusted-computing-base assumptions remain premises. |
| P7: closure and projection preservation | A relevant atom differs, a review supplies a necessary rule, a withdrawal changes live support, or a projector reads hidden ledger order/identity/cache state. | F1's two-direction root/rule certificates or F2's checked relevant-closure equality plus `RespectsRelevant`; binding of the production projector to that model. For prospective omission quantify over all P2 outcomes. A concrete changed atom/admission/frontier is a falsifier. |
| P8: nonvacuous successful application | Both frontiers are empty, all candidates are refused, objectives are empty, or there is no admissible modeled outcome. | A named subject in the catalogue, baseline `ScopedFrontier.admitted = true`, a nonempty required objective set already derived without review, and a nonempty admissible outcome model. This does not require the admitted subject itself to be nondominated. |
| P9: unchanged qualification context | Roots, rules, decoder, authorities, objectives, metric units, policy, catalogue, venue, harness, environment, or epoch changed after the certificate. | Exact snapshot manifest and dependency invalidation followed by requalification; or a stronger theorem covering all allowed changes. Today's conservative latent rule can become productive after a later root arrives. A prior pin is not a current waiver. |
| P10: process permission and required independence | The named standard/edition/integrity level or accepted assurance plan still requires review, approval, independence, or an assessment that the replacement does not fulfill. | An objective-by-objective applicability/substitution matrix with authoritative basis and retained independent evidence. Where the activity is required and cannot be substituted, perform it. Permission is external to the mathematical theorem and remains a premise until supplied. |
| P11: measured economic improvement, only if claimed | Qualification is unchanged but proof construction, checking, tool assurance, maintenance, or failure handling costs outweigh the omitted review. | A separate scoped before/after profile using QPIN's `aligned`/`noWorse`/`dominates`, with measured replacement costs and a declared horizon. No resource saving or Pareto dominance is claimed by F1–F3. This premise is not needed for technical redundancy. |

### Standards evidence and its limits

These sources motivate P2–P6 and P10. They do not instantiate those premises.

- [FAA AC 20-115D](https://www.faa.gov/regulations_policies/advisory_circulars/index.cfm/go/document.information/documentID/1032046)
  recognizes DO-178C, DO-330 and DO-333 as part of an acceptable means of
  compliance. Applicability belongs to the specific assurance plan.
- [NASA's DO-178C/DO-333 technical overview, section IX](https://ntrs.nasa.gov/api/citations/20120016835/downloads/20120016835.pdf?attachment=true)
  describes formal analysis replacing or augmenting specified verification
  activities, with justified assumptions and formal representations. This is
  a primary technical explanation, not a reproduction of the normative standard.
- [FAA report TC-15/57, sections 4.3.2–4.3.3](https://www.faa.gov/sites/faa.gov/files/aircraft/air_cert/design_approvals/air_software/TC-15-57.pdf)
  discusses traceability/inspection of formalized requirements and a concrete
  shared-model antecedent error that makes a proof meaningless. The report is
  research, not FAA policy. P3 retains that fidelity obligation.
- [NASA's DO-330 tool qualification study](https://shemesh.larc.nasa.gov/fm/FMinCert/DO-330-case-studies-RC.html)
  investigates independently checked proof certificates and qualifying the
  checker. It does not qualify Lean or this repository.
- [IEC's 2010 commented publication, Part 3, section 7.4.6.1](https://share.ansi.org/Shared%20Documents/News%20and%20Publications/Other%20Documents/IEC%2061508%20Commented%20Version.pdf)
  includes a module code-review requirement; section 7.4.7 discusses reduction
  of some testing through formal methods. A testing reduction is not a blanket
  review exemption. The commented/redline text contains superseded wording;
  P10 must identify the applicable edition and actual permitted route.
- Official [ISO 26262-6:2018](https://www.iso.org/standard/68388.html) and
  [ISO 26262-8:2018](https://www.iso.org/standard/68390.html) catalogues establish
  software verification and supporting-process/tool-confidence scope. Exact
  ASIL-specific review/independence/substitution requirements were not obtained
  from the normative text here; they remain P10, to be resolved against the
  licensed applicable standard and accepted safety plan.

## 6. Falsifiability, controls, and closure status

The [in-tree controls](statement/COUNTEREXAMPLES.md) use the imported family
operations and refute the overstrong readings: false roots despite equal
closures; novel relevant support; latent rules becoming productive; authorized
withdrawal; empty or incomplete evidence rosters; fresh provenance without a
decision change; a redundant completed outcome with a novel possible outcome;
duplicate receipts; search-space expansion; and empty-frontier vacuity.

A counterexample to F1 has both certificate directions true but different
closures, or equal closures with a certificate obligation false. A counterexample
to F2 has equal relevant closure and a valid noninterference certificate but
different imported admission/frontier results. A counterexample to F3 satisfies
every displayed mathematical hypothesis yet has a false required objective or
a differing decision for an allowed outcome. A deployment can instead fail
P1–P10: that is a counterexample to applying the claim there, even when the
abstract theorem remains valid. Record both kinds without conflating them.

The independent counterexample attempt strengthened this statement by requiring
prospective outcome coverage, allowing objective-relative redundancy while
retaining fresh provenance, using two-sided closure certificates for
nonmonotone changes, preventing vacuous admission, and pinning the epoch.
[`VERIFICATION.md`](VERIFICATION.md) records the final recheck boundary.

F1, F2 and F3 remain SPECIFIED until theorem terms are supplied and independently
rechecked at their pin. P1–P10 remain OPEN for each real application until its
evidence is admitted. P11 remains OPEN only for a proposed economic claim.
No current compiler, reviewer, deployment, or safety authority is asserted to
satisfy them. Proving a stronger statement or eliminating a premise requires
a new pinned certificate and renewed counterexample attempt.

## 7. Final Lean-ready theorem and its open premises

The statement below uses the actual declarations in `ReviewStatement.lean`.
`Q` is only an abbreviation for `Qualification.Derives`; `SameRelevant` is
pointwise equivalence on the declared `relevant` predicate;
`RespectsRelevant` is the noninterference condition in section 4;
`SameDecisions` is equality of imported candidate-admission bits and the exact
imported frontier list. `Outcome` ranges over the complete review outcome model,
not merely the outcome seen in an already completed review.

**F3 — prospective technical review redundancy (SPECIFIED):**

```lean
import ReviewStatement
open ReviewStatement

theorem review_omission
    {A Outcome : Type}
    (B₀ : A → Prop) (R₀ : List A → A → Prop)
    (B₁ : Outcome → A → Prop) (R₁ : Outcome → List A → A → Prop)
    (allowed : Outcome → Prop) (relevant required TrueAt : A → Prop)
    (project : (A → Prop) → ScopedFrontier.Subject → ScopedFrontier.Input)
    (k : ScopedFrontier.Contract) (catalogue : List ScopedFrontier.Subject)
    (subject : ScopedFrontier.Subject)
    (objectives_exist : ∃ a, required a)
    (outcomes_exist : ∃ o, allowed o)
    (subject_listed : subject ∈ catalogue)
    (baseline_admitted :
      ScopedFrontier.admitted k subject (project (Q B₀ R₀) subject) = true)
    (objectives_relevant : ∀ a, required a → relevant a)
    (objectives_discharged : ∀ a, required a → Q B₀ R₀ a)
    (valid_roots : ∀ a, B₀ a → TrueAt a)
    (valid_rules : Qualification.Closed R₀ TrueAt)
    (projection_respects : RespectsRelevant relevant project)
    (all_outcomes_conservative : ∀ o, allowed o →
      SameRelevant relevant (Q B₀ R₀) (Q (B₁ o) (R₁ o))) :
    (∀ a, required a → TrueAt a) ∧
    (∀ o, allowed o →
      SameRelevant relevant (Q B₀ R₀) (Q (B₁ o) (R₁ o)) ∧
      SameDecisions k catalogue project (Q B₀ R₀) (Q (B₁ o) (R₁ o)) ∧
      ScopedFrontier.admitted k subject
        (project (Q (B₁ o) (R₁ o)) subject) = true)
```

There is intentionally no proof body, proof admission, or custom logical axiom
for this claim. `OmissionClaim` is the complete typechecked proposition above.

The premises it openly rests on are:

1. **P1:** the baseline and its support are independent of the review removed.
2. **P2:** objectives, relevant inputs, and admissible review outcomes are
   complete for the named activity; all displayed universal conditions really
   range over that independently justified scope.
3. **P3:** `TrueAt`, the required atoms, and the formal properties faithfully
   express the intended requirements, including nonvacuity and assumptions.
4. **P4:** the model and evidence concern the actual source/object/configuration
   and environment being admitted.
5. **P5:** evidence is authentic, live, correctly decoded and scoped, and actual
   execution coverage has an independently complete roster where applicable.
6. **P6:** `valid_roots` and `valid_rules` hold; the checker/kernel and associated
   tools have the needed soundness and intended-use qualification evidence.
7. **P7:** every admissible outcome has the stated relevant-closure certificate,
   and the actual projector satisfies `projection_respects`; F1 can supply a
   stronger full-closure certificate without redefining qualification.
8. **P8:** required objectives and admissible outcomes are nonempty, the named
   subject is in the catalogue, and its review-independent admission succeeds.
9. **P9:** the pinned bases, interpretation, contract, catalogue, authorities,
   toolchain and environment remain the ones for which the certificate was
   checked; changes trigger requalification.
10. **P10:** the applicable assurance plan permits this specific omission or
    substitution and preserves all mandatory independence/approval objectives.
    The theorem does not derive this external permission.
11. **P11, only for an added cost claim:** a separate faithful, scoped measured
    comparison includes the full cost of replacement assurance. No saving or
    Pareto improvement follows from the theorem alone.
