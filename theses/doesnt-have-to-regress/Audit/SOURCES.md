# Source pins and definition strata

Prepared from direct GitHub contents/tree retrieval. This file records source provenance, not a build receipt.

## 1. Historical claim and historical family vocabulary

Target: `clpi/software-doesnt-have-to-regress@24d36c13414867e59ae67ccf47f83cc250ce55af`. Its recursive tree was verified to contain only README.md.

Historical subset/closure model is directly available in `clpi/software-is-incrementally-safe@de1b30716e2b758141d5940056f37cd678464032`:

| File | Git blob | Actual definition |
|---|---|---|
| SoftwareIsComposable.lean | 251c0824e8bc48a82bc69a640cbd54d7aff86f63 | profileLE p q := ∀ o, p.obs o → q.obs o; releaseLE R S := ∀ s, profileLE (R.behavior s) (S.behavior s) |
| SoftwareIsIncrementallyCertifiable.lean | 28f33d5fefa1a54e426a5ef45030be2f64794dee | c P p := ∃ q, P q ∧ profileLE p q; paretoLE a b := a.time ≤ b.time ∧ a.compute ≤ b.compute; admits safe bound a := c safe a.profile ∧ paretoLE a.cost bound |
| SoftwareIsIncrementallySafe/Safety.lean | 03a453e85164def6deab5a52d259ce52962d7961 | IsSafetyProperty is downward closure of observation sets; tracesOf/allowedTrace only inspect event membership |

Sources:
- https://github.com/clpi/software-doesnt-have-to-regress/tree/24d36c13414867e59ae67ccf47f83cc250ce55af
- https://github.com/clpi/software-is-incrementally-safe/blob/de1b30716e2b758141d5940056f37cd678464032/SoftwareIsComposable.lean
- https://github.com/clpi/software-is-incrementally-safe/blob/de1b30716e2b758141d5940056f37cd678464032/SoftwareIsIncrementallyCertifiable.lean
- https://github.com/clpi/software-is-incrementally-safe/blob/de1b30716e2b758141d5940056f37cd678464032/SoftwareIsIncrementallySafe/Safety.lean

The copied certifiable module names composable `929d8e355857b6557c1b5d1a6bd505d9bdaeea7f` inside siblingPin, but fetching SoftwareIsComposable.lean at that standalone repo pin returned 404. Do not use that unverified location as source. The vendored audited-safe files above were retrieved directly and exactly match original blob hashes recorded in the certifiable Legacy README.

Caution: downward-closed set properties are broader than allow-lists (e.g. forbidden co-occurrence), but all of these membership-only trace projections erase ordering and multiplicity.

## 2. Actual target at inspected live head and its imported dependencies

Target live head before this task: `858a85e383fbecc9826186aee2cc0101aea5ea62`.

Its lakefile AND manifest pin:

| Dependency | Full pin |
|---|---|
| software-is-composable | 033c12c01299a9b28983bee410c230641adc7d1e |
| software-is-quantifiable | a21c7c56fa028f32014dd795b35b14f688e8fdf1 |

Sources:
- https://github.com/clpi/software-doesnt-have-to-regress/blob/858a85e383fbecc9826186aee2cc0101aea5ea62/lakefile.lean
- https://github.com/clpi/software-doesnt-have-to-regress/blob/858a85e383fbecc9826186aee2cc0101aea5ea62/lake-manifest.json

**Composable imported pin:** Profile.lean blob `cc2ab87e390b283212f185207459f1a9b460aafc`, Admission.lean blob `72dda01e9417b69e20a25dc8f6fa41784324dc69`. Already uses finite per-symbol profiles, not historical subset releaseLE. SymbolAdmitted old new requires same symbol ID, valid old/new bounds, all OLD behaviors retained in NEW, same cost-vector length, each new upper endpoint ≤ old upper endpoint. The Bool gate is exact for this record.

- https://github.com/clpi/software-is-composable/blob/033c12c01299a9b28983bee410c230641adc7d1e/SoftwareIsComposable/Profile.lean
- https://github.com/clpi/software-is-composable/blob/033c12c01299a9b28983bee410c230641adc7d1e/SoftwareIsComposable/Admission.lean

**Quantifiable imported pin:** Pareto.lean blob `732572654548c144f6f2b3fb7037ab5137a676a1`. Already has fixed PriorQualification separate from candidate submission; acceptsRelease = context equality AND qualified containment AND componentwise point noWorse; acceptsReplacement reuses that gate on new upper versus old lower bounds; replacement_no_regression proves every pair of contained realizations no-worse. Frontier tradeoff counterexample already present.

- https://github.com/clpi/software-is-quantifiable/blob/a21c7c56fa028f32014dd795b35b14f688e8fdf1/SoftwareIsQuantifiable/Pareto.lean

Its Interface.lean blob `f60772a2ab3e778d04b9a265adecd90167da4bec` has releaseLe candidate incumbent := ∀ old profile q ∈ incumbent, ∃ new p ∈ candidate, noWorse p q. This imported old version DOES NOT yet include the current interface's release-level unique-ID and all-profile alignment conjuncts.

- https://github.com/clpi/software-is-quantifiable/blob/a21c7c56fa028f32014dd795b35b14f688e8fdf1/SoftwareIsQuantifiable/Interface.lean

**Target's own semantics:** SoftwareDoesntRegress/Profiles.lean calls the imported noQualifiedBehaviorLost on every incumbent behavior list; it treats the entire old list as required. It compares lists positionally; requires equal symbol-list shape and equal axis-list shape; orders BOTH interval endpoints new≤old; accepts additionally requires a strict new behavior or strict endpoint gain. step retains incumbent on refusal. This is a narrower modeled release policy, not all real nonregression. Baseline.lean proves behaviorsKept_eq_composable and only an implication from its endpoint order to composable's upper-bound order. It does not prove whole-gate equivalence or physical behavior fidelity.

## 3. Current siblings, distinct from target's actual imports

| Repo | Head inspected | Important change or relation |
|---|---|---|
| software-is-quantifiable | d88acbdc3ba78fff994067d2c73bcc01622b3f61 | acceptsRelease still has all three checks. Interface.releaseLe additionally requires unique IDs and every profile aligned. Coverage explicitly labels physical coverage as a premise. |
| software-is-composable | 7b1746467a410e9e5ae309f2a86bc4cd37700989 | Profile/Admission blobs identical to imported 033c12c. Bridge.oneSymbol has conditional gate agreement and counterexamples to removing its hypotheses. |
| software-is-incrementally-safe | 32174a7cbf2b12f7390a07ccdb7041fbf6043886 | OrderedIncrement supports input-indexed ordered finite traces, prefix safety, NI, and cone equality under explicit locality. |
| software-optimality | 0bbc1f3b8aa38afe17e02ccbd7ddd0e7722b3cb0 | ScopedFrontier.noRegression separates same-contract admission and incumbent componentwise comparison from frontier selection; ComparisonContract binds units/axes/workload/venue/epoch. |

Key URLs:
- https://github.com/clpi/software-is-quantifiable/blob/d88acbdc3ba78fff994067d2c73bcc01622b3f61/SoftwareIsQuantifiable/Interface.lean
- https://github.com/clpi/software-is-quantifiable/blob/d88acbdc3ba78fff994067d2c73bcc01622b3f61/SoftwareIsQuantifiable/Coverage.lean
- https://github.com/clpi/software-is-composable/blob/7b1746467a410e9e5ae309f2a86bc4cd37700989/SoftwareIsComposable/Bridge.lean
- https://github.com/clpi/software-is-incrementally-safe/blob/32174a7cbf2b12f7390a07ccdb7041fbf6043886/SoftwareIsIncrementallySafe/OrderedIncrement.lean
- https://github.com/clpi/software-optimality/blob/0bbc1f3b8aa38afe17e02ccbd7ddd0e7722b3cb0/ScopedFrontier.lean
- https://github.com/clpi/software-optimality/blob/0bbc1f3b8aa38afe17e02ccbd7ddd0e7722b3cb0/ComparisonContract.lean

## Wording constraints for the audit

“Superset-of-qualified” is an isolated behavioral reading. Calling the actual imported/current acceptsRelease containment-only is wrong. Saying the live family cannot express ordering or environment dependence is also wrong; ordered traces and context-indexed contract vocabulary exist. What is missing from the target's point/list projection is that information and a proven model-to-execution bridge. Even where the family can represent it, physical completeness, truthful measurements, correct dependency extraction, liveness/probability/continuous-time semantics remain separate obligations.

The old closure c and today's Qualification.Derives are different operations; do not identify them by the shared word “closure.”
