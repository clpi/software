# Standing counterexamples for the review statement

[ReviewControls.lean](ReviewControls.lean) and
[ReviewStrengtheningControls.lean](ReviewStrengtheningControls.lean) contain
eighteen kernel-checked synthetic counterexamples. They constrain the claim; they do not establish a production
system's model fidelity, tool qualification, requirements completeness, or
permission to omit a required review activity. All computations use the imported
family definitions at the revisions fixed in this package's manifest.

| Control theorem in namespace `ReviewControls` | Concrete witness | Claim ruled out |
|---|---|---|
| `derived_claim_can_have_false_interpretation` | A root asserts unit agreement, so `Qualification.Derives` accepts it, while its supplied physical interpretation is `1 = 2`, which is false. | Derivability alone establishes the truth of roots or the fidelity of the interpretation. The numbers are synthetic labels, not a reconstruction of an accident. |
| `novel_review_atom_changes_qualification` | The bounded upstream checker returns `[0]` from roots `[0]` and `[0, 1]` after review adds root `1`. | Every additional review fact is already redundant. |
| `latent_rule_is_conservative_only_at_current_basis` | Adding rule `[1] → 2` changes nothing with root `0`; after root `1` arrives, the reviewed basis derives `2` and the unreviewed basis does not. | Conservative extension at one pin establishes permanent omission permission after later evidence changes. |
| `append_only_history_does_not_make_live_support_monotone` | An authorized withdrawal leaves the original claim event admitted in history but makes its support cease to be `Admission.live`. | Append-only history implies monotone qualification inputs. Normalization must precede the closure comparison. |
| `empty_manifest_does_not_cover_an_actual_execution` | An empty manifest has no missing rows, while an independently named actual execution `7` is missing from the empty ledger and cannot satisfy `Coverage.PlatformPremise`. | Empty reported gaps establish complete coverage of actual activity. |
| `new_provenance_need_not_change_candidate_admission_or_frontier` | A fresh support identifier changes admitted event history; projecting either support `[0]` or `[0, 1]` yields a valid receipt for the same subject, admitted under the same contract and retained in the same nonempty frontier. | Event history equality is necessary for candidate decision equality. The fixture preserves the extra event instead of deleting it to manufacture redundancy. |
| `one_redundant_outcome_does_not_establish_prospective_redundancy` | The observed review outcome `false` adds nothing, but another possible Boolean outcome adds root `1`. | Absorption of one completed review's output proves all future admissible review outputs will be absorbed. |
| `raw_duplicate_receipts_can_reverse_qualification` | The upstream two-receipt policy qualifies its exact receipt set; appending a duplicate receipt makes `ScopedEvidence.qualify` false. | Semantic support equality permits an implementation to bypass canonical projection and concatenate arbitrary raw receipts. |
| `changing_the_catalogue_changes_the_frontier` | A subject of cost `2` is selected alone; adding a separately scoped, admitted subject of cost `1` removes the former subject from the frontier. | The frontier is independent of the declared candidate catalogue. |
| `equal_empty_frontiers_do_not_establish_admission` | An empty catalogue and a catalogue containing only a failing subject both produce the empty frontier; the subject is still not admitted. | Equality of frontiers is evidence that a release is qualified or that review omission has been instantiated successfully. |

## Recheck

From this directory, use the pinned Lean toolchain:

```sh
lake build +ReviewControls +ReviewStrengtheningControls
lake env lean -DwarningAsError=true ReviewControls.lean
lake env lean -DwarningAsError=true ReviewStrengtheningControls.lean
```

Both files print the axiom dependencies of every control theorem. Nine controls
use no axioms; the other nine use only Lean's standard `propext`,
`Classical.choice`, and `Quot.sound`. No control introduces a custom axiom or admits an
unfinished proof. These controls prove their stated counterexamples; the main
review-omission claims have their own separately checked proof terms.

## Boundaries still requiring application evidence

A proof of these examples does not check whether a real requirements inventory is
complete, whether a deployed binary realizes its formal model, whether a checker
is qualified for a particular assurance objective, whether review supplies an
independent approval, or whether an applicable standard permits substitution.
Those remain the explicitly listed application premises of the main statement.
Similarly, these examples make no economic claim: replacing review can require
more proof construction and maintenance work than the review itself.

## Controls from the proof-strengthening counterexample attempt

These eight controls are in namespace `ReviewStrengtheningControls`. They attack
possible strengthenings at the same pinned imported definitions.

| Control theorem | Concrete witness | Claim ruled out |
|---|---|---|
| `one_sided_inclusion_does_not_imply_target_rule_closure` | The source has no roots and only rule `[1] → 2`, so derives nothing. The target has root `1` and no rules, so contains the source closure but is not closed under the source's latent rule. | One-direction closure inclusion implies target closure under every source rule, including source-unreachable premises. The usual target-closed certificate is sufficient, but necessity needs a stronger relation between the closures or a restriction to source-derivable premises. |
| `equal_admission_does_not_preserve_frontier` | Admission agrees for every subject; the two catalogue subjects' bounded costs swap from `2,1` to `1,2`, so the selected subject changes. | Admission equality alone preserves the frontier. Metric/ordering effects must also be covered. |
| `equal_frontier_does_not_preserve_all_admissions` | The better subject remains selected, while the dominated subject changes from admitted to refused. | Frontier equality implies admission equality for every subject. |
| `equal_observations_do_not_require_equal_input` | Changing each sole receipt's ID from `0` to `1` changes the concrete inputs, while every subject's admission and the nonempty frontier remain identical. | Input equality is necessary for decision equality; harmless provenance differences may be retained. |
| `decision_noninterference_strictly_weaker_than_input_noninterference` | The nonempty relevant slice is `{1}`; the projector changes only receipt IDs according to irrelevant proposition `X(0)`. `RespectsDecisions` holds, `RespectsRelevant` fails, and the named baseline subject is admitted. | Exact input noninterference is necessary for observational noninterference. This directly proves the newer projector premise is strictly weaker, without an empty or wholly refused application. |
| `decisions_do_not_determine_relevant_qualification` | A constant projector preserves every admission and the frontier even though required atom `1` is absent before and present after. | Decision equality alone proves relevant qualification equality or completeness of the projector. Objective preservation remains a separate obligation. |
| `incomplete_outcome_inventory_can_hide_a_checked_difference` | Every outcome in the nonempty inventory `[false]` passes `checkRelevant`; the omitted Boolean outcome `true` adds relevant root `1` and returns `some false`. | Passing the supplied outcome inventory establishes completeness of that inventory or uniform preservation across all allowed outcomes. |
| `omitted_relevant_atoms_can_hide_a_checked_difference` | Empty `K` and `K=[2]` both produce `some true`; including encoded atom `1`, which actually changes, produces `some false`. | Checker acceptance establishes that the supplied relevant slice covers the real objectives or that any listed atom is derivable/true. |

The first control blocks a false converse encountered while strengthening the
closure certificate. Five controls delimit the legitimate weakening from exact
projected-input equality to preservation of the declared decision observations. The final two
show that the executable checker cannot supply its own relevance or outcome
coverage premises.
None treats unchanged decisions as evidence of semantic truth or process permission.
