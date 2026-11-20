# Standing counterexamples for the review statement

[ReviewControls.lean](ReviewControls.lean) contains ten kernel-checked synthetic
counterexamples. They constrain the claim; they do not establish a production
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
lake build +ReviewControls
lake env lean -DwarningAsError=true ReviewControls.lean
```

The file prints the axiom dependencies of every control theorem. Seven controls
use no axioms; the other three use only Lean's standard `propext` and, in the
coverage control, `Quot.sound`. No control introduces a custom axiom or admits an
unfinished proof. These are proofs of the counterexamples, not proofs of the
repository's proposed review-omission theorem.

## Boundaries still requiring application evidence

A proof of these examples does not check whether a real requirements inventory is
complete, whether a deployed binary realizes its formal model, whether a checker
is qualified for a particular assurance objective, whether review supplies an
independent approval, or whether an applicable standard permits substitution.
Those remain the explicitly listed application premises of the main statement.
Similarly, these examples make no economic claim: replacing review can require
more proof construction and maintenance work than the review itself.
