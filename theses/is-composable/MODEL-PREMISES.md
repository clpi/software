# Composition Model: Claims and Premises

This document and the `PointwiseModel` / `InteractionModel` interfaces were
preserved from concurrent main commit `7a408c7b752df6f47b9cf60ddbd89d4001b5e22a`.
The fuller audited module is now also present exactly, up to its namespace,
under `Legacy`. The recursive positive-interaction strengthening, exact uniform
safety criterion, semantic rule simulation, independent controls and complete
application-premise ledger are in [docs/composability-audit.md](docs/composability-audit.md).
The one-step finite interface below remains distinct: no equivalence of its
list evaluator with the recursive predicate closure is assumed.
`Rule.requires` can also be empty, so the finite evaluator permits nullary
effects without any selected component. The recursive binary closure requires
seed observations. `Audit/OneShotBoundary.lean` preserves this distinction and
the absence of recursive effect feedback as standing controls; a future bridge
must explicitly encode or restrict these cases.

## The pointwise theorem

At source commit [`de1b30716e2b758141d5940056f37cd678464032`](https://github.com/clpi/software-is-incrementally-safe/blob/de1b30716e2b758141d5940056f37cd678464032/SoftwareIsComposable.lean), `SoftwareIsComposable.incremental_monotone` states: for every release `R` and delta `d`, if each changed symbol's updated profile is below its old profile (`profileLE (d.update s) (R.behavior s)`), then the applied release is below the old release (`releaseLE (apply R d) R`). The same statement and proof are now landed here as `SoftwareIsComposable.PointwiseModel.incremental_monotone`; the namespace keeps it separate from this repository's existing `Release` type. Here `profileLE p q` means that every observation satisfying `p` also satisfies `q`; `releaseLE` applies that relation independently at every symbol. Unchanged symbols are equal by definition of `apply`. This proves pointwise set inclusion and nothing about new observations synthesized from two components acting together.

In the audited copy, the dependency lift `reaches_monotone` transports an already-present observation along dependency reachability. The relation is transitive reachability; it does not create an observation from a joint trigger. Thus neither theorem covers emergent interaction between components that are individually within spec but whose combination emits an observation outside spec.

## Explicit premise labels

- **P-UNION-ONLY (legacy composition semantics).** The legacy profile/dependency model has local observations and dependency reachability only. Composition does not evaluate cross-component interaction rules or synthesize a new observation from a pair of component observations. This is an expressiveness limit of the model, not a theorem that real compositions cannot interact. The existing `moduleAdmission_compose` additionally requires `InteractionClosed` and the stated module admissions.
- **P-FIXED-POSITIVE-RULES (extended monotonicity).** `InteractionModel.observations_mono` is proved for a fixed `baseObs` function and fixed rule list. A rule fires when every required `(component, local observation)` pair is present. Requirements are positive: adding components cannot turn a previously fired rule off. The theorem does not cover rule deletion, negative premises, priority/override semantics, or a changing local-observation function.
- **P-ONE-SHOT-RULES (extended semantics boundary).** Interaction effects are appended once to local observations. Effects do not feed back as premises to other rules. The landed example is deliberately the smallest extension that admits a binary emergent effect; it does not claim to model recursive or arbitrary runtime interactions.
- **P-TRIGGERED-EFFECT-SAFETY (required for composed spec-safety).** To conclude all observations satisfy an allowed-output predicate, it is not enough that every component's local observations satisfy it. Every rule that fires for the composed component set must also emit an allowed effect. `InteractionModel.inSpec_of_local_and_interaction_safe` proves exactly this conditional claim. The counterexample `InteractionModel.individually_safe_components_compose_to_leak` proves that the per-component premise alone is insufficient.

## Smallest admitted interaction

The counterexample has component A emit only `ready` and component B emit only `request`. A single rule requires both `(A, ready)` and `(B, request)` and emits `leakSecret`. Each singleton satisfies the spec `observation ≠ leakSecret`; the joint set fires the rule and fails that spec. The counterexample is machine-checked in `SoftwareIsComposable/InteractionModel.lean`.

The subset-monotonicity theorem survives unchanged in shape: for fixed local observations and fixed positive rules, if `small` is a subset of `large`, every observation produced for `small` is also produced for `large`. It does **not** imply that `large` remains within an arbitrary spec: monotonicity preserves inclusion of outputs, while a spec may reject an additional output. The disposition is therefore: monotonicity **survives**; unconditional composition-of-in-spec-components **fails**; spec-safety survives only under the explicit `P-TRIGGERED-EFFECT-SAFETY` premise.
