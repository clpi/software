# Independent counterexample review: positive interactions

## Review boundary

This review was performed independently of the author of
`SoftwareIsComposable/Interaction.lean`. It checked the statements and attempted
counterexamples before the candidate was committed. The immutable-pin recheck
and complete repository gate are recorded separately in the landing receipt.

Reviewed source SHA-256:

- `SoftwareIsComposable/Interaction.lean`:
  `c531fa1f7749cbc7616c73c8b4ee79b5a8e2727f6f05a12582faa841e6809b06`
- `Audit/InteractionControls.lean`:
  `f83d4fc80cb3126d36d65b3f7b3813054da9787cbb0817290fb897e816cd768b`

The reviewer rebuilt `Legacy.lean`, `Interaction.lean`, and
`Audit/InteractionControls.lean` into a fresh output directory using Lean
4.19.0 and `-DwarningAsError=true`. Compilation exited 0. The control module
contains 24 theorem declarations; each control's `#print axioms` result is
`does not depend on any axioms`.

This is a check of the model and its stated hypotheses. It is not evidence that
an arbitrary real program's interactions have been faithfully extracted.

## Attack 1: two safe components compose into an unsafe system

Use two component identities, `false` and `true`, and three observation labels,
`a`, `b`, and `alarm`. Component `false` supplies only `a`; component `true`
supplies only `b`. The allowed set contains `a` and `b`, but not `alarm`.
The interaction relation has one rule:

```
a and b together produce alarm
```

With no dependency edges, each component's entire interaction closure is safe:
no component can obtain both inputs. Adding the single dependency edge
`false -> true` lets the first component obtain `b` as well as its own `a`.
The positive interaction rule then derives `alarm`.

This control establishes more than safe seed profiles: both isolated
components' **derived closures** are safe. The observation `alarm` is absent
from every component's seed profile, and the original legacy model cannot
derive it even with the composition edge. The new model can.

Standing controls:

- `isolated_has_only_own_observation`
- `isolated_components_are_safe`
- `seed_profiles_are_safe`
- `composed_alarm`
- `composition_of_isolated_safe_components_is_unsafe`
- `alarm_has_no_component_origin`
- `legacy_composition_cannot_derive_alarm`

**Disposition:** the previous implication from local safety to composed safety
is false in the strengthened model. `safe_of_closed` correctly adds the
interaction-closure obligation. `allowed_is_not_interaction_closed` proves why
that obligation fails for this example.

The example is a small illustrative instance. The architectural change is one
new binary derivation constructor; no claim of minimum observation cardinality
is made.

## Attack 2: unchanged local profiles, changed composition context

Keep the two seed profiles exactly equal. Either add the dependency edge above,
or retain that edge and add the previously absent interaction rule. In each
case a new composed observation appears despite reflexive local inclusion.

Standing controls:

- `topology_change_breaks_global_refinement`
- `rule_change_breaks_global_refinement`

**Disposition:** arbitrary context changes do break global monotonicity. The
landed `reaches_refinement` theorem requires new dependencies and new interaction
rules to be subsets of the old ones. Its fixed-context corollary therefore
survives this attack. These hypotheses must remain visible when applying the
theorem; a local-profile proof alone does not discharge them.

Rule inclusion is a sufficient syntactic condition. It is not necessary. The
stronger `reaches_simulation` theorem now allows each new leaf, dependency step,
and interaction rule to be simulated in the old derived closure.
`safe_of_simulation` carries a safe baseline through that simulation. These
constructor obligations are explicit sufficient proof obligations, not an
unconditional claim that context extension is safe.

The reviewer tested that strengthening using old rules `a,a -> b` and
`b,b -> alarm`, then adding a shortcut `a,a -> alarm`. The shortcut is **not** an
old rule, but two old derivation steps simulate it. The new and old closures are
proved equivalent for every dependency graph, every seed profile, and every
root. A concrete reachable shortcut witness prevents this from being a vacuous
empty-input test.

Standing controls:

- `shortcut_is_not_rule_subset`
- `shortcut_primitive_simulated`
- `shortcut_extension_preserves_closure`
- `shortcut_has_live_witness`

The attempted counterexample to simulation changes the primitive obligation:
add the harmful `a,b -> alarm` rule to a model with no old rules. Both leaf and
dependency-step simulation still hold, but join simulation fails on the old
reachable witnesses `a` and `b`. The earlier emergent-alarm control already
shows the resulting failure of full transfer.
`primitive_join_obligation_is_load_bearing` proves this exact separation.

**Disposition:** constructor simulation is strictly more permissive than
literal rule inclusion, and the harmful extension does not satisfy its
hypotheses. No counterexample was found to the simulation theorem as stated.

## Attack 3: shrinking behavior enables an absence-sensitive fallback

Let the old profile contain `b` and the new profile be empty, so the new profile
is a strict subset of the old one. Define a composition observation by:

```
output o if the profile contains o,
or output alarm if the profile does not contain b
```

The old composition cannot produce `alarm`; the new composition does. The
absence test reverses the effect of deleting the old observation.

Standing control: `absence_sensitive_refinement_fails`.

**Disposition:** positive interaction refinement does not extend unchanged to
negative premises, absence-sensitive fallback, priority, or cancellation.
These require their own semantic order or simulation hypotheses. The new
`Reaches.interact` constructor accepts only positive derivation witnesses, so
it does not silently claim this broader result.

## Attack 4: closure is sufficient, but is it necessary?

For an individual baseline release, interaction closure of the entire allowed
set can be unnecessarily strong. A dangerous pair of allowed observations might
never be reachable together in that release. A baseline with no observations is
an immediate example.

**Disposition:** `safe_of_refinement` and `safe_of_incremental` correctly use
already-established composed safety of the old baseline and do not require
universal allowed-set closure. The stronger `universal_safety_iff_closed` speaks
about **every locally safe choice of seed profiles**. In that universal problem,
one may choose every allowed observation as a seed at the supplied root, making
the closure condition necessary as well as sufficient.

A separate counterexample targets an empty component type. Universal safety is
then vacuous even if the allowed set is not interaction-closed. Standing control:
`no_root_makes_universal_safety_vacuous`.

**Disposition:** the theorem's explicit `root : sigma` hypothesis blocks this
counterexample. Omitting that witness or an equivalent nonemptiness hypothesis
would make the claimed equivalence false.

## Attack 5: positive cyclic interactions manufacture evidence

Try a rule `alarm and alarm produce alarm` with no observations supplied by any
component. A cyclic interpretation might incorrectly treat its own conclusion
as evidence.

Standing controls:

- `empty_seeds_do_not_bootstrap`
- `positive_cycle_cannot_self_justify`

**Disposition:** the inductive `Reaches` relation admits only finite, grounded
derivations. Induction shows no observation can be derived from empty seeds,
regardless of dependency cycles or positive rule cycles. The attack fails.

The non-bootstrap result is mathematical. It does not establish termination or
complexity bounds for a future executable closure engine.

## Attack 6: does the positive monotonicity proof merely restate its conclusion?

The hypothesis bounds only raw component observations, dependencies, and rules;
it does not assume inclusion of composed observations. The proof transports each
finite derivation. A leaf uses raw observation inclusion; a dependency step uses
edge inclusion; an interaction step reuses both transported premises and the
included rule.

Standing controls `strict_local_refinement` and
`positive_interaction_refinement_survives` check the direction of the order in a
concrete instance. That instance retains `a` at the first component and removes
`b` from the second. `positive_refinement_has_live_observation` proves the new
closure still contains `a`; `shrunk_closure_has_only_a` and
`positive_refinement_removes_alarm` show it no longer derives the alarm. This
positive control has a nonempty new closure. The general theorem's derivation
induction supplies the full composed conclusion.

**Disposition:** the composed monotonicity theorem survives for positive rules.
The legacy `incremental_monotone` remains a pointwise set-inclusion result; the
new `incremental_monotone_iff` makes its near-definitional nature explicit.
Neither theorem establishes preservation of required behaviors under deletion,
strict performance improvement, or Pareto optimality.

## Attack 7: what remains outside the proof?

The original model can contain an observation named `deadlock` or `race` if a
caller supplies it in a seed profile. Its limitation is more precise: it cannot
derive such a new observation from jointly compatible local observations unless
that observation was already supplied somewhere reachable.

The added rule removes that limitation for positive finite interaction trees.
It does not prove that a real program's possible executions, environmental
assumptions, scheduling, or joint realizability are represented correctly.
Combining separately possible observations can overapproximate reality if they
cannot coexist in one execution. A faithful `join` relation must encode that
compatibility, or the model must be explicitly used as a conservative safety
approximation.

The existing executable finite admission checker and its `InteractionClosed`
no-cross-module-call condition are separate from this new predicate model.
The new semantic module does not itself extract interaction rules, compute a
finite closure, or make the existing command-line checker interaction-aware.
Those bridges remain explicit integration and adequacy obligations.

## Review conclusion

No counterexample was found to the 16 statements as written in the reviewed
`Interaction.lean`. The attacks produce permanent controls for claims that would
be false if closure, positivity, context preservation, groundedness, or the
root witness were omitted. The surviving conclusion is scoped: refinement of
raw profiles under a fixed positive interaction semantics preserves inclusion
of derived observations. More generally, changes to leaves, dependencies, and
rules are allowed when their primitive inference obligations are simulated in
the old closure. Safe composition additionally needs interaction closure or a
previously safe composed baseline.
