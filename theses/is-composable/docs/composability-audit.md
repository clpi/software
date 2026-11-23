# Composability: audited statement, strengthening, and premise ledger

## Scope and provenance

The audit ticket names `clpi/software-is-composable` at
`929d8e355857b6557c1b5d1a6bd505d9bdaeea7f`. That revision contained no Lean.
The repository had subsequently advanced to `main` at
`7b1746467a410e9e5ae309f2a86bc4cd37700989` before this work. That later tree
already contained a finite behavior-retention and cost-bound admission model,
including a cross-module call counterexample. This change preserves it.

During this work, `main` also advanced to
`7a408c7b752df6f47b9cf60ddbd89d4001b5e22a`. Its pointwise compatibility module,
finite one-step interaction model, counterexample, premise document, and
additional implication/axiom reports are preserved in the integrated tree.
Their sources are checked by the same exhaustive gate. The recursive closure
theorems below do not silently reinterpret the finite model's component-list
or one-step rule semantics. In particular, the finite `Rule.requires` list
may be empty, enabling a nullary effect even with no selected components.
The binary recursive closure cannot derive anything from empty seeds. Conversely,
recursive outputs can trigger further rules, while the one-step evaluator's
outputs cannot. `Audit/OneShotBoundary.lean` keeps these distinctions as
independent standing controls. Neither model is claimed to be an unchanged
encoding of the other.

`SoftwareIsComposable/Legacy.lean` lands the audited module from
`clpi/software-is-incrementally-safe`, branch `cursor/incremental-safety-0f5e`,
at `de1b30716e2b758141d5940056f37cd678464032`, path
`SoftwareIsComposable.lean`, Git blob
`251c0824e8bc48a82bc69a640cbd54d7aff86f63`. Only the opening and closing
namespace change from `SoftwareIsComposable` to `SoftwareIsComposable.Legacy`.
The namespace avoids a collision with the subsequently landed finite `Release`.
There is no change to the copied definitions, theorem statements, or proofs.

The stable `import SoftwareIsComposable` exposes both the preserved finite
admission model and the explicitly qualified `Legacy` and `Interaction` models.
The qualified names matter: these are different contracts over different
representations. A theorem at the older audit pin is not evidence about the
newer head until the new head has been checked.

## What the audited theorem actually proves

Write `B(s)` for the set of observations a component can exhibit. In the legacy
module, `profileLE p q` is the implication `p.obs o -> q.obs o` for every `o`.
`releaseLE new old` is that inclusion at every component.

For a delta `d`, `apply R d` replaces `R(s)` by `d.update(s)` exactly where
`d.changed(s)` is true. `Legacy.incremental_monotone` says:

> If every changed component's replacement observations are a subset of its
> old observations, then every component of the updated release has a subset
> of its old observations.

The unchanged components are equal by definition. The substantive local
refinement facts are hypotheses, not results of a program analysis.
`Interaction.incremental_monotone_iff` proves the converse too: the stated
changed-component hypothesis is exactly equivalent to this pointwise release
conclusion. This exposes why the original theorem is close to definitional.
The `inspect` field does not establish that any inspection has actually run.

`Legacy.Reaches deps B s o` has only a local-observation constructor and a
dependency propagation constructor. Hence its semantics is the union of
observations at components reachable from `s`, including `s` itself.
`Legacy.reaches_monotone` lifts pointwise inclusion through that fixed graph.
`Interaction.legacy_has_origin` makes the limitation formal: every derived
observation already occurs in some component's input profile.

`Legacy.reaches_outside_stable` gives equality of reachable observations
outside the reverse dependency cone when local profiles are equal outside the
edited set. The delta composition theorems give sequential/combined update
equivalence with later writes winning. None establishes that a real compiler,
build tool, scheduler, or runtime computes those sets or dependencies correctly.

### The excluded composition phenomena

The legacy model cannot derive a fresh observation that requires two or more
components to interact when that observation is absent from every supplied
local profile. This includes, when modeled that way, shared-resource
contention, races, mutual-exclusion violations, protocol mismatch, feedback,
and a deadlock caused jointly by otherwise valid component actions.

An observation can be *named* `deadlock` in a local profile. The restriction is
that composition cannot produce that observation unless somebody has already
placed it in a reachable profile. It is a restriction of the composition
operator, not of the spelling of observation labels. In particular, it cannot
justify the universal slogan that independently in-spec components necessarily
compose into an in-spec system.

It also proves no qualified-feature retention, performance improvement,
termination, liveness, temporal safety, security noninterference, or universal
software composability. Subset refinement may delete a required behavior.
The finite model's `qualifiedMono` instead preserves old behavior labels in the
new release; its cost theorem compares supplied upper bounds, not all runs.
Those claims are preserved separately and are not silently equated.

## The smallest structural extension used here

`Interaction.Reaches deps join B s o` preserves both legacy constructors and
adds one constructor:

```
join a b c -> Reaches s a -> Reaches s b -> Reaches s c
```

The ternary relation `join` identifies which pairs may generate a new
observation. Dependencies can bring observations from different components to
the same root, where they interact. Outputs can participate in later rules,
so the relation represents arbitrary finite interaction derivations, not
only a single pair. It is a least inductive closure: cyclic rules alone cannot
generate observations without seed observations.

This is the smallest *structural* change used in the design: one new inference
constructor. The readable three-label example is not claimed to minimize the
cardinality of every possible encoding.

The standing control uses two components. The first supplies `a`, the second
supplies `b`, and `join a b alarm` is the only rule. The common allowed set is
`{a, b}`. Each component's full isolated closure is safe, because neither can
derive both premises. A dependency from the first to the second lets the first
derive `a` and `b`, then `alarm`. Neither input profile contains `alarm`.
The existing legacy model still cannot derive it. Thus the extension actually
admits the phenomenon excluded by the original operator.

## Disposition of monotonicity and safety

### Monotonicity survives

The original pointwise `Legacy.incremental_monotone` is unchanged. It never
mentioned composition. More substantially, `Interaction.reaches_monotone`
proves that the new interacting closure is monotone in its base profiles for
fixed dependencies and rules. The proof transfers each finite derivation;
the interaction case transfers both positive premises and reuses the rule.

`Interaction.reaches_refinement` is stronger: the candidate may also remove
dependency edges and interaction rules. Formally, if

```
Bnew(s) ⊆ Bold(s) for every s,
depsNew ⊆ depsOld,
joinNew ⊆ joinOld,
```

then every observation derived in the candidate is derivable in the baseline.
These inclusions are sufficient structural obligations; they are not claimed
necessary for every observationally equivalent context change.

`Interaction.reaches_simulation` weakens them further: a candidate's local
observations must have old derivations, and each candidate dependency step and
interaction rule must be simulated by the old closure. Induction derives
whole-closure inclusion from those primitive obligations. Consequently a new
shortcut rule is admissible when it expands into old derivation steps, even
if literal rule inclusion fails. `safe_of_simulation` preserves old composed
safety under these weaker obligations. The two-step shortcut control proves
this is a strict extension of the literal subset criterion. The simulation
obligations are explicit PREMISES; the proof does not discover them from code.

`Interaction.incremental_interactions_monotone` specializes this result to
the original delta operation. It therefore preserves the original release
theorem's subset direction while admitting positive emergent interactions.

### Local safety alone fails; the exact uniform condition is proved

Let `allowed` be a common observation predicate. The missing condition is
`JoinClosed join allowed`:

```
join a b c -> allowed a -> allowed b -> allowed c.
```

`safe_of_closed` derives global safety from local safety and that closure.
`universal_safety_iff_closed` proves necessity as well as sufficiency for the
statement that *every* locally safe profile assignment composes safely. It
takes an explicit root `root : σ`; this excludes the empty-component
vacuity that would make the converse false. Necessity follows by assigning
all allowed observations to that root and applying an arbitrary rule.

This is an exact uniform criterion for this model, not an assertion that any
real specification satisfies it. In the emergence control it is false.

For a particular release, universal closure is unnecessarily strong:
unreachable rules may violate it harmlessly. `safe_of_refinement` and
`safe_of_incremental` instead preserve an already proved **composed baseline**
safety result under refinement. They require no global `JoinClosed` premise.
The in-tree controls preserve this distinction.

### Incremental rechecking also survives

With fixed `deps` and `join`, `reaches_outside_stable` proves equality outside
the original reverse dependency cone. Both children of an interaction are
at the same root, so the outside-cone argument applies to each child.
`incremental_recheck_iff` proves that, from an already safe composed baseline,
checking the new closure only on the affected cone is equivalent to checking
the entire new release. This theorem does not require local subset refinement;
it permits arbitrary edits if their affected consequences are rechecked.

This is a logical equivalence over predicates. It is not a finite executable
recheck implementation or a runtime measurement. Changes to the graph or rules
require a broader affected-set argument; they are not covered by this fixed
context equality theorem.

### Where the stronger claim falls

Adding a dependency edge or an interaction rule can enable `alarm` without
changing any local profile. Consequently, local refinement alone cannot prove
global refinement across arbitrary context changes. The standing controls
exhibit both failures.

Absence-sensitive composition is different again. A fallback that produces
`alarm` when a capability is missing can add `alarm` when the capability set
shrinks. The in-tree negative-premise control proves that counterexample.
There is no unconditional monotonicity theorem for arbitrary composition
operators. A new operator must establish preservation of the chosen order,
or carry a concrete simulation argument as an explicit premise.

## Explicit premise ledger

`PREMISE` below denotes a theorem hypothesis or an unproved application
obligation; none is introduced as a Lean `axiom`.

| Label | Status and exact boundary | Evidence / consequence |
|---|---|---|
| P-LEAF-REFINEMENT | PREMISE: each changed base profile is a subset of its baseline. | Exact equivalence `incremental_monotone_iff`; no analyzer synthesizes these facts. |
| P-LEGACY-UNION | Legacy model restriction: every composed observation has a local origin. Lifted in the new model. | `legacy_has_origin`; `no_interaction_iff_legacy`; emergence control. |
| P-CONTEXT-REFINEMENT | PREMISE for structural refinement: candidate edges and rules are subsets of baseline edges and rules. Fixed context is a special case. | `reaches_refinement`; new-edge and new-rule counterexamples. |
| P-CONSTRUCTOR-SIMULATION | Weaker alternative PREMISES: candidate leaves, dependency steps and joins have simulations in the old composed closure. | `reaches_simulation`, `safe_of_simulation`; redundant shortcut-rule control strictly extends literal rule inclusion. |
| P-POSITIVE-INTERACTION | Model restriction: finite, positively witnessed interaction derivations. | Negative/absence-sensitive composition counterexample; no unconditional extension claimed. |
| P-SPEC-CLOSURE | PREMISE for the uniform local-to-global safety claim: allowed observations are closed under every join rule. | `universal_safety_iff_closed` proves this is exactly necessary on a nonempty component domain. |
| P-COMPOSED-BASELINE | Alternative PREMISE for particular-release safety preservation: the baseline composed closure is safe. | `safe_of_refinement` needs no global P-SPEC-CLOSURE; local safety alone fails. |
| P-FIXED-RECHECK-CONTEXT | PREMISE for cone equality/recheck: unchanged dependencies and interaction rules; unchanged base profiles off the declared edit set. | `reaches_outside_stable`, `incremental_recheck_iff`; changing-context cone equality is not claimed. |
| P-MODEL-ADEQUACY | OPEN application PREMISE: real observations and interactions are soundly represented by the supplied profiles, dependencies and rules. | No extraction from code, runtime trace simulation, or scheduler model is supplied here. |
| P-COOCCURRENCE-FIDELITY | OPEN application PREMISE if exact behavior equality is claimed: paired observations and rule firings correspond to compatible executions. | The abstract closure can conservatively combine alternatives; a sound overapproximation suffices for safety, exactness needs more evidence. |
| P-EXECUTABLE-BRIDGE | OPEN application PREMISE: an executable checker/CLI implements the interaction closure and its obligations. | Existing finite admission harness is unchanged; it does not certify `Interaction.Safe`. |
| P-FINITE-DECISION | OPEN application PREMISE for termination and cost of an algorithm: finite/effective state and rule representation plus verified closure evaluation. | Predicate-level theorems do not provide an algorithm or performance bound. |
| P-PROPERTY-AND-ORDER | PREMISE of scope: observation allow-list safety and subset refinement are the claims being checked. | No inference to liveness, feature retention, hyperproperties, or performance. |
| P-FINITE-MODULE-CLOSURE | Existing finite-model PREMISE: `InteractionClosed` says calls stay inside their module; cover and unique IDs also appear explicitly. | `moduleAdmission_compose`; existing cross-module counterexample retained. It is not a proof about the new join operator. |
| P-ONE-SHOT-BRIDGE | OPEN integration PREMISE if the concurrent finite `InteractionModel` evaluator is claimed to implement recursive `Interaction.Reaches`. Its effects do not feed further rules, and its requirement lists may be empty; the binary closure requires seed derivations. | `Audit/OneShotBoundary.lean` demonstrates the nullary-effect and feedback differences. A bridge must restrict or encode these explicitly; no generic evaluator/recursive-closure equivalence is asserted. |

The open application boundaries remain work orders. They are not closed by
this landing, by a successful build, or by the repository's name.

## Verification and standing controls

Run `./check.sh` on the exact commit being claimed. The gate discovers every
repository `.lean` file, recompiles it with warnings as errors, audits every
compiled safe declaration and its transitive axiom dependencies, rejects custom
axioms and proof escapes, and exercises negative gate controls. It preserves
the existing harness, example checks and mutation refusal. Only the standard
Lean foundational axioms `propext`, `Classical.choice`, and `Quot.sound` are
permitted as transitive logical foundations; these are reported explicitly.

The previous Lake DSL config generated a custom `Lake.CustomOut` axiom when
audited. It is replaced with equivalent TOML metadata so the exhaustive gate
needs no configuration-file exemption. The historical `CHECK.log` is not a
receipt for this change. Current checked source hashes, counts and controls
are in `.lake/all-files-gate/receipt.json` after a successful run, and the
committed verification document identifies the independently rechecked pin.

`Audit/InteractionControls.lean` is an independent counterexample attempt
against the new model. Its controls are compiled by the same discovery gate,
not kept in an excluded audit directory. Mathematical review and a second
fresh build at an immutable pin are separate closure requirements.
