import SoftwareDoesntRegress
import SoftwareIsComposable.Admission
import SoftwareIsQuantifiable.Pareto
import SoftwareIsQuantifiable.Interface

/-!
# Candidate readings of "software doesn't have to regress"

Pins: software-doesnt-have-to-regress `858a85e3`, which requires
software-is-composable `033c12c0` and software-is-quantifiable `a21c7c56`.
Everything named `SoftwareDoesntRegress.*`, `SoftwareIsComposable.*` or
`SoftwareIsQuantifiable.*` below is the family's own definition, imported, not
restated. The two readings that live only outside these pins (legacy subset
`releaseLE`, certifiable `combinedAdmission`) are restated and say where from.

Behavior tokens. Their meaning is the intent of each example and is stated
here, because no repo in the family carries a notion of a good or bad
behavior other than a supplied allow list.

* `ok`      : a required behavior that was qualified.
* `feature` : a new behavior the spec allows.
* `crash`   : a behavior the spec forbids.
* `legacy`  : a behavior that was qualified and is now deprecated.
-/

namespace RegressAudit

open SoftwareDoesntRegress

def ok : Nat := 0
def feature : Nat := 1
def crash : Nat := 2
def legacy : Nat := 3

/-! ## Reading 1. Subset: the new release shows no behavior the old one did not.

`releaseLE new old` at software-is-incrementally-safe `11278f9f`
(branch idol/full-snapshot-admission-audit, not merged; `SoftwareIsComposable.lean`
line 27), restated on finite lists. -/

def subsetLE (old new : List Nat) : Bool :=
  new.all fun b => decide (b ∈ old)

/-- Condemns an improvement: adding an allowed feature. -/
theorem r1_condemns_feature : subsetLE [ok] [ok, feature] = false := by decide

/-- Blesses a regression: deleting the required behavior. -/
theorem r1_blesses_deletion : subsetLE [ok] [] = true := by decide

/-! ## Reading 2. Superset of qualified: nothing qualified disappears.

Three family instances, all imported. -/

/-- composable `accepts` blesses a release that adds a forbidden behavior. -/
theorem r2_composable_blesses_crash :
    SoftwareIsComposable.accepts [ok] [ok, crash] = true := by decide

/-- quantifiable `acceptsRelease`, same context, equal cost, blesses the crash. -/
theorem r2_quantifiable_blesses_crash :
    SoftwareIsQuantifiable.Pareto.acceptsRelease () ()
      { qualified := [ok] } { offered := [ok, crash] } (10, 10) (10, 10) = true := by
  decide

def inc1 : Release Nat := [{ behaviors := [ok], bounds := [⟨10, 10⟩] }]
def crashed : Release Nat := [{ behaviors := [ok, crash], bounds := [⟨10, 10⟩] }]

/-- The master gate of software-doesnt-have-to-regress accepts the crash, and
counts it as the strict gain that `accepts` requires: `newBehavior` is true for
any behavior not seen before, good or bad. -/
theorem r2_head_accepts_crash_as_gain :
    accepts inc1 crashed = true ∧ strictGain inc1 crashed = true := by decide

/-- The master gate takes the incumbent's offered behaviors as the qualified
set, so a bug fix that removes an observed crash is a regression to it, even
when it also halves the cost. -/
def fixedFast : Release Nat := [{ behaviors := [ok], bounds := [⟨5, 5⟩] }]

theorem r2_head_condemns_bug_fix :
    noRegress crashed fixedFast = false ∧ accepts crashed fixedFast = false := by decide

/-- The master gate matches symbols by position, so adding a symbol is refused. -/
def withNewSymbol : Release Nat :=
  inc1 ++ [{ behaviors := [feature], bounds := [⟨1, 1⟩] }]

theorem r2_head_condemns_added_symbol :
    noRegress inc1 withNewSymbol = false ∧ accepts inc1 withNewSymbol = false := by decide

/-- and reordering two unchanged symbols is refused. -/
def two : Release Nat :=
  [{ behaviors := [ok], bounds := [⟨10, 10⟩] }, { behaviors := [feature], bounds := [⟨3, 3⟩] }]
def twoSwapped : Release Nat := two.reverse

theorem r2_head_condemns_reorder : noRegress two twoSwapped = false := by decide

/-! quantifiable `Interface.releaseLe` at this pin (`a21c7c56`) is
`∀ q ∈ incumbent, ∃ p ∈ candidate, noWorse space p q`: keyed by symbol, one
`observed` bit per symbol, added symbols unconstrained, and no uniqueness. A
candidate that ships the incumbent's profile next to a second, failing profile
for the same symbol is `releaseLe` the incumbent. Quantifiable master
(`d88acbdc`) adds `uniqueSymbols`, which refuses this; the regress pin does not
have it. -/
section Interface
open SoftwareIsQuantifiable.Interface

def sp : MeasureSpace Unit := [{ measure := (), polarity := .minimize }]

def incR : SoftwareIsQuantifiable.Interface.Release Nat Unit :=
  [{ symbol := 0, readings := [10], observed := true }]

def candDup : SoftwareIsQuantifiable.Interface.Release Nat Unit :=
  [{ symbol := 0, readings := [10], observed := true },
   { symbol := 0, readings := [1000000], observed := false },
   { symbol := 1, readings := [1000000], observed := false }]

theorem r2_interface_blesses_duplicate_and_added : releaseLe sp candDup incR := by
  intro q hq
  simp [incR] at hq
  subst hq
  refine ⟨{ symbol := 0, readings := [10], observed := true }, by simp [candDup], ?_, ?_⟩
  · exact ⟨rfl, by simp [sp, axesLe, axisLe]⟩
  · intro h
    exact h

end Interface

/-! ## Reading 3. Frontier: the candidate is not dominated by the incumbent. -/

section Frontier
open SoftwareIsQuantifiable.Pareto

/-- Blesses a hundredfold time regression bought with one unit of compute. -/
theorem r3_blesses_trade : ¬ dominates (1, 10) (100, 9) := by
  simp [dominates]

/-- Survival half: this reading never condemns a candidate that dominates. -/
theorem r3_never_condemns_dominating {inc cand : Point}
    (h : dominates cand inc) : ¬ dominates inc cand := by
  intro h'
  simp only [dominates] at h h'
  omega

end Frontier

/-! ## Reading 4. Componentwise cost no worse. -/

/-- On two axes the master gate refuses a release that doubles memory. With
only the time axis selected it accepts the same release. Which axes are
"selected" is the `AxesRight` premise, never a theorem. -/
def inc2 : Release Nat := [{ behaviors := [ok], bounds := [⟨10, 10⟩, ⟨100, 100⟩] }]
def cand2 : Release Nat := [{ behaviors := [ok], bounds := [⟨9, 9⟩, ⟨200, 200⟩] }]
def timeOnly (r : Release Nat) : Release Nat :=
  r.map fun p => { p with bounds := p.bounds.take 1 }

theorem r4_two_axes_refuse : accepts inc2 cand2 = false := by decide
theorem r4_time_axis_blesses : accepts (timeOnly inc2) (timeOnly cand2) = true := by decide

/-- Endpoint comparison (master `Bound.noWorse`) condemns a worst case that
falls from 100 to 3, because the best case rose from 1 to 2. -/
def incTail : Release Nat := [{ behaviors := [ok], bounds := [⟨1, 100⟩] }]
def candTail : Release Nat := [{ behaviors := [ok], bounds := [⟨2, 3⟩] }]

theorem r4_endpoints_condemn_tail_win : accepts incTail candTail = false := by decide

/-- Endpoint comparison blesses a slower execution. This is the repo's own
`accepted_not_per_execution`, re-checked at this pin. -/
theorem r4_endpoints_bless_slower_run :
    accepts gateInc gateCand = true ∧
      ∃ x y : Nat, 10 ≤ x ∧ x ≤ 20 ∧ 8 ≤ y ∧ y ≤ 18 ∧ x < y :=
  accepted_not_per_execution

section Separation
open SoftwareIsQuantifiable.Pareto

def bd (lo hi : Nat) (h : lo ≤ hi := by decide) : Bounds := ⟨lo, hi, h⟩

/-- Per-execution separation (quantifiable `weaklySeparated`, proved sound as
`weaklySeparated_sound`) condemns an improvement whose intervals overlap. -/
theorem r4_separation_condemns_overlap :
    ¬ weaklySeparated (bd 9 19) (bd 1 1) (bd 10 20) (bd 1 1) := by
  simp [weaklySeparated, noWorse, bd]

/-- and condemns an identical rebuild whose measurement is noisy. -/
theorem r4_separation_condemns_noisy_rebuild :
    ¬ weaklySeparated (bd 10 11) (bd 1 1) (bd 10 11) (bd 1 1) := by
  simp [weaklySeparated, noWorse, bd]

end Separation

/-! ## Reading 5. Modal: a non-regressing release process exists.

Read literally, "doesn't have to regress" is witnessed by never shipping. -/

theorem r5_never_ship_witnesses :
    ∃ pol : Release Nat → Release Nat → Release Nat,
      (∀ i c, noRegress i (pol i c) = true) ∧
        accepts baseExample betterExample = true ∧
        pol baseExample betterExample = baseExample :=
  ⟨alwaysKeep, fun i _ => noRegress_refl i, better_is_improvement, rfl⟩

/-! ## Reading 6. Spec-relative: prior qualified kept, every behavior allowed.

Shape of `IncrementalCert.combinedAdmission` at software-is-incrementally-certifiable
`3d4952bb` and of `ReleaseSafe` at software-is-incrementally-safe `32174a7c`,
restated (neither is in this pin's dependency graph). -/

def specAdmit (allowed prior new : List Nat) : Bool :=
  !prior.isEmpty && prior.all (fun b => decide (b ∈ new)) &&
    new.all (fun b => decide (b ∈ allowed))

theorem r6_refuses_crash : specAdmit [ok, feature] [ok] [ok, crash] = false := by decide
theorem r6_accepts_feature : specAdmit [ok, feature] [ok] [ok, feature] = true := by decide
theorem r6_refuses_deletion : specAdmit [ok, feature] [ok] [] = false := by decide

/-- Condemns an intended deprecation: a qualified behavior can never leave,
and the vocabulary has no retraction of a qualification. -/
theorem r6_condemns_deprecation :
    specAdmit [ok, feature, legacy] [ok, legacy] [ok, feature] = false := by decide

/-- `ReleaseSafe` flattens behaviors across symbols (`behaviorsOf`). Symbol 0
loses `ok`, symbol 1 gains it, and the flat check passes. -/
def flat (r : List (Nat × List Nat)) : List Nat := r.flatMap (·.2)

theorem r6_flat_blesses_move :
    specAdmit [ok] [ok] (flat [(0, []), (1, [ok])]) = true ∧
      specAdmit [ok] [ok] (flat [(0, [ok]), (1, [])]) = true := by decide

end RegressAudit
