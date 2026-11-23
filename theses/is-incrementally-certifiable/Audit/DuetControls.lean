import IncrementalCert.LegacySequence
import IncrementalCert.ReleaseSequence

set_option autoImplicit false

namespace Audit.DuetControls

open Legacy.SoftwareIsComposable
open Legacy.SoftwareIsIncrementallyCertifiable
open IncrementalCert.LegacySequence

def retained : Profile Bool := ⟨fun b => b = false⟩

def permitted (p : Profile Bool) : Prop := p = retained

def inexpensive : Admission Bool := ⟨retained, ⟨1, 1⟩⟩

def expensive : Admission Bool := ⟨retained, ⟨2, 2⟩⟩

def fixedBound : Cost := ⟨2, 2⟩

def regressing : Nat → Admission Bool
  | 0 => inexpensive
  | _ + 1 => expensive

theorem inexpensive_admitted : admits permitted fixedBound inexpensive := by
  exact ⟨c_extensive permitted retained rfl, ⟨by decide, by decide⟩⟩

theorem expensive_admitted : admits permitted fixedBound expensive := by
  exact ⟨c_extensive permitted retained rfl, ⟨by decide, by decide⟩⟩

theorem every_regressing_release_admitted :
    ∀ n, admits permitted fixedBound (regressing n) := by
  intro n
  cases n with
  | zero => exact inexpensive_admitted
  | succ n => exact expensive_admitted

theorem earlier_strictly_dominates_later :
    paretoDominates (regressing 0).cost (regressing 1).cost ∧
      ¬ paretoLE (regressing 1).cost (regressing 0).cost := by
  constructor
  · exact ⟨⟨by decide, by decide⟩, Or.inl (by decide)⟩
  · intro h
    exact (by decide : ¬ (2 ≤ 1)) h.1

theorem regression_keeps_nonempty_behavior :
    (∀ n, (regressing n).profile = retained) ∧ retained.obs false := by
  constructor
  · intro n
    cases n <;> rfl
  · rfl

theorem singleton_release_points_are_undominated :
    (∀ a : Admission Bool, a ∈ [inexpensive] →
      ¬ paretoDominates a.cost inexpensive.cost) ∧
    (∀ a : Admission Bool, a ∈ [expensive] →
      ¬ paretoDominates a.cost expensive.cost) := by
  constructor
  · intro a ha
    cases List.mem_singleton.mp ha
    exact paretoDominates_irrefl inexpensive.cost
  · intro a ha
    cases List.mem_singleton.mp ha
    exact paretoDominates_irrefl expensive.cost

theorem admission_does_not_imply_release_monotonicity :
    ¬ (∀ r : Nat → Admission Bool,
      (∀ n, admits permitted fixedBound (r n)) →
      ∀ i j, i ≤ j → paretoLE (r j).cost (r i).cost) := by
  intro h
  exact earlier_strictly_dominates_later.2
    (h regressing every_regressing_release_admitted 0 1 (by decide))

theorem regressing_edge_refused_by_repair (required : Bool → Prop) :
    ¬ GuardedStep permitted fixedBound required (regressing 0) (regressing 1) := by
  intro h
  exact earlier_strictly_dominates_later.2 h.2.1

theorem stuttering_is_admitted_and_weak_but_not_strict :
    (∀ _n : Nat, admits permitted fixedBound inexpensive) ∧
      paretoLE inexpensive.cost inexpensive.cost ∧
      ¬ paretoDominates inexpensive.cost inexpensive.cost :=
  ⟨fun _ => inexpensive_admitted, paretoLE_refl _, paretoDominates_irrefl _⟩

def complete : Profile Bool := ⟨fun _ => True⟩

def completePermitted (p : Profile Bool) : Prop := p = complete

def beforeDeletion : Admission Bool := ⟨complete, ⟨1, 1⟩⟩

def afterDeletion : Admission Bool := ⟨retained, ⟨0, 0⟩⟩

def nothing : Admission Bool := ⟨⟨fun _ => False⟩, ⟨0, 0⟩⟩

theorem before_deletion_admitted :
    admits completePermitted fixedBound beforeDeletion :=
  ⟨c_extensive completePermitted complete rfl, ⟨by decide, by decide⟩⟩

theorem behavior_deletion_is_admitted_with_strict_cost_win :
    admits completePermitted fixedBound afterDeletion ∧
      paretoDominates afterDeletion.cost beforeDeletion.cost ∧
      beforeDeletion.profile.obs true ∧ ¬ afterDeletion.profile.obs true := by
  refine ⟨?_, ?_, trivial, ?_⟩
  · exact admitted_downward before_deletion_admitted
      (fun _ _ => trivial) ⟨by decide, by decide⟩
  · exact ⟨⟨by decide, by decide⟩, Or.inl (by decide)⟩
  · intro h
    cases h

theorem behavior_deletion_violates_preservation :
    ¬ profileLE beforeDeletion.profile afterDeletion.profile := by
  intro h
  have hlost : afterDeletion.profile.obs true := h true trivial
  cases hlost

theorem empty_behavior_is_admitted_with_strict_cost_win :
    admits completePermitted fixedBound nothing ∧
      paretoDominates nothing.cost beforeDeletion.cost ∧
      (∀ o, ¬ nothing.profile.obs o) := by
  refine ⟨?_, ?_, ?_⟩
  · exact admitted_downward before_deletion_admitted
      (fun _ h => h.elim) ⟨by decide, by decide⟩
  · exact ⟨⟨by decide, by decide⟩, Or.inl (by decide)⟩
  · intro _ h
    exact h

def requiredBehavior (b : Bool) : Prop := b = true

theorem initial_required_behavior_holds :
    HoldsRequired requiredBehavior beforeDeletion := by
  intro _ _
  trivial

theorem behavior_deletion_refused_by_repair :
    ¬ GuardedStep completePermitted fixedBound requiredBehavior
      beforeDeletion afterDeletion := by
  intro h
  have hlost : afterDeletion.profile.obs true := h.2.2 true rfl trivial
  cases hlost

theorem empty_behavior_refused_by_repair :
    ¬ GuardedStep completePermitted fixedBound requiredBehavior
      beforeDeletion nothing := by
  intro h
  exact h.2.2 true rfl trivial

def sameCostDeletion : Admission Bool := ⟨retained, ⟨1, 1⟩⟩

def equalCostCycle : Nat → Admission Bool
  | 0 => beforeDeletion
  | 1 => sameCostDeletion
  | _ + 2 => beforeDeletion

theorem equal_cost_cycle_cost (n : Nat) :
    (equalCostCycle n).cost = beforeDeletion.cost := by
  cases n with
  | zero => rfl
  | succ n => cases n <;> rfl

theorem every_equal_cost_cycle_release_admitted :
    ∀ n, admits completePermitted fixedBound (equalCostCycle n) := by
  intro n
  cases n with
  | zero => exact before_deletion_admitted
  | succ n =>
    cases n with
    | zero =>
      exact admitted_downward before_deletion_admitted
        (fun _ _ => trivial) (paretoLE_refl _)
    | succ n => exact before_deletion_admitted

theorem equal_cost_cycle_is_weak_and_returns_but_is_not_strict :
    (∀ n, paretoLE (equalCostCycle (n + 1)).cost (equalCostCycle n).cost) ∧
      equalCostCycle 2 = equalCostCycle 0 ∧
      equalCostCycle 1 ≠ equalCostCycle 0 ∧
      ¬ paretoDominates (equalCostCycle 1).cost (equalCostCycle 0).cost := by
  refine ⟨?_, rfl, ?_, ?_⟩
  · intro n
    rw [equal_cost_cycle_cost, equal_cost_cycle_cost]
    exact paretoLE_refl _
  · intro h
    have hobs := congrArg (fun a : Admission Bool => a.profile.obs true) h
    have htrue : (equalCostCycle 0).profile.obs true := trivial
    have hfalse : (equalCostCycle 1).profile.obs true := Eq.mpr hobs htrue
    cases hfalse
  · rw [equal_cost_cycle_cost, equal_cost_cycle_cost]
    exact paretoDominates_irrefl _

def improvingButNotOptimal : Nat → Admission Bool
  | 0 => expensive
  | _ + 1 => inexpensive

def unseenBetter : Admission Bool := ⟨retained, ⟨0, 0⟩⟩

theorem strict_improvement_does_not_establish_global_optimality :
    (∀ n, admits permitted fixedBound (improvingButNotOptimal n)) ∧
      (∀ n, paretoLE (improvingButNotOptimal (n + 1)).cost
        (improvingButNotOptimal n).cost) ∧
      paretoDominates (improvingButNotOptimal 1).cost (improvingButNotOptimal 0).cost ∧
      admits permitted fixedBound unseenBetter ∧
      (∀ n, paretoDominates unseenBetter.cost (improvingButNotOptimal n).cost) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n
    cases n with
    | zero => exact expensive_admitted
    | succ n => exact inexpensive_admitted
  · intro n
    cases n with
    | zero => exact ⟨by decide, by decide⟩
    | succ n => exact paretoLE_refl _
  · exact ⟨⟨by decide, by decide⟩, Or.inl (by decide)⟩
  · exact ⟨c_extensive permitted retained rfl, ⟨by decide, by decide⟩⟩
  · intro n
    cases n with
    | zero => exact ⟨⟨by decide, by decide⟩, Or.inl (by decide)⟩
    | succ n =>
      change paretoDominates unseenBetter.cost inexpensive.cost
      exact ⟨⟨by decide, by decide⟩, Or.inl (by decide)⟩

namespace Canonical

open SoftwareIsQuantifiable.Interface

def space : MeasureSpace Unit := [{ measure := (), polarity := .minimize }]

def kept : SoftwareIsQuantifiable.Interface.Profile Bool Unit :=
  { symbol := false, readings := [5], observed := true }

def introduced : SoftwareIsQuantifiable.Interface.Profile Bool Unit :=
  { symbol := true, readings := [10], observed := true }

def improved : SoftwareIsQuantifiable.Interface.Profile Bool Unit :=
  { symbol := true, readings := [9], observed := true }

def behaviorDropped : SoftwareIsQuantifiable.Interface.Profile Bool Unit :=
  { symbol := false, readings := [0], observed := false }

theorem cheaper_behavior_loss_rejected_by_checker :
    IncrementalCert.ReleaseSequence.stepCheck space [behaviorDropped] [kept] = false := by
  decide

theorem strict_step_on_added_symbol_does_not_improve_initial_metrics :
    releaseLe space [kept, introduced] [kept] ∧
      releaseDominates space [kept, improved] [kept, introduced] ∧
      ¬ releaseDominates space [kept, improved] [kept] := by
  simp [releaseLe, releaseDominates, uniqueSymbols, profilesAligned, aligned,
    kept, introduced, improved, space, SoftwareIsQuantifiable.Interface.noWorse,
    measuresLe, behaviorLe, SoftwareIsQuantifiable.Interface.dominates,
    strictlyBetter, axesLe, axesLt, axisLe, axisLt]

theorem reordered_release_is_equivalent_but_not_equal :
    releaseLe space [kept, introduced] [introduced, kept] ∧
      releaseLe space [introduced, kept] [kept, introduced] ∧
      [kept, introduced] ≠ [introduced, kept] := by
  refine ⟨?_, ?_, ?_⟩
  · simp [releaseLe, uniqueSymbols, profilesAligned, aligned, kept, introduced,
      space, SoftwareIsQuantifiable.Interface.noWorse, measuresLe, behaviorLe,
      axesLe, axisLe]
  · simp [releaseLe, uniqueSymbols, profilesAligned, aligned, kept, introduced,
      space, SoftwareIsQuantifiable.Interface.noWorse, measuresLe, behaviorLe,
      axesLe, axisLe]
  · intro h
    have hp : kept = introduced := (List.cons.inj h).1
    have hs : false = true := congrArg
      (fun p : SoftwareIsQuantifiable.Interface.Profile Bool Unit => p.symbol) hp
    cases hs

theorem empty_release_checker_accepts :
    IncrementalCert.ReleaseSequence.stepCheck space
      ([] : SoftwareIsQuantifiable.Interface.Release Bool Unit) [] = true := by
  decide

def missingBefore : SoftwareIsQuantifiable.Interface.Profile Unit Unit :=
  { symbol := (), readings := [2], observed := false }

def missingAfter : SoftwareIsQuantifiable.Interface.Profile Unit Unit :=
  { symbol := (), readings := [1], observed := false }

theorem absent_behavior_can_remain_absent_after_check :
    IncrementalCert.ReleaseSequence.stepCheck space [missingAfter] [missingBefore] = true := by
  decide

theorem gained_behavior_is_strict_refinement_without_metric_dominance :
    IncrementalCert.ReleaseSequence.StrictRefinement space
      [{ symbol := (), readings := [1], observed := true }]
      [{ symbol := (), readings := [1], observed := false }] ∧
      ¬ releaseDominates space
      [{ symbol := (), readings := [1], observed := true }]
      [{ symbol := (), readings := [1], observed := false }] := by
  simp [IncrementalCert.ReleaseSequence.StrictRefinement, releaseLe,
    releaseDominates, uniqueSymbols, profilesAligned, aligned,
    SoftwareIsQuantifiable.Interface.noWorse, measuresLe, behaviorLe,
    SoftwareIsQuantifiable.Interface.dominates, strictlyBetter,
    axesLe, axesLt, axisLe, axisLt, space]

end Canonical

end Audit.DuetControls
