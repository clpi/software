import CanonicalDominance
import IncrementalCert.Check

namespace IncrementalCert

open SoftwareIsQuantifiable.Interface

def selectedSpace : MeasureSpace Nat :=
  [{ measure := 0, polarity := .minimize }, { measure := 1, polarity := .minimize }]

inductive StepAdmitted : List Optimality.Point → Prop where
  | single (p : Optimality.Point) : StepAdmitted [p]
  | cons {r s : Optimality.Point} {rest : List Optimality.Point}
      (h : releaseLe SoftwareIsQuantifiable.Pareto.costSpace
        [SoftwareIsQuantifiable.Pareto.profileOf r]
        [SoftwareIsQuantifiable.Pareto.profileOf s])
      (t : StepAdmitted (s :: rest)) :
      StepAdmitted (r :: s :: rest)

def NothingOutside (catalogue ps : List Optimality.Point) : Prop :=
  (∀ p, p ∈ ps → p ∈ catalogue) ∧ (∀ p, p ∈ catalogue → p ∈ ps)

abbrev NoCoverageGaps {α : Type} (candidates : List α) (intended : α → Prop) : Prop :=
  Optimality.GeneratorCoverage candidates intended

theorem not_optimality_dominates_self (p : Optimality.Point) :
    ¬ Optimality.dominates p p := by
  intro h
  rcases h.2.2 with hlt | hlt
  · exact Nat.lt_irrefl _ hlt
  · exact Nat.lt_irrefl _ hlt

theorem not_point_dominates {later earlier : Optimality.Point}
    (h : releaseLe SoftwareIsQuantifiable.Pareto.costSpace
      [SoftwareIsQuantifiable.Pareto.profileOf later]
      [SoftwareIsQuantifiable.Pareto.profileOf earlier]) :
    ¬ Optimality.dominates earlier later := by
  intro hd
  have hcan :=
    (CanonicalDominance.Optimality.local_dominates_iff_canonical earlier later).mp hd
  obtain ⟨p, hp, hnw⟩ :=
    h.2.2.2.2 (SoftwareIsQuantifiable.Pareto.profileOf earlier) (by simp)
  simp only [List.mem_singleton] at hp
  subst p
  have heq := noWorse_antisymm hcan.1 hnw
  have hstrict := hcan.2
  rw [heq] at hstrict
  exact not_strictlyBetter_self _ _ hstrict

theorem eq_of_pairwise {a b : Profile Nat Nat} :
    ∀ {R : List (Profile Nat Nat)},
      R.Pairwise (fun x y => x.symbol ≠ y.symbol) →
      a ∈ R → b ∈ R → a.symbol = b.symbol → a = b
  | [], _, ha, _, _ => nomatch ha
  | _ :: _, hp, ha, hb, hs => by
    rw [List.pairwise_cons] at hp
    cases List.mem_cons.mp ha with
    | inl hxa =>
      cases hxa
      cases List.mem_cons.mp hb with
      | inl hxb => exact hxb.symm
      | inr hxb => exact absurd hs (hp.1 b hxb)
    | inr hxa =>
      cases List.mem_cons.mp hb with
      | inl hxb =>
        cases hxb
        exact absurd hs.symm (hp.1 a hxa)
      | inr hxb =>
        exact eq_of_pairwise hp.2 hxa hxb hs

theorem eq_of_uniqueSymbols {a b : Profile Nat Nat} {R : Release Nat Nat}
    (hu : uniqueSymbols R) (ha : a ∈ R) (hb : b ∈ R) (hs : a.symbol = b.symbol) : a = b :=
  eq_of_pairwise ((List.pairwise_map (R := (· ≠ ·)) (f := Profile.symbol)).1 hu) ha hb hs

theorem not_earlier_dominates {later earlier : Release Nat Nat}
    (h : releaseLe selectedSpace later earlier) :
    ¬ releaseDominates selectedSpace earlier later := by
  intro hd
  obtain ⟨q, hq, p, hp, hdom⟩ := hd.2
  obtain ⟨p', hp', hnw⟩ := h.2.2.2.2 p hp
  have hs : p'.symbol = q.symbol := hnw.1.1.trans hdom.1.1.1
  have hpq : p' = q := eq_of_uniqueSymbols h.1 hp' hq hs
  have hqp : noWorse selectedSpace q p := by simpa [hpq] using hnw
  have heq : p = q := noWorse_antisymm hdom.1 hqp
  have hstrict : strictlyBetter selectedSpace p q := hdom.2
  rw [heq] at hstrict
  exact not_strictlyBetter_self selectedSpace q hstrict

theorem pareto_monotone_chain
    {catalogue : List Optimality.Point} {intended : Optimality.Point → Prop}
    {a b c : Optimality.Point} {prev : Prev}
    (h : StepAdmitted [c, b, a])
    (hReq : RequiredNonempty prev)
    (hSrc : requiredOf prev = (priorOf prev).qualified)
    (h05 : NothingOutside catalogue [c, b, a])
    (h06 : NoCoverageGaps catalogue intended) :
    ¬ Optimality.dominates a c ∧
      ¬ Optimality.dominates b c ∧
      ¬ Optimality.dominates a b ∧
      (Optimality.dominates a c ↔
        SoftwareIsQuantifiable.Interface.dominates
          SoftwareIsQuantifiable.Pareto.costSpace
          (SoftwareIsQuantifiable.Pareto.profileOf a)
          (SoftwareIsQuantifiable.Pareto.profileOf c)) ∧
      c ∈ Optimality.paretoMaximal catalogue ∧
      (∀ y, intended y → ¬ Optimality.dominates y c) ∧
      requiredOf prev ≠ [] ∧
      requiredOf prev = (priorOf prev).qualified := by
  cases h with
  | cons hcb rest =>
    cases rest with
    | cons hab tail =>
      cases tail
      have hca := releaseLe_trans hcb hab
      have hnac := not_point_dominates hca
      have hnbc := not_point_dominates hcb
      have hnab := not_point_dominates hab
      have hiff := CanonicalDominance.Optimality.local_dominates_iff_canonical a c
      have hfront : c ∈ Optimality.paretoMaximal catalogue := by
        rw [Optimality.paretoMaximal_exact]
        refine ⟨h05.1 c (by simp), ?_⟩
        intro y hy hd
        have hyps : y ∈ [c, b, a] := h05.2 y hy
        cases List.mem_cons.mp hyps with
        | inl hyc =>
          cases hyc
          exact not_optimality_dominates_self c hd
        | inr hrest =>
          cases List.mem_cons.mp hrest with
          | inl hyb =>
            cases hyb
            exact hnbc hd
          | inr hlast =>
            cases List.mem_singleton.mp hlast
            exact hnac hd
      have hcov : ∀ y, intended y → ¬ Optimality.dominates y c := by
        intro y hy hd
        have hym : y ∈ catalogue := h06.complete y hy
        have hyps : y ∈ [c, b, a] := h05.2 y hym
        cases List.mem_cons.mp hyps with
        | inl hyc =>
          cases hyc
          exact not_optimality_dominates_self c hd
        | inr hrest =>
          cases List.mem_cons.mp hrest with
          | inl hyb =>
            cases hyb
            exact hnbc hd
          | inr hlast =>
            cases List.mem_singleton.mp hlast
            exact hnac hd
      exact ⟨hnac, hnbc, hnab, hiff, hfront, hcov, hReq.nonempty, hSrc⟩

def oneAxis : MeasureSpace Nat :=
  [{ measure := 0, polarity := .minimize }]

theorem axes_change_hides_regression :
    let later : Release Nat Nat := [{ symbol := 0, readings := [9, 100], observed := true }]
    let earlier : Release Nat Nat := [{ symbol := 0, readings := [10, 1], observed := true }]
    let later1 : Release Nat Nat := [{ symbol := 0, readings := [9], observed := true }]
    let earlier1 : Release Nat Nat := [{ symbol := 0, readings := [10], observed := true }]
    ¬ releaseLe selectedSpace later earlier ∧ releaseLe oneAxis later1 earlier1 := by
  refine ⟨?_, ?_⟩
  · intro h
    obtain ⟨p, hp, hnw⟩ :=
      h.2.2.2.2 { symbol := 0, readings := [10, 1], observed := true } (by simp)
    simp at hp
    subst hp
    obtain ⟨_, hrest⟩ := hnw.1.2
    simp [axesLe, axisLe] at hrest
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · unfold uniqueSymbols
      simp
    · unfold uniqueSymbols
      simp
    · intro p hp
      simp at hp
      subst hp
      rfl
    · intro p hp
      simp at hp
      subst hp
      rfl
    · intro q hq
      simp at hq
      subst hq
      refine ⟨{ symbol := 0, readings := [9], observed := true }, by simp, ?_⟩
      refine ⟨⟨rfl, by decide⟩, ?_⟩
      intro hobs
      rfl

theorem not_per_execution :
    ¬ ∀ x y : Nat × Nat,
      (1 ≤ x.1 ∧ x.1 ≤ 100 ∧ x.2 = 0) →
      (2 ≤ y.1 ∧ y.1 ≤ 3 ∧ y.2 = 0) →
      y.1 < x.1 :=
  SoftwareIsQuantifiable.Pareto.not_per_execution_dominance

theorem outside_dominates :
    let catalogue : List Optimality.Point := [(2, 2)]
    let outside : Optimality.Point := (0, 0)
    ¬ NothingOutside catalogue [outside, (2, 2)] ∧
      (2, 2) ∈ Optimality.paretoMaximal catalogue ∧
      Optimality.dominates outside (2, 2) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hmem := h.1 (0, 0) (by simp)
    simp at hmem
  · decide
  · decide

theorem coverage_gap_dominates :
    let catalogue : List Optimality.Point := [(1, 1)]
    let intended : Optimality.Point → Prop := fun p => p = (1, 1) ∨ p = (0, 0)
    ¬ NoCoverageGaps catalogue intended ∧
      (1, 1) ∈ Optimality.paretoMaximal catalogue ∧
      Optimality.dominates (0, 0) (1, 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hmem := h.complete (0, 0) (Or.inr rfl)
    simp at hmem
  · decide
  · decide

end IncrementalCert
