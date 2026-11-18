import SoftwareIsQuantifiable.Interface
import SoftwareIsQuantifiable.Pareto

namespace IncrementalCert

open SoftwareIsQuantifiable.Interface

def selectedSpace : MeasureSpace Nat :=
  [{ measure := 0, polarity := .minimize }, { measure := 1, polarity := .minimize }]

def FixedSelectedAxes (chain : List (Release Nat Nat)) : Prop :=
  ∀ r ∈ chain, profilesAligned selectedSpace r ∧ ∀ p ∈ r, p.symbol = 0

def ValidMeasurements (chain : List (Release Nat Nat)) : Prop :=
  ∀ r ∈ chain, uniqueSymbols r

def BaselineEligible (base : Release Nat Nat) : Prop :=
  base ≠ [] ∧ profilesAligned selectedSpace base

inductive StepAdmitted : List (Release Nat Nat) → Prop where
  | single (r : Release Nat Nat) : StepAdmitted [r]
  | cons {r s : Release Nat Nat} {rest : List (Release Nat Nat)}
      (h : releaseLe selectedSpace r s) (t : StepAdmitted (s :: rest)) :
      StepAdmitted (r :: s :: rest)

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

theorem pareto_monotone_chain {a b c : Release Nat Nat}
    (h : StepAdmitted [c, b, a])
    (hA : FixedSelectedAxes [c, b, a])
    (hV : ValidMeasurements [c, b, a])
    (hB : BaselineEligible a) :
    ¬ releaseDominates selectedSpace a b ∧
      ¬ releaseDominates selectedSpace b c ∧
      ¬ releaseDominates selectedSpace a c ∧
      (∀ p ∈ a, aligned selectedSpace p ∧ p.symbol = 0) ∧
      a ≠ [] ∧ uniqueSymbols b := by
  cases h with
  | cons hcb rest =>
    cases rest with
    | cons hab tail =>
      cases tail
      have hca := releaseLe_trans hcb hab
      have hAa := hA a (by simp)
      have hshape : ∀ p ∈ a, aligned selectedSpace p ∧ p.symbol = 0 := by
        intro p hp
        exact ⟨hAa.1 p hp, hAa.2 p hp⟩
      exact ⟨not_earlier_dominates hab, not_earlier_dominates hcb,
        not_earlier_dominates hca, hshape, hB.1, hV b (by simp)⟩

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

end IncrementalCert
