import Legacy.SoftwareIsIncrementallyCertifiable

set_option autoImplicit false

namespace IncrementalCert.LegacySequence

open Legacy.SoftwareIsComposable
open Legacy.SoftwareIsIncrementallyCertifiable

theorem paretoLE_antisymm {a b : Cost}
    (hab : paretoLE a b) (hba : paretoLE b a) : a = b := by
  have ht := Nat.le_antisymm hab.1 hba.1
  have hc := Nat.le_antisymm hab.2 hba.2
  cases a
  cases b
  cases ht
  cases hc
  rfl

theorem strict_iff_no_reverse {a b : Cost} :
    paretoDominates a b ↔ paretoLE a b ∧ ¬ paretoLE b a := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro hreverse
    rcases h.2 with ht | hc
    · exact Nat.not_le_of_lt ht hreverse.1
    · exact Nat.not_le_of_lt hc hreverse.2
  · intro h
    refine ⟨h.1, ?_⟩
    cases Nat.lt_or_ge a.time b.time with
    | inl ht => exact Or.inl ht
    | inr ht =>
      cases Nat.lt_or_ge a.compute b.compute with
      | inl hc => exact Or.inr hc
      | inr hc => exact False.elim (h.2 ⟨ht, hc⟩)

theorem strict_of_le_of_strict {a b c : Cost}
    (hab : paretoLE a b) (hbc : paretoDominates b c) :
    paretoDominates a c := by
  refine ⟨paretoLE_trans hab hbc.1, ?_⟩
  rcases hbc.2 with ht | hc
  · exact Or.inl (Nat.lt_of_le_of_lt hab.1 ht)
  · exact Or.inr (Nat.lt_of_le_of_lt hab.2 hc)

theorem strict_of_strict_of_le {a b c : Cost}
    (hab : paretoDominates a b) (hbc : paretoLE b c) :
    paretoDominates a c := by
  refine ⟨paretoLE_trans hab.1 hbc, ?_⟩
  rcases hab.2 with ht | hc
  · exact Or.inl (Nat.lt_of_lt_of_le ht hbc.1)
  · exact Or.inr (Nat.lt_of_lt_of_le hc hbc.2)

theorem strict_or_eq_of_le {a b : Cost} (h : paretoLE a b) :
    paretoDominates a b ∨ a = b := by
  cases Nat.lt_or_ge a.time b.time with
  | inl ht => exact Or.inl ⟨h, Or.inl ht⟩
  | inr ht =>
    cases Nat.lt_or_ge a.compute b.compute with
    | inl hc => exact Or.inl ⟨h, Or.inr hc⟩
    | inr hc => exact Or.inr (paretoLE_antisymm h ⟨ht, hc⟩)

theorem no_reverse_dominance {later earlier : Cost}
    (hle : paretoLE later earlier) : ¬ paretoDominates earlier later := by
  intro hstrict
  exact (strict_iff_no_reverse.mp hstrict).2 hle

theorem relation_global_of_adjacent {A : Type} (rel : A → A → Prop)
    (hrefl : ∀ a, rel a a)
    (htrans : ∀ {a b c}, rel a b → rel b c → rel a c)
    (r : Nat → A) (hstep : ∀ n, rel (r (n + 1)) (r n))
    {i j : Nat} (hij : i ≤ j) : rel (r j) (r i) := by
  induction hij with
  | refl => exact hrefl (r i)
  | @step k _ ih => exact htrans (hstep k) ih

theorem cost_global_of_adjacent (r : Nat → Cost)
    (hstep : ∀ n, paretoLE (r (n + 1)) (r n))
    {i j : Nat} (hij : i ≤ j) : paretoLE (r j) (r i) :=
  relation_global_of_adjacent paretoLE paretoLE_refl
    (fun h₁ h₂ => paretoLE_trans h₁ h₂) r hstep hij

theorem cost_adjacent_iff_global (r : Nat → Cost) :
    (∀ n, paretoLE (r (n + 1)) (r n)) ↔
      ∀ i j, i ≤ j → paretoLE (r j) (r i) := by
  constructor
  · intro h i j hij
    exact cost_global_of_adjacent r h hij
  · intro h n
    exact h n (n + 1) (Nat.le_succ n)

theorem profile_global_of_adjacent {ω : Type} (r : Nat → Profile ω)
    (hstep : ∀ n, profileLE (r (n + 1)) (r n))
    {i j : Nat} (hij : i ≤ j) : profileLE (r j) (r i) :=
  relation_global_of_adjacent profileLE profileLE_refl
    (fun h₁ h₂ => profileLE_trans h₁ h₂) r hstep hij

theorem admitted_sequence {ω : Type} {safe : Profile ω → Prop} {bound : Cost}
    (r : Nat → Admission ω) (hinit : admits safe bound (r 0))
    (hprofile : ∀ n, profileLE (r (n + 1)).profile (r n).profile)
    (hcost : ∀ n, paretoLE (r (n + 1)).cost (r n).cost) :
    ∀ n, admits safe bound (r n) := by
  intro n
  induction n with
  | zero => exact hinit
  | succ n ih => exact admitted_downward ih (hprofile n) (hcost n)

theorem release_sequence {ω : Type} {safe : Profile ω → Prop} {bound : Cost}
    (r : Nat → Admission ω) (hinit : admits safe bound (r 0))
    (hprofile : ∀ n, profileLE (r (n + 1)).profile (r n).profile)
    (hcost : ∀ n, paretoLE (r (n + 1)).cost (r n).cost) :
    (∀ n, admits safe bound (r n)) ∧
      (∀ i j, i ≤ j → paretoLE (r j).cost (r i).cost) ∧
      (∀ i j, i ≤ j → ¬ paretoDominates (r i).cost (r j).cost) := by
  refine ⟨admitted_sequence r hinit hprofile hcost, ?_, ?_⟩
  · intro i j hij
    exact cost_global_of_adjacent (fun n => (r n).cost) hcost hij
  · intro i j hij
    exact no_reverse_dominance
      (cost_global_of_adjacent (fun n => (r n).cost) hcost hij)

theorem strict_interval (r : Nat → Cost)
    (hstep : ∀ n, paretoLE (r (n + 1)) (r n))
    {i k j : Nat} (hik : i ≤ k) (hkj : k < j)
    (hstrict : paretoDominates (r (k + 1)) (r k)) :
    paretoDominates (r j) (r i) :=
  strict_of_le_of_strict
    (cost_global_of_adjacent r hstep (Nat.succ_le_of_lt hkj))
    (strict_of_strict_of_le hstrict (cost_global_of_adjacent r hstep hik))

theorem strict_interval_no_return (r : Nat → Cost)
    (hstep : ∀ n, paretoLE (r (n + 1)) (r n))
    {i k j : Nat} (hik : i ≤ k) (hkj : k < j)
    (hstrict : paretoDominates (r (k + 1)) (r k)) : r j ≠ r i := by
  intro heq
  have h := strict_interval r hstep hik hkj hstrict
  rw [heq] at h
  exact paretoDominates_irrefl _ h

theorem strict_interval_has_step (r : Nat → Cost)
    (hstep : ∀ n, paretoLE (r (n + 1)) (r n))
    {i j : Nat} (hij : i ≤ j) (hstrict : paretoDominates (r j) (r i)) :
    ∃ k, i ≤ k ∧ k < j ∧ paretoDominates (r (k + 1)) (r k) := by
  induction hij with
  | refl => exact False.elim (paretoDominates_irrefl _ hstrict)
  | @step k hik ih =>
    cases strict_or_eq_of_le (hstep k) with
    | inl hs => exact ⟨k, hik, Nat.lt_succ_self k, hs⟩
    | inr heq =>
      have hs : paretoDominates (r k) (r i) := by simpa [heq] using hstrict
      obtain ⟨l, hil, hlk, hl⟩ := ih hs
      exact ⟨l, hil, Nat.lt_trans hlk (Nat.lt_succ_self k), hl⟩

theorem strict_interval_iff (r : Nat → Cost)
    (hstep : ∀ n, paretoLE (r (n + 1)) (r n))
    {i j : Nat} (hij : i ≤ j) :
    paretoDominates (r j) (r i) ↔
      ∃ k, i ≤ k ∧ k < j ∧ paretoDominates (r (k + 1)) (r k) := by
  constructor
  · exact strict_interval_has_step r hstep hij
  · rintro ⟨k, hik, hkj, hs⟩
    exact strict_interval r hstep hik hkj hs

theorem return_forces_constant_interval (r : Nat → Cost)
    (hstep : ∀ n, paretoLE (r (n + 1)) (r n))
    {i k j : Nat} (hik : i ≤ k) (hkj : k ≤ j) (hreturn : r j = r i) :
    r k = r i := by
  apply paretoLE_antisymm (cost_global_of_adjacent r hstep hik)
  rw [← hreturn]
  exact cost_global_of_adjacent r hstep hkj

def HoldsRequired {ω : Type} (required : ω → Prop) (a : Admission ω) : Prop :=
  ∀ o, required o → a.profile.obs o

def KeepsRequired {ω : Type} (required : ω → Prop)
    (earlier later : Admission ω) : Prop :=
  ∀ o, required o → earlier.profile.obs o → later.profile.obs o

theorem required_sequence {ω : Type} (required : ω → Prop) (r : Nat → Admission ω)
    (hinit : HoldsRequired required (r 0))
    (hkeep : ∀ n, KeepsRequired required (r n) (r (n + 1))) :
    ∀ n, HoldsRequired required (r n) := by
  intro n
  induction n with
  | zero => exact hinit
  | succ n ih =>
    intro o ho
    exact hkeep n o ho (ih o ho)

theorem required_adjacent_iff_global {ω : Type} (required : ω → Prop)
    (r : Nat → Admission ω) (hinit : HoldsRequired required (r 0)) :
    (∀ n, KeepsRequired required (r n) (r (n + 1))) ↔
      ∀ n, HoldsRequired required (r n) := by
  constructor
  · exact required_sequence required r hinit
  · intro h n o ho _
    exact h (n + 1) o ho

theorem certified_required_sequence {ω : Type} {safe : Profile ω → Prop}
    {bound : Cost} (required : ω → Prop) (r : Nat → Admission ω)
    (hinit : admits safe bound (r 0))
    (hprofile : ∀ n, profileLE (r (n + 1)).profile (r n).profile)
    (hcost : ∀ n, paretoLE (r (n + 1)).cost (r n).cost)
    (hrequired : HoldsRequired required (r 0))
    (hkeep : ∀ n, KeepsRequired required (r n) (r (n + 1))) :
    (∀ n, admits safe bound (r n) ∧ HoldsRequired required (r n)) ∧
      (∀ i j, i ≤ j → paretoLE (r j).cost (r i).cost) ∧
      (∀ i j, i ≤ j → ¬ paretoDominates (r i).cost (r j).cost) := by
  obtain ⟨hadmitted, hle, hnoreverse⟩ := release_sequence r hinit hprofile hcost
  exact ⟨fun n => ⟨hadmitted n, required_sequence required r hrequired hkeep n⟩,
    hle, hnoreverse⟩

def GuardedStep {ω : Type} (safe : Profile ω → Prop) (bound : Cost)
    (required : ω → Prop) (earlier later : Admission ω) : Prop :=
  admits safe bound later ∧ paretoLE later.cost earlier.cost ∧
    KeepsRequired required earlier later

theorem rechecked_sequence {ω : Type} {safe : Profile ω → Prop} {bound : Cost}
    (required : ω → Prop) (r : Nat → Admission ω)
    (hadmitted : ∀ n, admits safe bound (r n))
    (hcost : ∀ n, paretoLE (r (n + 1)).cost (r n).cost)
    (hrequired : HoldsRequired required (r 0))
    (hkeep : ∀ n, KeepsRequired required (r n) (r (n + 1))) :
    (∀ n, admits safe bound (r n) ∧ HoldsRequired required (r n)) ∧
      (∀ i j, i ≤ j → paretoLE (r j).cost (r i).cost) ∧
      (∀ i j, i ≤ j → ¬ paretoDominates (r i).cost (r j).cost) := by
  refine ⟨fun n => ⟨hadmitted n, required_sequence required r hrequired hkeep n⟩, ?_, ?_⟩
  · intro i j hij
    exact cost_global_of_adjacent (fun n => (r n).cost) hcost hij
  · intro i j hij
    exact no_reverse_dominance
      (cost_global_of_adjacent (fun n => (r n).cost) hcost hij)

theorem guarded_sequence {ω : Type} {safe : Profile ω → Prop} {bound : Cost}
    (required : ω → Prop) (r : Nat → Admission ω)
    (hinit : admits safe bound (r 0)) (hrequired : HoldsRequired required (r 0))
    (hstep : ∀ n, GuardedStep safe bound required (r n) (r (n + 1))) :
    (∀ n, admits safe bound (r n) ∧ HoldsRequired required (r n)) ∧
      (∀ i j, i ≤ j → paretoLE (r j).cost (r i).cost) ∧
      (∀ i j, i ≤ j → ¬ paretoDominates (r i).cost (r j).cost) := by
  apply rechecked_sequence required r ?_ (fun n => (hstep n).2.1) hrequired
    (fun n => (hstep n).2.2)
  intro n
  cases n with
  | zero => exact hinit
  | succ n => exact (hstep n).1

theorem empty_profile_refused {ω : Type} {required : ω → Prop}
    {a : Admission ω} (hne : ∃ o, required o)
    (hempty : ∀ o, ¬ a.profile.obs o) : ¬ HoldsRequired required a := by
  intro h
  obtain ⟨o, ho⟩ := hne
  exact hempty o (h o ho)

end IncrementalCert.LegacySequence
