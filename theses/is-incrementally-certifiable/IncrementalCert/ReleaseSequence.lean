import SoftwareIsQuantifiable.Interface

set_option autoImplicit false

namespace IncrementalCert.ReleaseSequence

open SoftwareIsQuantifiable.Interface

theorem profile_eq_of_unique {Symbol Measure : Type}
    {p q : Profile Symbol Measure} {R : Release Symbol Measure}
    (hU : uniqueSymbols R) (hp : p ∈ R) (hq : q ∈ R)
    (hs : p.symbol = q.symbol) : p = q := by
  have hP : R.Pairwise (fun a b => a.symbol ≠ b.symbol) :=
    (List.pairwise_map (R := (· ≠ ·)) (f := Profile.symbol)).mp hU
  clear hU
  induction R with
  | nil => cases hp
  | cons a rest ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hP
    cases List.mem_cons.mp hp with
    | inl heq =>
      subst p
      cases List.mem_cons.mp hq with
      | inl heq => exact heq.symm
      | inr hq => exact False.elim (hhead q hq hs)
    | inr hp =>
      cases List.mem_cons.mp hq with
      | inl heq =>
        subst q
        exact False.elim (hhead p hp hs.symm)
      | inr hq => exact ih hp hq htail

theorem no_earlier_profile_dominates {Symbol Measure : Type}
    {space : MeasureSpace Measure} {later earlier : Release Symbol Measure}
    (h : releaseLe space later earlier)
    {p q : Profile Symbol Measure} (hp : p ∈ earlier) (hq : q ∈ later) :
    ¬ dominates space p q := by
  intro hd
  obtain ⟨p', hp', hnw⟩ := h.2.2.2.2 p hp
  have heq : p' = q :=
    profile_eq_of_unique h.1 hp' hq (hnw.1.1.trans hd.1.1.1)
  subst p'
  have hpq : p = q := noWorse_antisymm hd.1 hnw
  subst p
  exact not_strictlyBetter_self space q hd.2

theorem no_earlier_release_dominates {Symbol Measure : Type}
    {space : MeasureSpace Measure} {later earlier : Release Symbol Measure}
    (h : releaseLe space later earlier) :
    ¬ releaseDominates space earlier later := by
  intro hd
  obtain ⟨q, hq, p, hp, hdom⟩ := hd.2
  exact no_earlier_profile_dominates h hp hq hdom

def Adjacent {Symbol Measure : Type} (space : MeasureSpace Measure)
    (releases : Nat → Release Symbol Measure) : Prop :=
  ∀ n, releaseLe space (releases (n + 1)) (releases n)

theorem all_pairs {Symbol Measure : Type}
    {space : MeasureSpace Measure} {releases : Nat → Release Symbol Measure}
    (h : Adjacent space releases) {i j : Nat} (hij : i ≤ j) :
    releaseLe space (releases j) (releases i) := by
  induction hij with
  | refl => exact releaseLe_refl (h i).2.1 (h i).2.2.2.1
  | @step j _ ih => exact releaseLe_trans (h j) ih

theorem adjacent_iff_all_pairs {Symbol Measure : Type}
    (space : MeasureSpace Measure) (releases : Nat → Release Symbol Measure) :
    Adjacent space releases ↔
      ∀ i j, i ≤ j → releaseLe space (releases j) (releases i) := by
  constructor
  · intro h i j hij
    exact all_pairs h hij
  · intro h n
    exact h n (n + 1) (Nat.le_succ n)

theorem no_regression {Symbol Measure : Type}
    {space : MeasureSpace Measure} {releases : Nat → Release Symbol Measure}
    (h : Adjacent space releases) {i j : Nat} (hij : i ≤ j) :
    ¬ releaseDominates space (releases i) (releases j) :=
  no_earlier_release_dominates (all_pairs h hij)

theorem observed_behavior_retained {Symbol Measure : Type}
    {space : MeasureSpace Measure} {releases : Nat → Release Symbol Measure}
    (h : Adjacent space releases) {i j : Nat} (hij : i ≤ j)
    {q : Profile Symbol Measure} (hq : q ∈ releases i) (hobs : q.observed = true) :
    ∃ p ∈ releases j, p.symbol = q.symbol ∧
      p.observed = true ∧ measuresLe space p q := by
  obtain ⟨p, hp, hnw⟩ := (all_pairs h hij).2.2.2.2 q hq
  exact ⟨p, hp, hnw.1.1, hnw.2 hobs, hnw.1⟩

def History {Symbol Measure : Type}
    (releases : Nat → Release Symbol Measure) (n : Nat) : Release Symbol Measure :=
  (List.range (n + 1)).flatMap releases

theorem latest_on_history_frontier {Symbol Measure : Type} [DecidableEq Symbol]
    {space : MeasureSpace Measure} {releases : Nat → Release Symbol Measure}
    (h : Adjacent space releases) (n : Nat)
    {p : Profile Symbol Measure} (hp : p ∈ releases n) :
    p ∈ frontier space (History releases n) := by
  apply frontier_exact.mpr
  refine ⟨?_, (h n).2.2.2.1 p hp, ?_⟩
  · exact List.mem_flatMap.mpr ⟨n, List.mem_range.mpr (Nat.lt_succ_self n), hp⟩
  · intro q hq
    obtain ⟨i, hi, hqi⟩ := List.mem_flatMap.mp hq
    have hin : i ≤ n := Nat.le_of_lt_succ (List.mem_range.mp hi)
    exact no_earlier_profile_dominates (all_pairs h hin) hqi hp

theorem frontier_covered {Symbol Measure : Type} [DecidableEq Symbol]
    {space : MeasureSpace Measure} {releases : Nat → Release Symbol Measure}
    (h : Adjacent space releases) {i j : Nat} (hij : i ≤ j)
    {q : Profile Symbol Measure} (hq : q ∈ frontier space (releases i)) :
    ∃ p ∈ frontier space (releases j), noWorse space p q := by
  obtain ⟨p, hp, hnw⟩ := (all_pairs h hij).2.2.2.2 q (frontier_exact.mp hq).1
  refine ⟨p, frontier_exact.mpr ⟨hp, (h j).2.2.2.1 p hp, ?_⟩, hnw⟩
  intro r hr
  exact no_earlier_profile_dominates (all_pairs h (Nat.le_refl j)) hr hp

def StrictRefinement {Symbol Measure : Type} (space : MeasureSpace Measure)
    (later earlier : Release Symbol Measure) : Prop :=
  releaseLe space later earlier ∧ ¬ releaseLe space earlier later

theorem metric_dominance_strict {Symbol Measure : Type}
    {space : MeasureSpace Measure} {later earlier : Release Symbol Measure}
    (h : releaseDominates space later earlier) : StrictRefinement space later earlier :=
  ⟨h.1, fun hrev => no_earlier_release_dominates hrev h⟩

theorem strict_refinement_persists {Symbol Measure : Type}
    {space : MeasureSpace Measure} {releases : Nat → Release Symbol Measure}
    (h : Adjacent space releases) {i k j : Nat}
    (hik : i ≤ k) (hkj : k + 1 ≤ j)
    (hs : StrictRefinement space (releases (k + 1)) (releases k)) :
    StrictRefinement space (releases j) (releases i) := by
  refine ⟨all_pairs h (Nat.le_trans hik (Nat.le_trans (Nat.le_succ k) hkj)), ?_⟩
  intro hreverse
  exact hs.2 (releaseLe_trans (all_pairs h hik)
    (releaseLe_trans hreverse (all_pairs h hkj)))

theorem strict_refinement_no_return {Symbol Measure : Type}
    {space : MeasureSpace Measure} {releases : Nat → Release Symbol Measure}
    (h : Adjacent space releases) {i k j : Nat}
    (hik : i ≤ k) (hkj : k + 1 ≤ j)
    (hs : StrictRefinement space (releases (k + 1)) (releases k)) :
    releases j ≠ releases i := by
  intro heq
  have hn := (strict_refinement_persists h hik hkj hs).2
  rw [heq] at hn
  exact hn (all_pairs h (Nat.le_refl i))

theorem mutually_no_worse_same_profiles {Symbol Measure : Type}
    {space : MeasureSpace Measure} {a b : Release Symbol Measure}
    (hab : releaseLe space a b) (hba : releaseLe space b a) :
    ∀ p, p ∈ a ↔ p ∈ b := by
  have forward : ∀ {x y : Release Symbol Measure},
      releaseLe space x y → releaseLe space y x →
      ∀ p, p ∈ x → p ∈ y := by
    intro x y hxy hyx p hp
    obtain ⟨q, hq, hqp⟩ := hyx.2.2.2.2 p hp
    obtain ⟨r, hr, hrq⟩ := hxy.2.2.2.2 q hq
    have hrp : r = p := profile_eq_of_unique hxy.1 hr hp (hrq.1.1.trans hqp.1.1)
    subst r
    have hqp' : q = p := noWorse_antisymm hqp hrq
    simpa [hqp'] using hq
  intro p
  exact ⟨forward hab hba p, forward hba hab p⟩

instance releaseLeDecidable {Symbol Measure : Type} [DecidableEq Symbol]
    (space : MeasureSpace Measure) (later earlier : Release Symbol Measure) :
    Decidable (releaseLe space later earlier) := by
  unfold releaseLe uniqueSymbols profilesAligned
  infer_instance

def stepCheck {Symbol Measure : Type} [DecidableEq Symbol]
    (space : MeasureSpace Measure) (later earlier : Release Symbol Measure) : Bool :=
  decide (releaseLe space later earlier)

theorem stepCheck_exact {Symbol Measure : Type} [DecidableEq Symbol]
    (space : MeasureSpace Measure) (later earlier : Release Symbol Measure) :
    stepCheck space later earlier = true ↔ releaseLe space later earlier := by
  simp [stepCheck]

theorem checked_sequence {Symbol Measure : Type} [DecidableEq Symbol]
    {space : MeasureSpace Measure} {releases : Nat → Release Symbol Measure}
    (h : ∀ n, stepCheck space (releases (n + 1)) (releases n) = true)
    {i j : Nat} (hij : i ≤ j) :
    releaseLe space (releases j) (releases i) ∧
      ¬ releaseDominates space (releases i) (releases j) := by
  have hadj : Adjacent space releases := fun n =>
    (stepCheck_exact space (releases (n + 1)) (releases n)).mp (h n)
  exact ⟨all_pairs hadj hij, no_regression hadj hij⟩

end IncrementalCert.ReleaseSequence
