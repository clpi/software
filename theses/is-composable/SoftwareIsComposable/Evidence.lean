import FiniteQualification
import SoftwareIsComposable.Profile

namespace SoftwareIsComposable

def hasPrefix (pref xs : List Bool) : Bool :=
  decide (xs.take pref.length = pref)

theorem candidates_nodup_map (b : Bool) (l : List (List Bool)) (hl : l.Nodup) :
    (l.map (fun t => b :: t)).Nodup := by
  induction l with
  | nil => simp
  | cons a as ih =>
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.nodup_cons]
    constructor
    · intro hmem
      rcases List.mem_map.mp hmem with ⟨t, ht, he⟩
      injection he with _ heq
      exact hl.1 (heq ▸ ht)
    · exact ih hl.2

theorem cons_branches_disjoint (l1 l2 : List (List Bool)) (x : List Bool)
    (h1 : x ∈ l1.map (fun t => false :: t)) (h2 : x ∈ l2.map (fun t => true :: t)) : False := by
  rcases List.mem_map.mp h1 with ⟨_, _, rfl⟩
  rcases List.mem_map.mp h2 with ⟨_, _, he⟩
  injection he with hhead
  cases hhead

theorem nodup_append_disjoint {α : Type} {l1 l2 : List α}
    (h1 : l1.Nodup) (h2 : l2.Nodup) (hd : ∀ x, x ∈ l1 → x ∈ l2 → False) :
    (l1 ++ l2).Nodup := by
  induction l1 with
  | nil => simpa using h2
  | cons a as ih =>
    rw [List.nodup_cons] at h1
    rw [List.cons_append, List.nodup_cons]
    constructor
    · intro hmem
      rcases List.mem_append.mp hmem with hmem | hmem
      · exact h1.1 hmem
      · exact hd a (List.mem_cons.mpr (Or.inl rfl)) hmem
    · exact ih h1.2 fun x hx hmem => hd x (List.mem_cons.mpr (Or.inr hx)) hmem

theorem candidates_nodup : ∀ n, (FiniteQualification.candidates n).Nodup
  | 0 => by simp [FiniteQualification.candidates]
  | n + 1 => by
    rw [FiniteQualification.candidates]
    apply nodup_append_disjoint
    · exact candidates_nodup_map false _ (candidates_nodup n)
    · exact candidates_nodup_map true _ (candidates_nodup n)
    · intro x h1 h2
      exact cons_branches_disjoint _ _ x h1 h2

theorem filter_eq_singleton {α : Type} [DecidableEq α] {l : List α} {a : α}
    (hl : l.Nodup) (ha : a ∈ l) : l.filter (fun x => decide (x = a)) = [a] := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    simp [List.filter]
    cases ha with
    | head =>
      have hnin : a ∉ xs := (List.nodup_cons.mp hl).1
      have hempty : xs.filter (fun y => decide (y = a)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro y hy htrue
        exact hnin ((of_decide_eq_true htrue).symm ▸ hy)
      simp [hempty]
    | tail _ hmem =>
      have hne : x ≠ a := by
        intro heq
        exact (List.nodup_cons.mp hl).1 (heq ▸ hmem)
      simp [hne]
      exact ih (List.nodup_cons.mp hl).2 hmem

theorem determined_of_coverage (n : Nat) (cov : SymbolCoverage n) :
    ((FiniteQualification.candidates n).filter
      (fun xs => decide (xs = List.ofFn cov.observe))).length = 1 := by
  have hmem : List.ofFn cov.observe ∈ FiniteQualification.candidates n :=
    (FiniteQualification.candidates_exact n (List.ofFn cov.observe)).mpr List.length_ofFn
  rw [filter_eq_singleton (candidates_nodup n) hmem]
  simp

theorem filter_prefix_nil (n : Nat) :
    ((FiniteQualification.candidates n).filter (hasPrefix [])).length = 2 ^ n := by
  have hself : (FiniteQualification.candidates n).filter (hasPrefix []) =
      FiniteQualification.candidates n := by
    apply List.filter_eq_self.mpr
    intro xs _
    simp [hasPrefix]
  rw [hself]
  exact FiniteQualification.candidates_length n

theorem take_prefix_cons (bit : Bool) (t pref : List Bool) :
    decide ((bit :: t).take (pref.length + 1) = bit :: pref) =
      decide (t.take pref.length = pref) := by
  simp [List.take_succ_cons]

theorem filter_cons_keep (bit : Bool) (pref : List Bool) (xs : List (List Bool)) :
    ((xs.map (fun t => bit :: t)).filter (hasPrefix (bit :: pref))) =
      (xs.filter (hasPrefix pref)).map (fun t => bit :: t) := by
  induction xs with
  | nil => simp
  | cons t ts ih =>
    simp [List.map, List.filter, hasPrefix, take_prefix_cons]
    cases h : decide (t.take pref.length = pref) <;> simp [h, ih]

theorem filter_cons_drop {bit other : Bool} (hne : other ≠ bit) (pref : List Bool)
    (xs : List (List Bool)) :
    ((xs.map (fun t => other :: t)).filter (hasPrefix (bit :: pref))) = [] := by
  induction xs with
  | nil => simp
  | cons t ts ih =>
    simp [List.map, List.filter, hasPrefix, List.take_succ_cons, hne, ih]

theorem evidence_remaining (pref : List Bool) (free : Nat) :
    ((FiniteQualification.candidates (pref.length + free)).filter (hasPrefix pref)).length =
      2 ^ free := by
  induction pref generalizing free with
  | nil =>
    simpa using filter_prefix_nil free
  | cons b pref ih =>
    have hlen : (b :: pref).length + free = pref.length + free + 1 := by
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    rw [hlen, FiniteQualification.candidates, List.filter_append]
    cases b with
    | false =>
      rw [filter_cons_keep, filter_cons_drop (by decide : true ≠ false), List.length_append,
        List.length_map, List.length_nil, Nat.add_zero, ih]
    | true =>
      rw [filter_cons_drop (by decide : false ≠ true), filter_cons_keep, List.length_append,
        List.length_nil, List.length_map, Nat.zero_add, ih]

theorem not_repeated_observation_shrinks :
    let once := (FiniteQualification.candidates 2).filter (fun xs => xs.take 1 == [true])
    let twice := once.filter (fun xs => xs.take 1 == [true])
    twice.length = once.length ∧ once.length = 2 := by
  decide

theorem not_disqualification_empties :
    ((FiniteQualification.candidates 2).filter (fun xs => xs.take 1 == [false])).length = 2 := by
  decide

end SoftwareIsComposable
