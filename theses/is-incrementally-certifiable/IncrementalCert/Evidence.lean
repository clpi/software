set_option autoImplicit false

namespace IncrementalCert

def pow2 : Nat → Nat
  | 0 => 1
  | n + 1 => pow2 n * 2

def allVecs : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 =>
    let tail := allVecs n
    tail.map (fun v => v ++ [false]) ++ tail.map (fun v => v ++ [true])

def agrees (v : List Bool) : List (Nat × Bool) → Bool
  | [] => true
  | (i, b) :: ps => ((v.getD i (!b)) == b) && agrees v ps

def isHigh (n : Nat) (p : Nat × Bool) : Bool :=
  decide (p.1 = n)

def isLow (n : Nat) (p : Nat × Bool) : Bool :=
  !isHigh n p

def consistentLength (n : Nat) (fix : List (Nat × Bool)) : Nat :=
  ((allVecs n).filter (fun v => agrees v fix)).length

structure IndependencePremise (n : Nat) (fix : List (Nat × Bool)) : Prop where
  distinct : List.Pairwise (fun a b : Nat × Bool => a.1 ≠ b.1) fix
  inRange : ∀ p, p ∈ fix → p.1 < n

structure CoveragePremise (n : Nat) (fix : List (Nat × Bool)) : Prop where
  mediated : ∀ i, i < n → ∃ b, (i, b) ∈ fix

theorem pow2_add (a b : Nat) : pow2 (a + b) = pow2 a * pow2 b := by
  induction a with
  | zero => simp [pow2]
  | succ a ih =>
    calc
      pow2 (a + 1 + b) = pow2 (a + b + 1) := by rw [Nat.add_right_comm]
      _ = pow2 (a + b) * 2 := by simp [pow2]
      _ = (pow2 a * pow2 b) * 2 := by rw [ih]
      _ = (pow2 a * 2) * pow2 b := by
        rw [Nat.mul_assoc, Nat.mul_comm (pow2 b) 2, ← Nat.mul_assoc]
      _ = pow2 (a + 1) * pow2 b := by simp [pow2]

theorem pow2_ge_one : ∀ k : Nat, 1 ≤ pow2 k
  | 0 => by simp [pow2]
  | k + 1 => by
    have ih := pow2_ge_one k
    simp [pow2]
    omega

theorem pow2_at_least_two {k : Nat} (hk : 1 ≤ k) : 2 ≤ pow2 k := by
  cases k with
  | zero => cases hk
  | succ k =>
    have := pow2_ge_one k
    simp [pow2]
    omega

theorem allVecs_succ (n : Nat) :
    allVecs (n + 1) =
      (allVecs n).map (fun v => v ++ [false]) ++
        (allVecs n).map (fun v => v ++ [true]) := rfl

theorem allVecs_card : ∀ n : Nat, (allVecs n).length = pow2 n
  | 0 => rfl
  | n + 1 => by
    rw [allVecs_succ, List.length_append, List.length_map, List.length_map, allVecs_card n, pow2]
    omega

theorem allVecs_vec_length : ∀ n : Nat, ∀ v ∈ allVecs n, v.length = n
  | 0, v, hv => by
    simp [allVecs] at hv
    subst hv
    rfl
  | n + 1, v, hv => by
    simp [allVecs_succ, List.mem_append, List.mem_map] at hv
    rcases hv with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
    · simp [allVecs_vec_length n t ht]
    · simp [allVecs_vec_length n t ht]

theorem getD_append_low {v : List Bool} {b : Bool} {i : Nat} {d : Bool}
    (hi : i < v.length) : (v ++ [b]).getD i d = v.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_append_last {v : List Bool} {b d : Bool} :
    (v ++ [b]).getD v.length d = b := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _)]

theorem and_rot (x y z : Bool) : (x && (y && z)) = ((x && y) && z) := by
  cases x <;> cases y <;> cases z <;> rfl

theorem and_comm_mid (x y z : Bool) : (x && (y && z)) = (y && (x && z)) := by
  cases x <;> cases y <;> cases z <;> rfl

theorem and_true (x : Bool) : (x && true) = x := by
  cases x <;> rfl

theorem and_false (x : Bool) : (x && false) = false := by
  cases x <;> rfl

theorem not_true_iff (a : Bool) : ((!a) = true) ↔ a = false := by
  cases a <;> simp

theorem filter_partition_length {α : Type} (p : α → Bool) :
    ∀ l : List α, (l.filter p).length + (l.filter (fun a => !p a)).length = l.length
  | [] => rfl
  | a :: as => by
    have ih := filter_partition_length p as
    cases h : p a
    · simp [List.filter, h, ih]
      omega
    · simp [List.filter, h, ih]
      omega

theorem agrees_split (v : List Bool) (c : Bool) :
    ∀ fix : List (Nat × Bool),
      (∀ p, p ∈ fix → p.1 < v.length + 1) →
        (agrees (v ++ [c]) fix) =
          ((agrees v (fix.filter (isLow v.length))) &&
            ((fix.filter (isHigh v.length)).all (fun p => c == p.2)))
  | [], _ => by simp [agrees]
  | (i, b) :: ps, hf => by
    have hi : i < v.length + 1 := hf (i, b) (List.mem_cons_self (l := ps))
    have hps : ∀ q, q ∈ ps → q.1 < v.length + 1 := by
      intro q hq
      exact hf q (List.mem_cons_of_mem _ hq)
    have ih := agrees_split v c ps hps
    by_cases hlt : i < v.length
    · have hne : i ≠ v.length := Nat.ne_of_lt hlt
      have hdecide : decide (i = v.length) = false := by
        rw [decide_eq_false_iff_not]
        exact hne
      have hlow : isLow v.length (i, b) = true := by
        unfold isLow isHigh
        change (!decide (i = v.length)) = true
        rw [hdecide]
        rfl
      have hhigh : isHigh v.length (i, b) = false := by
        unfold isHigh
        change decide (i = v.length) = false
        exact hdecide
      have hneg : ¬ isHigh v.length (i, b) := by
        rw [hhigh]
        decide
      rw [agrees, getD_append_low hlt, ih]
      rw [List.filter_cons_of_pos (p := isLow v.length) (a := (i, b)) (l := ps) hlow]
      rw [List.filter_cons_of_neg (p := isHigh v.length) (a := (i, b)) (l := ps) hneg]
      rw [agrees]
      exact and_rot ((v.getD i (!b)) == b)
        (agrees v (ps.filter (isLow v.length)))
        ((ps.filter (isHigh v.length)).all (fun p => c == p.2))
    · have heq : i = v.length := by
        omega
      subst heq
      have hdecide : decide (v.length = v.length) = true := by simp
      have hlow : isLow v.length (v.length, b) = false := by
        unfold isLow isHigh
        change (!decide (v.length = v.length)) = false
        rw [hdecide]
        rfl
      have hhigh : isHigh v.length (v.length, b) = true := by
        unfold isHigh
        change decide (v.length = v.length) = true
        exact hdecide
      have hneg : ¬ isLow v.length (v.length, b) := by
        rw [hlow]
        decide
      rw [agrees, getD_append_last, ih]
      rw [List.filter_cons_of_neg (p := isLow v.length) (a := (v.length, b)) (l := ps) hneg]
      rw [List.filter_cons_of_pos (p := isHigh v.length) (a := (v.length, b)) (l := ps) hhigh]
      rw [List.all_cons]
      exact and_comm_mid (c == b)
        (agrees v (ps.filter (isLow v.length)))
        ((ps.filter (isHigh v.length)).all (fun p => c == p.2))

theorem length_filter_half (n : Nat) (fix : List (Nat × Bool)) (c : Bool)
    (hv : ∀ v, v ∈ allVecs n → v.length = n)
    (hf : ∀ p, p ∈ fix → p.1 < n + 1) :
    ((((allVecs n).map (fun v => v ++ [c])).filter (fun w => agrees w fix)).length) =
      (if (fix.filter (isHigh n)).all (fun p => c == p.2) then
        ((allVecs n).filter (fun v => agrees v (fix.filter (isLow n)))).length
      else 0) := by
  rw [List.filter_map]
  simp only [List.length_map]
  have hpred : ∀ v, v ∈ allVecs n →
      (agrees (v ++ [c]) fix) =
        ((agrees v (fix.filter (isLow n))) &&
          ((fix.filter (isHigh n)).all (fun p => c == p.2))) := by
    intro v hv'
    have hlen : v.length = n := hv v hv'
    have hrange : ∀ p, p ∈ fix → p.1 < v.length + 1 := by
      intro p hp
      rw [hlen]
      exact hf p hp
    have hsplit := agrees_split v c fix hrange
    rw [hlen] at hsplit
    exact hsplit
  by_cases hall : ((fix.filter (isHigh n)).all (fun p => c == p.2)) = true
  · rw [if_pos hall]
    apply congrArg List.length
    apply List.filter_congr
    intro v hv'
    change agrees (v ++ [c]) fix = agrees v (fix.filter (isLow n))
    have h := hpred v hv'
    rw [h, hall]
    exact and_true _
  · rw [if_neg hall]
    rw [List.length_eq_zero_iff]
    apply List.filter_eq_nil_iff.mpr
    intro v hv'
    change ¬ agrees (v ++ [c]) fix = true
    have h := hpred v hv'
    have hall' : ((fix.filter (isHigh n)).all (fun p => c == p.2)) = false := by
      cases hflag : (fix.filter (isHigh n)).all (fun p => c == p.2)
      · rfl
      · exact False.elim (hall hflag)
    rw [h, hall']
    rw [and_false]
    decide

theorem high_card (n : Nat) :
    ∀ fix : List (Nat × Bool),
      List.Pairwise (fun a b : Nat × Bool => a.1 ≠ b.1) fix →
        (fix.filter (isHigh n)).length ≤ 1
  | [], _ => by simp
  | p :: ps, hd => by
    have hpw := List.pairwise_cons.mp hd
    cases hp : isHigh n p
    · have hp' : ¬ isHigh n p := by
        rw [hp]
        decide
      rw [List.filter_cons_of_neg hp']
      exact high_card n ps hpw.2
    · have hrest : ps.filter (isHigh n) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro q hq hhigh
        have hne := hpw.1 q hq
        have hq_idx : q.1 = n := by
          unfold isHigh at hhigh
          exact of_decide_eq_true hhigh
        have hp_idx : p.1 = n := by
          unfold isHigh at hp
          exact of_decide_eq_true hp
        exact hne (hp_idx.trans hq_idx.symm)
      rw [List.filter_cons_of_pos (p := isHigh n) hp, hrest]
      simp

theorem pairwise_indices :
    ∀ fix : List (Nat × Bool),
      List.Pairwise (fun a b : Nat × Bool => a.1 ≠ b.1) fix →
        List.Pairwise (· ≠ ·) (fix.map (·.1))
  | [], _ => by simp
  | p :: ps, hd => by
    have hpw := List.pairwise_cons.mp hd
    refine List.pairwise_cons.mpr ⟨?_, pairwise_indices ps hpw.2⟩
    intro a ha
    rcases List.mem_map.mp ha with ⟨q, hq, rfl⟩
    exact hpw.1 q hq

theorem nodup_lt_length : ∀ (n : Nat) (l : List Nat),
    List.Pairwise (· ≠ ·) l → (∀ a ∈ l, a < n) → l.length ≤ n
  | 0, [], _, _ => Nat.zero_le _
  | 0, a :: as, _, hr => by
    have hlt : a < 0 := hr a (List.mem_cons_self (l := as))
    omega
  | n + 1, l, hp, hr => by
    by_cases hn : n ∈ l
    · have hsub := List.Pairwise.sublist (List.erase_sublist (a := n) (l := l)) hp
      have hlt : ∀ a ∈ l.erase n, a < n := by
        intro a ha
        have ha' : a ∈ l := List.mem_of_mem_erase ha
        have hlt' : a < n + 1 := hr a ha'
        have hne : a ≠ n := by
          intro heq
          have hnin : n ∉ l.erase n := List.Nodup.not_mem_erase hp
          exact hnin (heq ▸ ha)
        exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hlt') hne
      have ih := nodup_lt_length n (l.erase n) hsub hlt
      have hlen : (l.erase n).length = l.length - 1 := List.length_erase_of_mem hn
      have hpos : 0 < l.length := List.length_pos_of_mem hn
      have hstep : (l.erase n).length + 1 ≤ n + 1 := Nat.succ_le_succ ih
      rw [hlen, Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)] at hstep
      exact hstep
    · have hlt : ∀ a ∈ l, a < n := by
        intro a ha
        have hlt' : a < n + 1 := hr a ha
        have hne : a ≠ n := by
          intro heq
          exact hn (heq ▸ ha)
        exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hlt') hne
      exact Nat.le_trans (nodup_lt_length n l hp hlt) (Nat.le_succ n)

theorem indices_bounded {n : Nat} {fix : List (Nat × Bool)}
    (h : IndependencePremise n fix) : fix.length ≤ n := by
  have hpw := pairwise_indices fix h.distinct
  have hr : ∀ a ∈ fix.map (·.1), a < n := by
    intro a ha
    rcases List.mem_map.mp ha with ⟨p, hp, rfl⟩
    exact h.inRange p hp
  have hlen := nodup_lt_length n (fix.map (·.1)) hpw hr
  rw [List.length_map] at hlen
  exact hlen

theorem length_ge_cover : ∀ (n : Nat) (l : List Nat),
    (∀ i, i < n → i ∈ l) → n ≤ l.length
  | 0, _, _ => Nat.zero_le _
  | n + 1, l, h => by
    have hn : n ∈ l := h n (Nat.lt_succ_self _)
    have hrest : ∀ i, i < n → i ∈ l.erase n := by
      intro i hi
      have hi' : i ∈ l := h i (Nat.lt_succ_of_lt hi)
      have hine : i ≠ n := Nat.ne_of_lt hi
      exact (List.mem_erase_of_ne hine).mpr hi'
    have ih := length_ge_cover n (l.erase n) hrest
    have hlen : (l.erase n).length = l.length - 1 := List.length_erase_of_mem hn
    have hpos : 0 < l.length := List.length_pos_of_mem hn
    have hstep : (l.erase n).length + 1 ≤ l.length := by
      rw [hlen, Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)]
      exact Nat.le_refl _
    have hge : n + 1 ≤ (l.erase n).length + 1 := Nat.succ_le_succ ih
    exact Nat.le_trans hge hstep

theorem coverage_length {n : Nat} {fix : List (Nat × Bool)}
    (hI : IndependencePremise n fix) (hC : CoveragePremise n fix) :
    fix.length = n := by
  have hge : n ≤ fix.length := by
    have hmem : ∀ i, i < n → i ∈ fix.map (·.1) := by
      intro i hi
      rcases hC.mediated i hi with ⟨b, hb⟩
      exact List.mem_map.mpr ⟨(i, b), hb, rfl⟩
    have hcov := length_ge_cover n (fix.map (·.1)) hmem
    rw [List.length_map] at hcov
    exact hcov
  exact Nat.le_antisymm (indices_bounded hI) hge

theorem low_premise {n : Nat} {fix : List (Nat × Bool)}
    (h : IndependencePremise (n + 1) fix) :
    IndependencePremise n (fix.filter (isLow n)) := by
  refine ⟨List.Pairwise.filter (isLow n) h.distinct, ?_⟩
  intro p hp
  have hmem := (List.mem_filter.mp hp).1
  have hlow := (List.mem_filter.mp hp).2
  have hlt := h.inRange p hmem
  have hdec : decide (p.1 = n) = false := by
    have hnot : (!decide (p.1 = n)) = true := by
      unfold isLow at hlow
      exact hlow
    exact (not_true_iff (decide (p.1 = n))).mp hnot
  have hne : p.1 ≠ n := (decide_eq_false_iff_not).mp hdec
  exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hlt) hne

theorem length_split (n : Nat) (fix : List (Nat × Bool)) :
    (consistentLength (n + 1) fix) =
      ((((allVecs n).map (fun v => v ++ [false])).filter (fun w => agrees w fix)).length +
        (((allVecs n).map (fun v => v ++ [true])).filter (fun w => agrees w fix)).length) := by
  rw [consistentLength, allVecs_succ, List.filter_append, List.length_append]

theorem consistent_pow :
    ∀ (n : Nat) (fix : List (Nat × Bool)),
      IndependencePremise n fix →
        consistentLength n fix = pow2 (n - fix.length)
  | 0, [], _ => by simp [consistentLength, allVecs, agrees, pow2]
  | 0, p :: _, h => by
    have := h.inRange p (List.mem_cons_self (l := _))
    omega
  | n + 1, fix, h => by
    have hfalse := length_filter_half n fix false (allVecs_vec_length n) h.inRange
    have htrue := length_filter_half n fix true (allVecs_vec_length n) h.inRange
    have hpart := filter_partition_length (isHigh n) fix
    have hcard := high_card n fix h.distinct
    have hloP := low_premise h
    have ih := consistent_pow n (fix.filter (isLow n)) hloP
    have hbound := indices_bounded hloP
    cases hhi : fix.filter (isHigh n) with
    | nil =>
      have hlen : (fix.filter (isLow n)).length = fix.length := by
        have hsum := hpart
        rw [hhi, List.length_nil, Nat.zero_add] at hsum
        have heq : fix.filter (fun a => !isHigh n a) = fix.filter (isLow n) := rfl
        rw [heq] at hsum
        exact hsum
      have hallF : ((fix.filter (isHigh n)).all (fun p => false == p.2)) = true := by
        rw [hhi]
        rfl
      have hallT : ((fix.filter (isHigh n)).all (fun p => true == p.2)) = true := by
        rw [hhi]
        rfl
      rw [hallF, if_pos rfl] at hfalse
      rw [hallT, if_pos rfl] at htrue
      rw [← consistentLength] at hfalse
      rw [← consistentLength] at htrue
      have hmain : consistentLength (n + 1) fix =
          consistentLength n (fix.filter (isLow n)) * 2 := by
        rw [length_split, hfalse, htrue]
        omega
      rw [hmain, ih, hlen]
      have hsub : n + 1 - fix.length = (n - fix.length) + 1 := by
        have hle : fix.length ≤ n := by
          rw [← hlen]
          exact hbound
        omega
      rw [hsub]
      rfl
    | cons p rest =>
      have hrest : rest = [] := by
        have hclen : (p :: rest).length ≤ 1 := by
          rw [← hhi]
          exact hcard
        cases rest with
        | nil => rfl
        | cons q qs =>
          simp at hclen
      subst hrest
      have hp_high : isHigh n p = true := by
        have hp_mem : p ∈ fix.filter (isHigh n) := by
          rw [hhi]
          exact List.mem_cons_self (l := [])
        exact (List.mem_filter.mp hp_mem).2
      have hlen : fix.length = (fix.filter (isLow n)).length + 1 := by
        have hsum := hpart
        rw [hhi, List.length_singleton] at hsum
        have heq : fix.filter (fun a => !isHigh n a) = fix.filter (isLow n) := rfl
        rw [heq] at hsum
        omega
      have hsub : n + 1 - fix.length = n - (fix.filter (isLow n)).length := by
        omega
      have hall (c : Bool) :
          ((fix.filter (isHigh n)).all (fun q => c == q.2)) = (c == p.2) := by
        rw [hhi, List.all_cons, List.all_nil, and_true]
      cases hb : p.2 with
      | false =>
        rw [hall false, hb] at hfalse
        rw [hall true, hb] at htrue
        have hff : (false == false) = true := rfl
        have htf : (true == false) = false := rfl
        rw [hff, if_pos rfl] at hfalse
        rw [htf, if_neg Bool.false_ne_true] at htrue
        rw [← consistentLength] at hfalse
        have hmain : consistentLength (n + 1) fix =
            consistentLength n (fix.filter (isLow n)) := by
          rw [length_split, hfalse, htrue, Nat.add_zero]
        rw [hmain, ih, hsub]
      | true =>
        rw [hall false, hb] at hfalse
        rw [hall true, hb] at htrue
        have hft : (false == true) = false := rfl
        have htt : (true == true) = true := rfl
        rw [hft, if_neg Bool.false_ne_true] at hfalse
        rw [htt, if_pos rfl] at htrue
        rw [← consistentLength] at htrue
        have hmain : consistentLength (n + 1) fix =
            consistentLength n (fix.filter (isLow n)) := by
          rw [length_split, hfalse, htrue, Nat.zero_add]
        rw [hmain, ih, hsub]

theorem evidence_cuts {n : Nat} {fix : List (Nat × Bool)}
    (h : IndependencePremise n fix) :
    consistentLength n fix * pow2 fix.length = pow2 n := by
  rw [consistent_pow n fix h]
  have hb := indices_bounded h
  calc
    pow2 (n - fix.length) * pow2 fix.length = pow2 ((n - fix.length) + fix.length) :=
      (pow2_add (n - fix.length) fix.length).symm
    _ = pow2 n := by rw [Nat.sub_add_cancel hb]

theorem consistent_singleton_of_coverage {n : Nat} {fix : List (Nat × Bool)}
    (hI : IndependencePremise n fix) (hC : CoveragePremise n fix) :
    consistentLength n fix = 1 := by
  rw [consistent_pow n fix hI, coverage_length hI hC, Nat.sub_self, pow2]

theorem partial_not_singleton {n : Nat} {fix : List (Nat × Bool)}
    (hI : IndependencePremise n fix) (hk : fix.length < n) :
    consistentLength n fix ≠ 1 := by
  rw [consistent_pow n fix hI]
  have hge : 2 ≤ pow2 (n - fix.length) := pow2_at_least_two (by omega)
  omega

theorem duplicate_does_not_cut :
    let n := 2
    let fix : List (Nat × Bool) := [(0, true), (0, true)]
    let got := consistentLength n fix
    (got * pow2 fix.length ≠ pow2 n) ∧ (got * pow2 1 = pow2 n) := by
  decide

end IncrementalCert
