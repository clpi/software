import SoftwareDoesntRegress.Gate

namespace SoftwareDoesntRegress

def sideInc {β : Type} (p : Pair β) : Profile β :=
  p.inc

def sideCand {β : Type} (p : Pair β) : Profile β :=
  p.cand

def syms {β : Type} (ps : List (Pair β)) : List Nat :=
  ps.map fun p => p.sym

def pairsOk {β : Type} [DecidableEq β] : List (Pair β) → Bool
  | [] => true
  | p :: ps => profileNoRegress p.inc p.cand && pairsOk ps

def notElem : Nat → List Nat → Bool
  | _, [] => true
  | x, y :: ys => decide (x ≠ y) && notElem x ys

def nodupB : List Nat → Bool
  | [] => true
  | x :: xs => notElem x xs && nodupB xs

def axisGet : Nat → List Bound → Bound
  | _, [] => { lo := 0, hi := 0 }
  | 0, b :: _ => b
  | n + 1, _ :: bs => axisGet n bs

def sumLo (k : Nat) {β : Type} (ps : List (Pair β)) (side : Pair β → Profile β) : Nat :=
  ps.foldl (fun s p => s + (axisGet k (side p).bounds).lo) 0

def sumHi (k : Nat) {β : Type} (ps : List (Pair β)) (side : Pair β → Profile β) : Nat :=
  ps.foldl (fun s p => s + (axisGet k (side p).bounds).hi) 0

def Seen {β : Type} (ps : List (Pair β)) (side : Pair β → Profile β) (i : Nat) (b : β) : Prop :=
  ∃ p, p ∈ ps ∧ p.sym = i ∧ b ∈ (side p).behaviors

theorem pairs_all_ok {β : Type} [DecidableEq β] {ps : List (Pair β)}
    (h : pairsOk ps = true) {p : Pair β} (hp : p ∈ ps) :
    profileNoRegress p.inc p.cand = true := by
  induction ps with
  | nil => cases hp
  | cons q qs ih =>
    cases hp with
    | head =>
      simp [pairsOk, band_eq] at h
      exact h.1
    | tail _ hp =>
      simp [pairsOk, band_eq] at h
      exact ih h.2 hp

theorem notElem_iff (x : Nat) (xs : List Nat) : notElem x xs = true ↔ x ∉ xs := by
  induction xs with
  | nil => simp [notElem]
  | cons y ys ih =>
    simp [notElem, band_eq, decide_eq_true_eq, ih, List.mem_cons]

theorem nodup_cons {x : Nat} {xs : List Nat} :
    nodupB (x :: xs) = true ↔ notElem x xs = true ∧ nodupB xs = true := by
  simp [nodupB, band_eq]

theorem sym_unique {β : Type} {ps : List (Pair β)} {p q : Pair β}
    (huniq : nodupB (syms ps) = true) (hp : p ∈ ps) (hq : q ∈ ps) (hsym : p.sym = q.sym) :
    p = q := by
  induction ps with
  | nil => cases hp
  | cons hd tl ih =>
    cases hp with
    | head =>
      cases hq with
      | head => rfl
      | tail _ hq =>
        have hnod := nodup_cons.mp huniq
        exact False.elim ((notElem_iff p.sym (syms tl)).mp hnod.1
          (List.mem_map.mpr ⟨q, hq, hsym.symm⟩))
    | tail _ hp =>
      cases hq with
      | head =>
        have hnod := nodup_cons.mp huniq
        exact False.elim ((notElem_iff q.sym (syms tl)).mp hnod.1
          (List.mem_map.mpr ⟨p, hp, hsym⟩))
      | tail _ hq =>
        exact ih (nodup_cons.mp huniq).2 hp hq

theorem axis_mono : ∀ (k : Nat) {a b : List Bound},
    boundsNoWorse a b = true →
      (axisGet k b).lo ≤ (axisGet k a).lo ∧ (axisGet k b).hi ≤ (axisGet k a).hi
  | 0, [], [], _ => by simp [axisGet]
  | 0, a :: _, b :: _, h => by
    simp [axisGet, boundsNoWorse, band_eq, Bound.noWorse_iff] at h
    exact h.1
  | 0, [], _ :: _, h => by simp [boundsNoWorse] at h
  | 0, _ :: _, [], h => by simp [boundsNoWorse] at h
  | k + 1, [], [], _ => by simp [axisGet]
  | k + 1, _ :: as, _ :: bs, h => by
    simp [axisGet, boundsNoWorse, band_eq] at h
    exact axis_mono k h.2
  | k + 1, [], _ :: _, h => by simp [boundsNoWorse] at h
  | k + 1, _ :: _, [], h => by simp [boundsNoWorse] at h

theorem foldl_add {α : Type} (ps : List α) (g : α → Nat) (s : Nat) :
    ps.foldl (fun acc x => acc + g x) s = s + ps.foldl (fun acc x => acc + g x) 0 := by
  induction ps generalizing s with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [ih (g x), ih]
    simp [Nat.add_assoc, Nat.add_left_comm]

theorem sumLo_cons {β : Type} (k : Nat) (p : Pair β) (ps : List (Pair β))
    (side : Pair β → Profile β) :
    sumLo k (p :: ps) side = (axisGet k (side p).bounds).lo + sumLo k ps side := by
  rw [sumLo, List.foldl_cons, Nat.zero_add, foldl_add, sumLo]

theorem sumHi_cons {β : Type} (k : Nat) (p : Pair β) (ps : List (Pair β))
    (side : Pair β → Profile β) :
    sumHi k (p :: ps) side = (axisGet k (side p).bounds).hi + sumHi k ps side := by
  rw [sumHi, List.foldl_cons, Nat.zero_add, foldl_add, sumHi]

theorem sumLo_le {β : Type} [DecidableEq β] (k : Nat) (ps : List (Pair β))
    (h : pairsOk ps = true) :
    sumLo k ps sideCand ≤ sumLo k ps sideInc := by
  induction ps with
  | nil => simp [sumLo]
  | cons p ps ih =>
    have hp := pairs_all_ok h List.mem_cons_self
    have htail : pairsOk ps = true := by
      exact (band_eq.mp (by simpa [pairsOk] using h)).2
    have hnw := ((profileNoRegress_iff p.inc p.cand).mp hp).2
    have haxis := (axis_mono k hnw).1
    rw [sumLo_cons, sumLo_cons]
    exact Nat.add_le_add haxis (ih htail)

theorem sumHi_le {β : Type} [DecidableEq β] (k : Nat) (ps : List (Pair β))
    (h : pairsOk ps = true) :
    sumHi k ps sideCand ≤ sumHi k ps sideInc := by
  induction ps with
  | nil => simp [sumHi]
  | cons p ps ih =>
    have hp := pairs_all_ok h List.mem_cons_self
    have htail : pairsOk ps = true := by
      exact (band_eq.mp (by simpa [pairsOk] using h)).2
    have hnw := ((profileNoRegress_iff p.inc p.cand).mp hp).2
    have haxis := (axis_mono k hnw).2
    rw [sumHi_cons, sumHi_cons]
    exact Nat.add_le_add haxis (ih htail)

theorem sumLo_lt {β : Type} [DecidableEq β] (k : Nat) (ps : List (Pair β))
    (h : pairsOk ps = true)
    (hs : ∃ p, p ∈ ps ∧ (axisGet k p.cand.bounds).lo < (axisGet k p.inc.bounds).lo) :
    sumLo k ps sideCand < sumLo k ps sideInc := by
  induction ps with
  | nil =>
    obtain ⟨_, hmem, _⟩ := hs
    cases hmem
  | cons p ps ih =>
    have hp := pairs_all_ok h List.mem_cons_self
    have htail : pairsOk ps = true := by
      exact (band_eq.mp (by simpa [pairsOk] using h)).2
    have hnw := ((profileNoRegress_iff p.inc p.cand).mp hp).2
    have haxis := (axis_mono k hnw).1
    rw [sumLo_cons, sumLo_cons]
    obtain ⟨q, hq, hlt⟩ := hs
    cases hq with
    | head =>
      exact Nat.add_lt_add_of_lt_of_le hlt (sumLo_le k ps htail)
    | tail _ hq =>
      exact Nat.add_lt_add_of_le_of_lt haxis (ih htail ⟨q, hq, hlt⟩)

theorem sumHi_lt {β : Type} [DecidableEq β] (k : Nat) (ps : List (Pair β))
    (h : pairsOk ps = true)
    (hs : ∃ p, p ∈ ps ∧ (axisGet k p.cand.bounds).hi < (axisGet k p.inc.bounds).hi) :
    sumHi k ps sideCand < sumHi k ps sideInc := by
  induction ps with
  | nil =>
    obtain ⟨_, hmem, _⟩ := hs
    cases hmem
  | cons p ps ih =>
    have hp := pairs_all_ok h List.mem_cons_self
    have htail : pairsOk ps = true := by
      exact (band_eq.mp (by simpa [pairsOk] using h)).2
    have hnw := ((profileNoRegress_iff p.inc p.cand).mp hp).2
    have haxis := (axis_mono k hnw).2
    rw [sumHi_cons, sumHi_cons]
    obtain ⟨q, hq, hlt⟩ := hs
    cases hq with
    | head =>
      exact Nat.add_lt_add_of_lt_of_le hlt (sumHi_le k ps htail)
    | tail _ hq =>
      exact Nat.add_lt_add_of_le_of_lt haxis (ih htail ⟨q, hq, hlt⟩)

theorem seen_kept {β : Type} [DecidableEq β] {ps : List (Pair β)}
    (h : pairsOk ps = true) {i : Nat} {b : β}
    (hs : Seen ps sideInc i b) : Seen ps sideCand i b := by
  obtain ⟨p, hp, hsym, hb⟩ := hs
  have hkeep := ((profileNoRegress_iff p.inc p.cand).mp (pairs_all_ok h hp)).1
  exact ⟨p, hp, hsym, (behaviorsKept_iff _ _).mp hkeep b hb⟩

theorem seen_new {β : Type} [DecidableEq β] {ps : List (Pair β)} {p : Pair β} {b : β}
    (hp : p ∈ ps) (hnew : b ∈ p.cand.behaviors) (hmiss : b ∉ p.inc.behaviors)
    (huniq : nodupB (syms ps) = true) :
    Seen ps sideCand p.sym b ∧ ¬ Seen ps sideInc p.sym b := by
  refine ⟨⟨p, hp, rfl, hnew⟩, ?_⟩
  intro hs
  obtain ⟨q, hq, hsym, hb⟩ := hs
  have hsame := sym_unique huniq hq hp hsym
  cases hsame
  exact hmiss hb

theorem fine_pairs_ok {β : Type} [DecidableEq β] {ps : List (Pair β)}
    (h : noRegress (fineInc ps) (fineCand ps) = true) : pairsOk ps = true := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp [fineInc, fineCand, noRegress, pairsOk, band_eq] at h ⊢
    exact ⟨h.1, ih h.2⟩

theorem fine_has_strict {β : Type} [DecidableEq β] {ps : List (Pair β)}
    (h : strictGain (fineInc ps) (fineCand ps) = true) :
    ∃ p, p ∈ ps ∧ profileStrict p.inc p.cand = true := by
  induction ps with
  | nil => simp [fineInc, fineCand, strictGain] at h
  | cons p ps ih =>
    simp [fineInc, fineCand, strictGain, bor_eq] at h
    cases h with
    | inl h => exact ⟨p, List.mem_cons_self, h⟩
    | inr h =>
      obtain ⟨q, hq, hs⟩ := ih h
      exact ⟨q, List.mem_cons_of_mem _ hq, hs⟩

theorem exists_axis_strict {a b : List Bound}
    (hnw : boundsNoWorse a b = true) (hs : boundsStrict a b = true) :
    ∃ k, (axisGet k b).lo < (axisGet k a).lo ∨ (axisGet k b).hi < (axisGet k a).hi := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => simp [boundsStrict] at hs
    | cons => simp [boundsNoWorse] at hnw
  | cons a as ih =>
    cases b with
    | nil => simp [boundsNoWorse] at hnw
    | cons b bs =>
      simp [boundsNoWorse, boundsStrict, band_eq, bor_eq] at hnw hs
      cases hs with
      | inl h =>
        refine ⟨0, ?_⟩
        simp [axisGet, Bound.strict_iff] at h
        exact h
      | inr h =>
        obtain ⟨k, hk⟩ := ih hnw.2 h
        exact ⟨k + 1, by simpa [axisGet] using hk⟩

theorem finer_bounds {β : Type} [DecidableEq β] {ps : List (Pair β)}
    (h : noRegress (fineInc ps) (fineCand ps) = true) (k : Nat) :
    sumLo k ps sideCand ≤ sumLo k ps sideInc ∧
      sumHi k ps sideCand ≤ sumHi k ps sideInc :=
  ⟨sumLo_le k ps (fine_pairs_ok h), sumHi_le k ps (fine_pairs_ok h)⟩

theorem finer_behaviors {β : Type} [DecidableEq β] {ps : List (Pair β)}
    (h : noRegress (fineInc ps) (fineCand ps) = true) :
    ∀ i b, Seen ps sideInc i b → Seen ps sideCand i b :=
  fun _ _ hs => seen_kept (fine_pairs_ok h) hs

theorem finer_strict {β : Type} [DecidableEq β] {ps : List (Pair β)}
    (hn : noRegress (fineInc ps) (fineCand ps) = true)
    (hs : strictGain (fineInc ps) (fineCand ps) = true)
    (huniq : nodupB (syms ps) = true) :
    (∃ i b, Seen ps sideCand i b ∧ ¬ Seen ps sideInc i b) ∨
      (∃ k, sumLo k ps sideCand < sumLo k ps sideInc ∨
        sumHi k ps sideCand < sumHi k ps sideInc) := by
  obtain ⟨p, hp, hstrict⟩ := fine_has_strict hs
  have hprof := (profileStrict_iff p.inc p.cand).mp hstrict
  cases hprof with
  | inl hnew =>
    obtain ⟨b, hb, hmiss⟩ := (newBehavior_iff p.inc.behaviors p.cand.behaviors).mp hnew
    have hseen := seen_new hp hb hmiss huniq
    exact Or.inl ⟨p.sym, b, hseen.1, hseen.2⟩
  | inr hbound =>
    have hok := fine_pairs_ok hn
    have hpair := pairs_all_ok hok hp
    have hnw := ((profileNoRegress_iff p.inc p.cand).mp hpair).2
    obtain ⟨k, hk⟩ := exists_axis_strict hnw hbound
    cases hk with
    | inl h => exact Or.inr ⟨k, Or.inl (sumLo_lt k ps hok ⟨p, hp, h⟩)⟩
    | inr h => exact Or.inr ⟨k, Or.inr (sumHi_lt k ps hok ⟨p, hp, h⟩)⟩

theorem coarse_admits_symbol_regression :
    accepts exInc exTrade = false ∧
      accepts (coarsen exBlock exInc) (coarsen exBlock exTrade) = true := by
  decide

theorem refuse_named_symbol : firstRefusal exNames exInc exPure = some "emit" := by
  decide

end SoftwareDoesntRegress
