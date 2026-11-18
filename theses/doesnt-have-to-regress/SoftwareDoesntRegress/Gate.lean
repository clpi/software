import SoftwareDoesntRegress.Profiles

namespace SoftwareDoesntRegress

theorem band_eq {a b : Bool} : (a && b) = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

theorem bor_eq {a b : Bool} : (a || b) = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> decide

theorem bnot_eq {a : Bool} : (!a) = true ↔ a = false := by
  cases a <;> decide

theorem behaviorsKept_iff {β : Type} [DecidableEq β] (inc cand : List β) :
    behaviorsKept inc cand = true ↔ ∀ b ∈ inc, b ∈ cand := by
  simpa [behaviorsKept] using
    (SoftwareIsQuantifiable.Pareto.accepts_iff (qualified := inc) (candidate := cand))

theorem behaviorsKept_trans {β : Type} [DecidableEq β] {a b c : List β}
    (hab : behaviorsKept a b = true) (hbc : behaviorsKept b c = true) :
    behaviorsKept a c = true := by
  apply (behaviorsKept_iff a c).mpr
  intro x hx
  exact (behaviorsKept_iff b c).mp hbc x ((behaviorsKept_iff a b).mp hab x hx)

theorem newBehavior_iff {β : Type} [DecidableEq β] (inc cand : List β) :
    newBehavior inc cand = true ↔ ∃ b, b ∈ cand ∧ b ∉ inc := by
  induction cand with
  | nil => simp [newBehavior]
  | cons b bs ih =>
    simp [newBehavior, bor_eq, bnot_eq, decide_eq_false_iff_not, ih, List.mem_cons]

theorem newBehavior_of_kept {β : Type} [DecidableEq β] {inc cand : List β}
    (h : behaviorsKept cand inc = true) : newBehavior inc cand = false := by
  cases hnew : newBehavior inc cand with
  | false => rfl
  | true =>
    obtain ⟨b, hb, hn⟩ := (newBehavior_iff inc cand).mp hnew
    exact absurd ((behaviorsKept_iff cand inc).mp h b hb) hn

theorem newBehavior_lift {β : Type} [DecidableEq β] {a b c : List β}
    (hsub : behaviorsKept a b = true) (hnew : newBehavior b c = true) :
    newBehavior a c = true := by
  obtain ⟨x, hx, hn⟩ := (newBehavior_iff b c).mp hnew
  apply (newBehavior_iff a c).mpr
  refine ⟨x, hx, ?_⟩
  intro ha
  exact hn ((behaviorsKept_iff a b).mp hsub x ha)

theorem Bound.noWorse_iff {inc cand : Bound} :
    Bound.noWorse inc cand = true ↔ cand.lo ≤ inc.lo ∧ cand.hi ≤ inc.hi := by
  simp [Bound.noWorse, band_eq, decide_eq_true_eq]

theorem Bound.strict_iff {inc cand : Bound} :
    Bound.strict inc cand = true ↔ cand.lo < inc.lo ∨ cand.hi < inc.hi := by
  simp [Bound.strict, bor_eq, decide_eq_true_eq]

theorem Bound.ok_iff {b : Bound} : Bound.ok b = true ↔ b.lo ≤ b.hi := by
  simp [Bound.ok, decide_eq_true_eq]

theorem Bound.noWorse_refl (b : Bound) : Bound.noWorse b b = true := by
  simp [Bound.noWorse_iff]

theorem Bound.strict_irrefl (b : Bound) : Bound.strict b b = false := by
  cases h : Bound.strict b b with
  | false => rfl
  | true =>
    have hlt := Bound.strict_iff.mp h
    cases hlt with
    | inl h => exact absurd h (Nat.lt_irrefl _)
    | inr h => exact absurd h (Nat.lt_irrefl _)

theorem Bound.noWorse_trans {a b c : Bound}
    (hab : Bound.noWorse a b = true) (hbc : Bound.noWorse b c = true) :
    Bound.noWorse a c = true := by
  have hab := Bound.noWorse_iff.mp hab
  have hbc := Bound.noWorse_iff.mp hbc
  exact Bound.noWorse_iff.mpr ⟨Nat.le_trans hbc.1 hab.1, Nat.le_trans hbc.2 hab.2⟩

theorem Bound.strict_lift {a b c : Bound}
    (hab : Bound.noWorse a b = true) (hbc : Bound.noWorse b c = true)
    (hs : Bound.strict b c = true) : Bound.strict a c = true := by
  have hab := Bound.noWorse_iff.mp hab
  have hbc := Bound.noWorse_iff.mp hbc
  have hs := Bound.strict_iff.mp hs
  apply Bound.strict_iff.mpr
  cases hs with
  | inl h => exact Or.inl (Nat.lt_of_lt_of_le h hab.1)
  | inr h => exact Or.inr (Nat.lt_of_lt_of_le h hab.2)

theorem Bound.noWorse_antisym {a b : Bound}
    (hab : Bound.noWorse a b = true) (hba : Bound.noWorse b a = true) :
    a = b := by
  have hab := Bound.noWorse_iff.mp hab
  have hba := Bound.noWorse_iff.mp hba
  cases a
  cases b
  simp
  exact ⟨Nat.le_antisymm hba.1 hab.1, Nat.le_antisymm hba.2 hab.2⟩

theorem addBound_ok {a b : Bound} (ha : Bound.ok a = true) (hb : Bound.ok b = true) :
    Bound.ok (addBound a b) = true := by
  have ha := Bound.ok_iff.mp ha
  have hb := Bound.ok_iff.mp hb
  exact Bound.ok_iff.mpr (Nat.add_le_add ha hb)

theorem addBound_noWorse {a b c d : Bound}
    (hab : Bound.noWorse a b = true) (hcd : Bound.noWorse c d = true) :
    Bound.noWorse (addBound a c) (addBound b d) = true := by
  have hab := Bound.noWorse_iff.mp hab
  have hcd := Bound.noWorse_iff.mp hcd
  apply Bound.noWorse_iff.mpr
  constructor
  · exact Nat.add_le_add hab.1 hcd.1
  · exact Nat.add_le_add hab.2 hcd.2

theorem addBound_strict_right {a b c d : Bound}
    (hab : Bound.noWorse a b = true) (hcd : Bound.noWorse c d = true)
    (hs : Bound.strict c d = true) :
    Bound.strict (addBound a c) (addBound b d) = true := by
  have hab := Bound.noWorse_iff.mp hab
  have hcd := Bound.noWorse_iff.mp hcd
  have hs := Bound.strict_iff.mp hs
  apply Bound.strict_iff.mpr
  cases hs with
  | inl h => exact Or.inl (Nat.add_lt_add_of_le_of_lt hab.1 h)
  | inr h => exact Or.inr (Nat.add_lt_add_of_le_of_lt hab.2 h)

theorem addBound_strict_left {a b c d : Bound}
    (hab : Bound.noWorse a b = true) (hcd : Bound.noWorse c d = true)
    (hs : Bound.strict a b = true) :
    Bound.strict (addBound a c) (addBound b d) = true := by
  have hab := Bound.noWorse_iff.mp hab
  have hcd := Bound.noWorse_iff.mp hcd
  have hs := Bound.strict_iff.mp hs
  apply Bound.strict_iff.mpr
  cases hs with
  | inl h => exact Or.inl (Nat.add_lt_add_of_lt_of_le h hcd.1)
  | inr h => exact Or.inr (Nat.add_lt_add_of_lt_of_le h hcd.2)

theorem boundsNoWorse_refl : ∀ bs, boundsNoWorse bs bs = true
  | [] => rfl
  | b :: bs => by
    simp [boundsNoWorse, Bound.noWorse_refl, boundsNoWorse_refl bs]

theorem boundsNoWorse_trans {a b c : List Bound}
    (hab : boundsNoWorse a b = true) (hbc : boundsNoWorse b c = true) :
    boundsNoWorse a c = true := by
  induction a generalizing b c with
  | nil =>
    cases b with
    | nil =>
      cases c with
      | nil => exact hab
      | cons => simp [boundsNoWorse] at hbc
    | cons => simp [boundsNoWorse] at hab
  | cons a as ih =>
    cases b with
    | nil => simp [boundsNoWorse] at hab
    | cons b bs =>
      cases c with
      | nil => simp [boundsNoWorse] at hbc
      | cons c cs =>
        simp [boundsNoWorse, band_eq] at hab hbc ⊢
        exact ⟨Bound.noWorse_trans hab.1 hbc.1, ih hab.2 hbc.2⟩

theorem boundsStrict_irrefl : ∀ bs, boundsStrict bs bs = false
  | [] => rfl
  | b :: bs => by
    simp [boundsStrict, Bound.strict_irrefl, boundsStrict_irrefl bs]

theorem boundsStrict_lift {a b c : List Bound}
    (hab : boundsNoWorse a b = true) (hbc : boundsNoWorse b c = true)
    (hs : boundsStrict b c = true) : boundsStrict a c = true := by
  induction b generalizing a c with
  | nil =>
    cases a with
    | nil =>
      cases c with
      | nil => simp [boundsStrict] at hs
      | cons => simp [boundsNoWorse] at hbc
    | cons => simp [boundsNoWorse] at hab
  | cons b bs ih =>
    cases a with
    | nil => simp [boundsNoWorse] at hab
    | cons a as =>
      cases c with
      | nil => simp [boundsNoWorse] at hbc
      | cons c cs =>
        simp [boundsNoWorse, boundsStrict, band_eq, bor_eq] at hab hbc hs ⊢
        cases hs with
        | inl h => exact Or.inl (Bound.strict_lift hab.1 hbc.1 h)
        | inr h => exact Or.inr (ih hab.2 hbc.2 h)

theorem boundsNoWorse_antisym {a b : List Bound}
    (hab : boundsNoWorse a b = true) (hba : boundsNoWorse b a = true) :
    a = b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons => simp [boundsNoWorse] at hab
  | cons a as ih =>
    cases b with
    | nil => simp [boundsNoWorse] at hab
    | cons b bs =>
      simp [boundsNoWorse, band_eq] at hab hba
      have hhead := Bound.noWorse_antisym hab.1 hba.1
      have htail := ih hab.2 hba.2
      simp [hhead, htail]

theorem profileNoRegress_iff {β : Type} [DecidableEq β] (inc cand : Profile β) :
    profileNoRegress inc cand = true ↔
      behaviorsKept inc.behaviors cand.behaviors = true ∧
        boundsNoWorse inc.bounds cand.bounds = true := by
  simp [profileNoRegress, band_eq]

theorem profileStrict_iff {β : Type} [DecidableEq β] (inc cand : Profile β) :
    profileStrict inc cand = true ↔
      newBehavior inc.behaviors cand.behaviors = true ∨
        boundsStrict inc.bounds cand.bounds = true := by
  simp [profileStrict, bor_eq]

theorem profileNoRegress_refl {β : Type} [DecidableEq β] (p : Profile β) :
    profileNoRegress p p = true := by
  apply (profileNoRegress_iff p p).mpr
  refine ⟨?_, boundsNoWorse_refl p.bounds⟩
  apply (behaviorsKept_iff p.behaviors p.behaviors).mpr
  intro b hb
  exact hb

theorem profileStrict_irrefl {β : Type} [DecidableEq β] (p : Profile β) :
    profileStrict p p = false := by
  cases h : profileStrict p p with
  | false => rfl
  | true =>
    have h := (profileStrict_iff p p).mp h
    cases h with
    | inl h => exact absurd h (by
        have hfalse := newBehavior_of_kept (inc := p.behaviors) (cand := p.behaviors)
          ((behaviorsKept_iff _ _).mpr (fun _ hb => hb))
        simp [hfalse] at h)
    | inr h =>
      have hfalse := boundsStrict_irrefl p.bounds
      simp [hfalse] at h

theorem profileNoRegress_trans {β : Type} [DecidableEq β] {a b c : Profile β}
    (hab : profileNoRegress a b = true) (hbc : profileNoRegress b c = true) :
    profileNoRegress a c = true := by
  have hab := (profileNoRegress_iff a b).mp hab
  have hbc := (profileNoRegress_iff b c).mp hbc
  apply (profileNoRegress_iff a c).mpr
  exact ⟨behaviorsKept_trans hab.1 hbc.1, boundsNoWorse_trans hab.2 hbc.2⟩

theorem profileStrict_lift {β : Type} [DecidableEq β] {a b c : Profile β}
    (hab : profileNoRegress a b = true) (hbc : profileNoRegress b c = true)
    (hs : profileStrict b c = true) : profileStrict a c = true := by
  have hab := (profileNoRegress_iff a b).mp hab
  have hbc := (profileNoRegress_iff b c).mp hbc
  have hs := (profileStrict_iff b c).mp hs
  apply (profileStrict_iff a c).mpr
  cases hs with
  | inl h => exact Or.inl (newBehavior_lift hab.1 h)
  | inr h => exact Or.inr (boundsStrict_lift hab.2 hbc.2 h)

theorem profileNoRegress_antisym {β : Type} [DecidableEq β] {a b : Profile β}
    (hab : profileNoRegress a b = true) (hba : profileNoRegress b a = true) :
    profileStrict a b = false := by
  have habp := (profileNoRegress_iff a b).mp hab
  have hbap := (profileNoRegress_iff b a).mp hba
  cases h : profileStrict a b with
  | false => rfl
  | true =>
    have hs := (profileStrict_iff a b).mp h
    cases hs with
    | inl hnew => exact absurd hnew (by
        have hfalse := newBehavior_of_kept hbap.1
        simp [hfalse] at hnew)
    | inr hbound =>
      have heq := boundsNoWorse_antisym habp.2 hbap.2
      rw [heq] at hbound
      have hfalse := boundsStrict_irrefl b.bounds
      simp [hfalse] at hbound

theorem noRegress_refl {β : Type} [DecidableEq β] : ∀ r : Release β, noRegress r r = true
  | [] => rfl
  | p :: ps => by
    simp [noRegress, profileNoRegress_refl, noRegress_refl ps]

theorem strictGain_irrefl {β : Type} [DecidableEq β] : ∀ r : Release β, strictGain r r = false
  | [] => rfl
  | p :: ps => by
    simp [strictGain, profileStrict_irrefl, strictGain_irrefl ps]

theorem noRegress_trans {β : Type} [DecidableEq β] {a b c : Release β}
    (hab : noRegress a b = true) (hbc : noRegress b c = true) :
    noRegress a c = true := by
  induction a generalizing b c with
  | nil =>
    cases b with
    | nil =>
      cases c with
      | nil => exact hab
      | cons => simp [noRegress] at hbc
    | cons => simp [noRegress] at hab
  | cons a as ih =>
    cases b with
    | nil => simp [noRegress] at hab
    | cons b bs =>
      cases c with
      | nil => simp [noRegress] at hbc
      | cons c cs =>
        simp [noRegress, band_eq] at hab hbc ⊢
        exact ⟨profileNoRegress_trans hab.1 hbc.1, ih hab.2 hbc.2⟩

theorem strictGain_lift {β : Type} [DecidableEq β] {a b c : Release β}
    (hab : noRegress a b = true) (hbc : noRegress b c = true)
    (hs : strictGain b c = true) : strictGain a c = true := by
  induction b generalizing a c with
  | nil =>
    cases a with
    | nil =>
      cases c with
      | nil => simp [strictGain] at hs
      | cons => simp [noRegress] at hbc
    | cons => simp [noRegress] at hab
  | cons b bs ih =>
    cases a with
    | nil => simp [noRegress] at hab
    | cons a as =>
      cases c with
      | nil => simp [noRegress] at hbc
      | cons c cs =>
        simp [noRegress, strictGain, band_eq, bor_eq] at hab hbc hs ⊢
        cases hs with
        | inl h => exact Or.inl (profileStrict_lift hab.1 hbc.1 h)
        | inr h => exact Or.inr (ih hab.2 hbc.2 h)

theorem strictGain_of_antisym {β : Type} [DecidableEq β] {a b : Release β}
    (hab : noRegress a b = true) (hba : noRegress b a = true) :
    strictGain a b = false := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons => simp [noRegress] at hab
  | cons a as ih =>
    cases b with
    | nil => simp [noRegress] at hab
    | cons b bs =>
      simp [noRegress, band_eq] at hab hba
      have hhead := profileNoRegress_antisym hab.1 hba.1
      have htail := ih hab.2 hba.2
      simp [strictGain, hhead, htail]

theorem releaseOk_cons_iff {β : Type} {p : Profile β} {ps : Release β} :
    releaseOk (p :: ps) = true ↔ boundsOk p.bounds = true ∧ releaseOk ps = true := by
  simp [releaseOk, band_eq]

theorem accepts_iff_parts {β : Type} [DecidableEq β] {inc cand : Release β} :
    accepts inc cand = true ↔
      releaseOk inc = true ∧ releaseOk cand = true ∧
        noRegress inc cand = true ∧ strictGain inc cand = true := by
  simp [accepts, band_eq, and_assoc]

theorem accepts_irrefl {β : Type} [DecidableEq β] (r : Release β) : accepts r r = false := by
  cases h : accepts r r with
  | false => rfl
  | true =>
    have hs := ((accepts_iff_parts (inc := r) (cand := r)).mp h).2.2.2
    have hfalse := strictGain_irrefl r
    simp [hfalse] at hs

theorem accepted_strict {β : Type} [DecidableEq β] {inc cand : Release β}
    (h : accepts inc cand = true) :
    noRegress inc cand = true ∧ strictGain inc cand = true ∧ cand ≠ inc := by
  have hp := (accepts_iff_parts (inc := inc) (cand := cand)).mp h
  refine ⟨hp.2.2.1, hp.2.2.2, ?_⟩
  intro heq
  cases heq
  have hfalse := strictGain_irrefl inc
  simp [hfalse] at hp

theorem accepts_complete {β : Type} [DecidableEq β] {inc cand : Release β}
    (hokI : releaseOk inc = true) (hokC : releaseOk cand = true)
    (hn : noRegress inc cand = true) (hs : strictGain inc cand = true) :
    accepts inc cand = true := by
  exact (accepts_iff_parts (inc := inc) (cand := cand)).mpr ⟨hokI, hokC, hn, hs⟩

theorem accepts_lift {β : Type} [DecidableEq β] {a b c : Release β}
    (hab : noRegress a b = true) (hbc : accepts b c = true) (hok : releaseOk a = true) :
    accepts a c = true := by
  have hp := (accepts_iff_parts (inc := b) (cand := c)).mp hbc
  exact accepts_complete hok hp.2.1 (noRegress_trans hab hp.2.2.1)
    (strictGain_lift hab hp.2.2.1 hp.2.2.2)

theorem step_noRegress {β : Type} [DecidableEq β] (inc cand : Release β) :
    noRegress inc (step inc cand) = true := by
  unfold step
  split
  · next h => exact ((accepts_iff_parts (inc := inc) (cand := cand)).mp h).2.2.1
  · exact noRegress_refl inc

theorem step_witness {β : Type} [DecidableEq β] (inc cand : Release β) :
    noRegress inc (step inc cand) = true ∧
      (step inc cand = cand ∨ step inc cand = inc) := by
  refine ⟨step_noRegress inc cand, ?_⟩
  unfold step
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem bool_eq_false_of_ne_true {a : Bool} (h : ¬ a = true) : a = false := by
  cases a <;> simp_all

end SoftwareDoesntRegress
