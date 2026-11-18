import SoftwareIsComposable.Profile

namespace SoftwareIsComposable

def accepts (qualified candidate : List Nat) : Bool :=
  qualified.all fun b => decide (b ∈ candidate)

theorem accepts_iff {qualified candidate : List Nat} :
    accepts qualified candidate = true ↔ ∀ b ∈ qualified, b ∈ candidate := by
  simp [accepts, List.all_eq_true, decide_eq_true_iff]

structure SymbolAdmitted (old new : SymbolProfile) : Prop where
  sameId : old.id = new.id
  validOld : ∀ b ∈ old.costs, b.lo ≤ b.hi
  validNew : ∀ b ∈ new.costs, b.lo ≤ b.hi
  keeps : ∀ b ∈ old.behaviors, b ∈ new.behaviors
  costLen : old.costs.length = new.costs.length
  costHi : ∀ x ∈ old.costs.zip new.costs, x.2.hi ≤ x.1.hi

def symbolAdmitted (old new : SymbolProfile) : Bool :=
  decide (old.id = new.id) &&
    old.costs.all (fun b => decide (b.lo ≤ b.hi)) &&
    new.costs.all (fun b => decide (b.lo ≤ b.hi)) &&
    old.behaviors.all (fun b => new.behaviors.contains b) &&
    decide (old.costs.length = new.costs.length) &&
    (old.costs.zip new.costs).all (fun x => decide (x.2.hi ≤ x.1.hi))

theorem symbolAdmitted_iff {old new : SymbolProfile} :
    symbolAdmitted old new = true ↔ SymbolAdmitted old new := by
  constructor
  · intro h
    simp [symbolAdmitted, Bool.and_eq_true, List.all_eq_true, decide_eq_true_iff,
      List.contains_iff] at h
    rcases h with ⟨⟨⟨⟨⟨hid, hvo⟩, hvn⟩, hk⟩, hlen⟩, hhi⟩
    refine ⟨hid, hvo, hvn, hk, hlen, ?_⟩
    intro x hx
    exact hhi x.1 x.2 hx
  · intro h
    simp [symbolAdmitted, Bool.and_eq_true, List.all_eq_true, decide_eq_true_iff,
      List.contains_iff]
    exact ⟨⟨⟨⟨⟨h.sameId, h.validOld⟩, h.validNew⟩, h.keeps⟩, h.costLen⟩,
      fun a b hab => h.costHi (a, b) hab⟩

theorem zip_self_eq {l : List Bounds} {x : Bounds × Bounds} (hx : x ∈ l.zip l) : x.1 = x.2 := by
  induction l with
  | nil => simp at hx
  | cons a as ih =>
    rw [List.zip_cons_cons] at hx
    rcases List.mem_cons.mp hx with rfl | hx
    · rfl
    · exact ih hx

theorem SymbolAdmitted.refl {p : SymbolProfile}
    (hv : ∀ b ∈ p.costs, b.lo ≤ b.hi) : SymbolAdmitted p p where
  sameId := rfl
  validOld := hv
  validNew := hv
  keeps := fun _ hb => hb
  costLen := rfl
  costHi := by
    intro x hx
    have hxeq : x.1 = x.2 := zip_self_eq hx
    simp [hxeq]

theorem zip_rel_trans {a b c : List Bounds}
    (h1 : a.length = b.length) (h2 : b.length = c.length)
    (p1 : ∀ x ∈ a.zip b, x.2.hi ≤ x.1.hi)
    (p2 : ∀ x ∈ b.zip c, x.2.hi ≤ x.1.hi) :
    ∀ x ∈ a.zip c, x.2.hi ≤ x.1.hi := by
  intro x hx
  induction a generalizing b c x with
  | nil =>
    cases b with
    | nil =>
      cases c with
      | nil => simp at hx
      | cons _ _ => simp at h2
    | cons _ _ => simp at h1
  | cons a0 as ih =>
    cases b with
    | nil => simp at h1
    | cons b0 bs =>
      cases c with
      | nil => simp at h2
      | cons c0 cs =>
        rw [List.zip_cons_cons] at hx p1 p2
        have p1h : b0.hi ≤ a0.hi := p1 (a0, b0) (List.mem_cons.mpr (Or.inl rfl))
        have p2h : c0.hi ≤ b0.hi := p2 (b0, c0) (List.mem_cons.mpr (Or.inl rfl))
        have p1t : ∀ y ∈ as.zip bs, y.2.hi ≤ y.1.hi :=
          fun y hy => p1 y (List.mem_cons.mpr (Or.inr hy))
        have p2t : ∀ y ∈ bs.zip cs, y.2.hi ≤ y.1.hi :=
          fun y hy => p2 y (List.mem_cons.mpr (Or.inr hy))
        rcases List.mem_cons.mp hx with rfl | hx
        · exact Nat.le_trans p2h p1h
        · exact ih (by simp [List.length] at h1; exact h1)
            (by simp [List.length] at h2; exact h2) p1t p2t x hx

theorem symbolAdmitted_trans {a b c : SymbolProfile}
    (h1 : SymbolAdmitted a b) (h2 : SymbolAdmitted b c) : SymbolAdmitted a c where
  sameId := h1.sameId.trans h2.sameId
  validOld := h1.validOld
  validNew := h2.validNew
  keeps := fun beh hb => h2.keeps beh (h1.keeps beh hb)
  costLen := h1.costLen.trans h2.costLen
  costHi := zip_rel_trans h1.costLen h2.costLen h1.costHi h2.costHi

def ReleaseAdmitted (old new : Release) : Prop :=
  ∀ p ∈ old.symbols,
    match new.symbols.find? (fun q => q.id == p.id) with
    | some q => SymbolAdmitted p q
    | none => False

def releaseAdmitted (old new : Release) : Bool :=
  old.symbols.all fun p =>
    match new.symbols.find? (fun q => q.id == p.id) with
    | some q => symbolAdmitted p q
    | none => false

theorem find?_pred {α : Type} {p : α → Bool} {l : List α} {a : α}
    (h : l.find? p = some a) : p a = true := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    by_cases hp : p x
    · have hx : (x :: xs).find? p = some x := by simp [List.find?, hp]
      have ha : a = x := by
        rw [hx] at h
        exact (Option.some.inj h).symm
      simpa [ha] using hp
    · have hx : (x :: xs).find? p = xs.find? p := by simp [List.find?, hp]
      exact ih (by rw [hx] at h; exact h)

theorem mem_find? {α : Type} {p : α → Bool} {l : List α} {a : α}
    (h : l.find? p = some a) : a ∈ l := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    by_cases hp : p x
    · have hx : (x :: xs).find? p = some x := by simp [List.find?, hp]
      have ha : a = x := by
        rw [hx] at h
        exact (Option.some.inj h).symm
      simp [ha]
    · have hx : (x :: xs).find? p = xs.find? p := by simp [List.find?, hp]
      exact List.mem_cons.mpr (Or.inr (ih (by rw [hx] at h; exact h)))

theorem releaseAdmitted_iff {old new : Release} :
    releaseAdmitted old new = true ↔ ReleaseAdmitted old new := by
  constructor
  · intro h p hp
    have hp' := (List.all_eq_true.mp h) p hp
    cases hfind : new.symbols.find? (fun q => q.id == p.id) with
    | none => simp [releaseAdmitted, hfind] at hp'
    | some q =>
      simp [hfind] at hp'
      simp [hfind]
      exact (symbolAdmitted_iff).mp hp'
  · intro h
    apply List.all_eq_true.mpr
    intro p hp
    have hp' := h p hp
    cases hfind : new.symbols.find? (fun q => q.id == p.id) with
    | none => simp [hfind] at hp'
    | some q =>
      simp [hfind] at hp'
      simp [hfind]
      exact (symbolAdmitted_iff).mpr hp'

theorem releaseAdmitted_trans {a b c : Release}
    (hab : ReleaseAdmitted a b) (hbc : ReleaseAdmitted b c) : ReleaseAdmitted a c := by
  intro p hp
  have hab' := hab p hp
  cases hfind : b.symbols.find? (fun q => q.id == p.id) with
  | none => simp [hfind] at hab'
  | some q =>
    simp [hfind] at hab'
    have hq : q ∈ b.symbols := mem_find? hfind
    have hbc' := hbc q hq
    let pred : SymbolProfile → Bool := fun s => s.id == p.id
    have hfindP : b.symbols.find? pred = some q := hfind
    have htrue : pred q = true := find?_pred hfindP
    have hidq : q.id = p.id := by
      have hb : (q.id == p.id) = true := by simpa [pred] using htrue
      exact beq_iff_eq.mp hb
    cases hfind2 : c.symbols.find? (fun r => r.id == q.id) with
    | none => simp [hfind2] at hbc'
    | some r =>
      simp [hfind2] at hbc'
      have hpq : p.id = q.id := hidq.symm
      have hsame : c.symbols.find? (fun r => r.id == p.id) =
          c.symbols.find? (fun r => r.id == q.id) := by
        simp [hpq]
      simp [hsame, hfind2]
      exact symbolAdmitted_trans hab' hbc'

def firstDropped (old new : List Nat) : Option Nat :=
  old.find? fun b => !new.contains b

def firstRegressed (old new : List Bounds) : Option Nat :=
  (List.range old.length).find? fun i =>
    match old[i]?, new[i]? with
    | some a, some b => decide (b.hi > a.hi)
    | _, _ => false

def reasonOf (old new : SymbolProfile) : Reason :=
  if old.id ≠ new.id then .missingSymbol old.id
  else if old.costs.any (fun b => decide (b.lo > b.hi)) ||
      new.costs.any (fun b => decide (b.lo > b.hi)) then .invalidBounds old.id
  else if old.costs.length ≠ new.costs.length then .axisMismatch old.id
  else
    match firstDropped old.behaviors new.behaviors with
    | some b => .behaviorDropped old.id b
    | none =>
      match firstRegressed old.costs new.costs with
      | some i => .costRegressed old.id i
      | none => .missingSymbol old.id

def symbolVerdict (old new : SymbolProfile) : Verdict :=
  if symbolAdmitted old new then .admitted else .refused (reasonOf old new)

theorem symbolVerdict_admitted_iff (old new : SymbolProfile) :
    symbolVerdict old new = .admitted ↔ symbolAdmitted old new = true := by
  cases h : symbolAdmitted old new <;> simp [symbolVerdict, h]

def symbolVerdicts (old new : Release) : List (Nat × Verdict) :=
  old.symbols.map fun p =>
    match new.symbols.find? (fun q => q.id == p.id) with
    | none => (p.id, .refused (.missingSymbol p.id))
    | some q => (p.id, symbolVerdict p q)

theorem find?_eq_of_mem {l : List SymbolProfile} {p : SymbolProfile}
    (hp : p ∈ l) (hu : l.Pairwise fun a b => a.id ≠ b.id) :
    l.find? (fun q => q.id == p.id) = some p := by
  induction l with
  | nil => cases hp
  | cons a as ih =>
    simp [List.find?]
    cases hp with
    | head =>
      simp [beq_iff_eq]
    | tail _ hmem =>
      rw [List.pairwise_cons] at hu
      have hne : a.id ≠ p.id := hu.1 p hmem
      have hbeq : (a.id == p.id) = false := by
        cases h : a.id == p.id with
        | true => exact absurd (beq_iff_eq.mp h) hne
        | false => rfl
      simp [hbeq]
      exact ih hmem hu.2

theorem zip_get {l1 l2 : List Bounds} (hl : l1.length = l2.length) (i : Nat)
    (hi : i < l1.length) : (l1[i], l2[i]) ∈ l1.zip l2 := by
  induction l1 generalizing l2 i with
  | nil => simp at hi
  | cons a as ih =>
    cases l2 with
    | nil => simp at hl
    | cons b bs =>
      cases i with
      | zero => simp [List.zip]
      | succ i =>
        simp [List.zip]
        exact Or.inr (ih (by simp at hl; exact hl) i (by simp at hi; exact hi))

end SoftwareIsComposable
