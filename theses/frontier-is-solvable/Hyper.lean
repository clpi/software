import Std

namespace Hyper

def code (t h : Bool) : Int :=
  match t, h with
  | true, true => 3
  | true, false => 2
  | false, true => 1
  | false, false => 0

theorem codetail (t h : Bool) : (code t h == 2 || code t h == 3) = t := by
  cases t <;> cases h <;> rfl

theorem codehead (t h : Bool) : (code t h == 1 || code t h == 3) = h := by
  cases t <;> cases h <;> rfl

@[ext] structure Graph where
  states : Nat
  nedges : Nat
  tail : Nat → Nat → Bool
  head : Nat → Nat → Bool
  eclass : Nat → Nat
  need : Nat → Nat

def matrix (g : Graph) (v e : Nat) : Int :=
  if e < g.nedges ∧ v < g.states then
    code (g.tail e v) (g.head e v)
  else if e < g.nedges ∧ v = g.states then
    (g.eclass e : Int)
  else if e < g.nedges ∧ v = g.states + 1 then
    (g.need e : Int)
  else
    0

def decode (states nedges : Nat) (entry : Nat → Nat → Int) : Graph where
  states := states
  nedges := nedges
  tail e v :=
    if e < nedges ∧ v < states then entry v e == 2 || entry v e == 3 else false
  head e v :=
    if e < nedges ∧ v < states then entry v e == 1 || entry v e == 3 else false
  eclass e := if e < nedges then (entry states e).toNat else 0
  need e := if e < nedges then (entry (states + 1) e).toNat else 0

def bounded (g : Graph) : Prop :=
  (∀ e v, g.nedges ≤ e ∨ g.states ≤ v → g.tail e v = false ∧ g.head e v = false) ∧
  (∀ e, g.nedges ≤ e → g.eclass e = 0 ∧ g.need e = 0)

theorem outside (nedges states e v : Nat) (h : ¬ (e < nedges ∧ v < states)) :
    nedges ≤ e ∨ states ≤ v := by
  by_cases he : e < nedges
  · have hv : ¬ v < states := by
      intro hv
      exact h ⟨he, hv⟩
    exact Or.inr ((Nat.not_lt).mp hv)
  · exact Or.inl ((Nat.not_lt).mp he)

theorem roundtrip (g : Graph) (hb : bounded g) :
    decode g.states g.nedges (matrix g) = g := by
  rcases g with ⟨states, nedges, tail, head, eclass, need⟩
  rcases hb with ⟨hsupp, hzero⟩
  let g0 : Graph := ⟨states, nedges, tail, head, eclass, need⟩
  have hinside : ∀ e v, e < nedges → v < states → matrix g0 v e = code (tail e v) (head e v) := by
    intro e v he hv
    simp [matrix, g0, he, hv]
  have hclass : ∀ e, e < nedges → matrix g0 states e = (eclass e : Int) := by
    intro e he
    have hnot : ¬ (e < nedges ∧ states < states) := by
      intro h
      exact Nat.lt_irrefl _ h.2
    simp [matrix, g0, he, hnot]
  have hneedrow : ∀ e, e < nedges → matrix g0 (states + 1) e = (need e : Int) := by
    intro e he
    show (if e < nedges ∧ states + 1 < states then
        code (tail e (states + 1)) (head e (states + 1))
      else if e < nedges ∧ states + 1 = states then (eclass e : Int)
      else if e < nedges ∧ states + 1 = states + 1 then (need e : Int) else 0) = _
    have h1 : ¬ (e < nedges ∧ states + 1 < states) := by intro h; omega
    have h2 : ¬ (e < nedges ∧ states + 1 = states) := by intro h; omega
    rw [if_neg h1, if_neg h2, if_pos ⟨he, rfl⟩]
  refine Graph.ext rfl rfl ?tail ?head ?eclass ?need
  · funext e v
    simp only [decode]
    by_cases h : e < nedges ∧ v < states
    · rw [if_pos h, hinside e v h.1 h.2]
      exact codetail (tail e v) (head e v)
    · rw [if_neg h]
      exact Eq.symm (hsupp e v (outside nedges states e v h)).1
  · funext e v
    simp only [decode]
    by_cases h : e < nedges ∧ v < states
    · rw [if_pos h, hinside e v h.1 h.2]
      exact codehead (tail e v) (head e v)
    · rw [if_neg h]
      exact Eq.symm (hsupp e v (outside nedges states e v h)).2
  · funext e
    simp only [decode]
    by_cases he : e < nedges
    · rw [if_pos he, hclass e he, Int.toNat_ofNat]
    · rw [if_neg he]
      exact Eq.symm (hzero e ((Nat.not_lt).mp he)).1
  · funext e
    simp only [decode]
    by_cases he : e < nedges
    · rw [if_pos he, hneedrow e he, Int.toNat_ofNat]
    · rw [if_neg he]
      exact Eq.symm (hzero e ((Nat.not_lt).mp he)).2

namespace Observed

def mask (g : Graph) (dial : Nat) : Graph where
  states := g.states
  nedges := g.nedges
  tail e v := if g.need e ≤ dial then g.tail e v else false
  head e v := if g.need e ≤ dial then g.head e v else false
  eclass := g.eclass
  need := g.need

theorem subset (g : Graph) (dial e v : Nat) :
    ((mask g dial).tail e v = true → g.tail e v = true) ∧
    ((mask g dial).head e v = true → g.head e v = true) := by
  constructor
  · intro h
    by_cases hk : g.need e ≤ dial
    · simpa [mask, hk] using h
    · simp [mask, hk] at h
  · intro h
    by_cases hk : g.need e ≤ dial
    · simpa [mask, hk] using h
    · simp [mask, hk] at h

theorem monotone (g : Graph) {d1 d2 : Nat} (hd : d1 ≤ d2) (e v : Nat) :
    ((mask g d1).tail e v = true → (mask g d2).tail e v = true) ∧
    ((mask g d1).head e v = true → (mask g d2).head e v = true) := by
  constructor
  · intro h
    by_cases hk : g.need e ≤ d1
    · have hk2 : g.need e ≤ d2 := Nat.le_trans hk hd
      simpa [mask, hk, hk2] using h
    · simp [mask, hk] at h
  · intro h
    by_cases hk : g.need e ≤ d1
    · have hk2 : g.need e ≤ d2 := Nat.le_trans hk hd
      simpa [mask, hk, hk2] using h
    · simp [mask, hk] at h

end Observed

namespace Paint

inductive Color where
  | intended
  | stray
  | gap
  | unknown
  deriving DecidableEq, Repr

def meant (color : Color) : Bool :=
  match color with
  | .intended => true
  | .stray => false
  | .gap => false
  | .unknown => false

theorem unknown : meant .unknown = false := rfl

def apply (want see : Bool) : Color :=
  match want, see with
  | true, true => .intended
  | false, true => .stray
  | true, false => .gap
  | false, false => .unknown

def seen (g : Graph) (dial v : Nat) : Bool :=
  (List.range g.nedges).any fun e =>
    (Observed.mask g dial).tail e v || (Observed.mask g dial).head e v

def color (g : Graph) (dial : Nat) (want : Nat → Bool) (v : Nat) : Color :=
  apply (want v) (seen g dial v)

theorem total (g : Graph) (dial : Nat) (want : Nat → Bool) (v : Nat) :
    color g dial want v = .intended ∨ color g dial want v = .stray ∨
      color g dial want v = .gap ∨ color g dial want v = .unknown := by
  cases hw : want v <;> cases hs : seen g dial v <;>
    simp [color, apply, hw, hs]

def qualified (g : Graph) (dial : Nat) (want : Nat → Bool) : List Nat :=
  (List.range g.states).filter fun v => color g dial want v == .intended

theorem qualifiedmeant (g : Graph) (dial : Nat) (want : Nat → Bool) (v : Nat)
    (h : v ∈ qualified g dial want) : meant (color g dial want v) = true := by
  simp only [qualified, List.mem_filter, beq_iff_eq] at h
  rw [h.2]
  rfl

end Paint

def demo : Graph where
  states := 4
  nedges := 2
  tail e v := (e == 0 && v == 0) || (e == 1 && v == 1)
  head e v := (e == 0 && v == 1) || (e == 1 && v == 2)
  eclass e := if e == 0 then 7 else if e == 1 then 8 else 0
  need e := if e == 0 then 0 else if e == 1 then 1 else 0

theorem demobounded : bounded demo := by
  constructor
  · intro e v h
    simp only [demo] at h ⊢
    rcases h with he | hv
    · have h0 : (e == 0) = false := by rw [beq_eq_false_iff_ne]; omega
      have h1 : (e == 1) = false := by rw [beq_eq_false_iff_ne]; omega
      simp [h0, h1]
    · have h0 : (v == 0) = false := by rw [beq_eq_false_iff_ne]; omega
      have h1 : (v == 1) = false := by rw [beq_eq_false_iff_ne]; omega
      have h2 : (v == 2) = false := by rw [beq_eq_false_iff_ne]; omega
      simp [h0, h1, h2]
  · intro e he
    simp only [demo] at he ⊢
    have h0 : (e == 0) = false := by rw [beq_eq_false_iff_ne]; omega
    have h1 : (e == 1) = false := by rw [beq_eq_false_iff_ne]; omega
    simp [h0, h1]

theorem demoround : decode demo.states demo.nedges (matrix demo) = demo :=
  roundtrip demo demobounded

def want (v : Nat) : Bool := decide (v = 0 ∨ v = 1 ∨ v = 2)

end Hyper
