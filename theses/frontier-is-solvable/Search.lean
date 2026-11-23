import Frontier
import Hyper
import Std

namespace Search

open FrontierSolvable

variable {A I : Type}

def join (a b : List A) : List A := a ++ b

theorem join.mem {a b : List A} {x : A} :
    x ∈ join a b ↔ x ∈ a ∨ x ∈ b := by
  simp [join]

theorem join.comm (a b : List A) (x : A) :
    x ∈ join a b ↔ x ∈ join b a := by
  simp [join, or_comm]

theorem join.assoc (a b c : List A) (x : A) :
    x ∈ join (join a b) c ↔ x ∈ join a (join b c) := by
  simp [join, or_assoc]

theorem join.idem (a : List A) (x : A) :
    x ∈ join a a ↔ x ∈ a := by
  simp [join]

def closed (step : A → A → Prop) (s : List A) : Prop :=
  ∀ x y, x ∈ s → step x y → y ∈ s

def sat (step : A → A → Prop) (s : List A) (x : A) : Prop :=
  ∀ t : List A, s ⊆ t → closed step t → x ∈ t

theorem sat.mem {step : A → A → Prop} {s : List A} {x : A} (h : x ∈ s) :
    sat step s x :=
  fun _t ht _ => ht h

theorem sat.step {step : A → A → Prop} {s : List A} {x y : A}
    (hx : sat step s x) (h : step x y) : sat step s y :=
  fun t ht hc => hc x y (hx t ht hc) h

theorem sat.least {step : A → A → Prop} {s t : List A}
    (hsub : s ⊆ t) (hc : closed step t) {x : A} (hx : sat step s x) :
    x ∈ t :=
  hx t hsub hc

theorem sat.mono {step : A → A → Prop} {s t : List A} (h : s ⊆ t)
    {x : A} (hx : sat step s x) : sat step t x :=
  fun u hu hc => hx u (fun _y hy => hu (h hy)) hc

def lower (cost : A → I → Int) (s : List A) (i : I) (b : Int) : Prop :=
  ∀ x ∈ s, b ≤ cost x i

def glb (cost : A → I → Int) (s : List A) (i : I) (b : Int) : Prop :=
  lower cost s i b ∧ ∀ b', lower cost s i b' → b' ≤ b

def upper (cost : A → I → Int) (s : List A) (i : I) (b : Int) : Prop :=
  ∀ x ∈ s, cost x i ≤ b

def gub (cost : A → I → Int) (s : List A) (i : I) (b : Int) : Prop :=
  upper cost s i b ∧ ∀ b', upper cost s i b' → b ≤ b'

theorem glb.join (cost : A → I → Int) {a b : List A} {i : I} {ba bb : Int}
    (ha : glb cost a i ba) (hb : glb cost b i bb) :
    glb cost (join a b) i (min ba bb) := by
  constructor
  · intro x hx
    rw [join.mem] at hx
    rcases hx with hx | hx
    · exact Int.le_trans (by omega) (ha.1 x hx)
    · exact Int.le_trans (by omega) (hb.1 x hx)
  · intro b' hb'
    have h1 := ha.2 b' (fun x hx => hb' x (join.mem.mpr (Or.inl hx)))
    have h2 := hb.2 b' (fun x hx => hb' x (join.mem.mpr (Or.inr hx)))
    omega

theorem gub.join (cost : A → I → Int) {a b : List A} {i : I} {ba bb : Int}
    (ha : gub cost a i ba) (hb : gub cost b i bb) :
    gub cost (join a b) i (max ba bb) := by
  constructor
  · intro x hx
    rw [join.mem] at hx
    rcases hx with hx | hx
    · exact Int.le_trans (ha.1 x hx) (by omega)
    · exact Int.le_trans (hb.1 x hx) (by omega)
  · intro b' hb'
    have h1 := ha.2 b' (fun x hx => hb' x (join.mem.mpr (Or.inl hx)))
    have h2 := hb.2 b' (fun x hx => hb' x (join.mem.mpr (Or.inr hx)))
    omega

theorem join.lower (cost : A → I → Int) {a b : List A} {i : I} {bound : Int}
    (h : lower cost (join a b) i bound) :
    lower cost a i bound ∧ lower cost b i bound :=
  ⟨fun x hx => h x (join.mem.mpr (Or.inl hx)),
    fun x hx => h x (join.mem.mpr (Or.inr hx))⟩

theorem tighten (cost : A → I → Int) {a b : List A} {i : I} {ba bj : Int}
    (ha : glb cost a i ba) (hj : lower cost (join a b) i bj) : bj ≤ ba :=
  ha.2 bj (join.lower cost hj).1

theorem tighten.up (cost : A → I → Int) {a b : List A} {i : I} {ba bj : Int}
    (ha : gub cost a i ba) (hj : upper cost (join a b) i bj) : ba ≤ bj :=
  ha.2 bj (fun x hx => hj x (join.mem.mpr (Or.inl hx)))

theorem glb.exists (cost : A → I → Int) (i : I) :
    ∀ s : List A, s ≠ [] → ∃ b, glb cost s i b := by
  intro s
  induction s with
  | nil => intro h; exact absurd rfl h
  | cons x xs ih =>
    intro _
    cases xs with
    | nil =>
      refine ⟨cost x i, fun y hy => ?_, fun b hb => hb x (by simp)⟩
      simp at hy
      subst hy
      exact Int.le_refl _
    | cons y ys =>
      obtain ⟨b, hb1, hb2⟩ := ih (by simp)
      refine ⟨min (cost x i) b, ?_, ?_⟩
      · intro z hz
        simp at hz
        rcases hz with rfl | hz
        · omega
        · exact Int.le_trans (by omega) (hb1 z (List.mem_cons.mpr hz))
      · intro b' hb'
        have h1 := hb' x (by simp)
        have h2 := hb2 b' (fun z hz => hb' z (List.mem_cons_of_mem x hz))
        omega

def exams (s : List A) : Nat := s.length * s.length

theorem squared (a b : List A) :
    exams (join a b) = (a.length + b.length) * (a.length + b.length) := by
  simp [exams, join]

theorem finite (candidates : List A) (e : A → Bool) (d : A → A → Bool) :
    (compute candidates e d).length ≤ candidates.length := by
  have h1 : (candidates.filter e).length ≤ candidates.length :=
    List.length_filter_le _ _
  unfold compute
  exact Nat.le_trans (List.length_filter_le _ _) h1

theorem optimal (candidates : List A) (e : A → Bool) (d : A → A → Bool) :
    (∀ x, x ∈ compute candidates e d ↔
      Frontier (fun y => y ∈ candidates ∧ e y = true) (fun y x => d y x = true) x) ∧
      (compute candidates e d).length ≤ candidates.length :=
  ⟨fun x => compute_exact candidates e d x, finite candidates e d⟩

theorem join.frontier (a b : List A) (e : A → Bool) (d : A → A → Bool) (x : A) :
    x ∈ compute (join a b) e d ↔
      Frontier (fun y => (y ∈ a ∨ y ∈ b) ∧ e y = true) (fun y x => d y x = true) x := by
  refine (compute_exact (join a b) e d x).trans
    (derived_view_extensional _ _ _ _ ?_ (fun _ _ => Iff.rfl) x)
  intro y
  constructor
  · rintro ⟨hy, he⟩
    exact ⟨join.mem.mp hy, he⟩
  · rintro ⟨hy, he⟩
    exact ⟨join.mem.mpr hy, he⟩

def spec (eligible : A → Prop) (extra : List A) (x : A) : Prop :=
  eligible x ∨ x ∈ extra

theorem cone.list (eligible : A → Prop) (extra : List A) (d : A → A → Prop)
    {x : A} (h : Frontier (spec eligible extra) d x) :
    Frontier eligible d x ∨ x ∈ extra := by
  rcases h.1 with he | hx
  · exact Or.inl ⟨he, fun y hy => h.2 y (Or.inl hy)⟩
  · exact Or.inr hx

theorem discharge.list (eligible : A → Prop) (extra : List A) (d : A → A → Prop)
    (h : ∀ z ∈ extra, eligible z) (x : A) :
    Frontier (spec eligible extra) d x ↔ Frontier eligible d x := by
  refine derived_view_extensional _ _ _ _ ?_ (fun _ _ => Iff.rfl) x
  intro y
  constructor
  · intro hy
    exact hy.elim id (fun hz => h y hz)
  · intro hy
    exact Or.inl hy

theorem discharge (eligible : A → Prop) (d : A → A → Prop) {z : A}
    (hz : eligible z) (x : A) :
    Frontier (Insert eligible z) d x ↔ Frontier eligible d x := by
  refine derived_view_extensional _ _ _ _ ?_ (fun _ _ => Iff.rfl) x
  intro y
  constructor
  · intro hy
    exact hy.elim id (fun h => h ▸ hz)
  · intro hy
    exact Or.inl hy

theorem refuted (eligible : A → Prop) (d : A → A → Prop)
    (irr : ∀ x, ¬ d x x) {z x : A}
    (h : Frontier (Insert eligible z) d x) (hx : x ≠ z) :
    Frontier eligible d x := by
  rcases (insertion_exact eligible d irr z x).mp h with ⟨hf, -⟩ | ⟨hxx, -⟩
  · exact hf
  · exact absurd hxx hx

theorem qualified.seen (g : Hyper.Graph) (dial : Nat) (want : Nat → Bool)
    (v : Nat) (h : v ∈ Hyper.Paint.qualified g dial want) :
    Hyper.Paint.seen g dial v = true ∧ want v = true := by
  have hc : Hyper.Paint.color g dial want v = .intended := by
    simp only [Hyper.Paint.qualified, List.mem_filter, beq_iff_eq] at h
    exact h.2
  cases hw : want v <;> cases hs : Hyper.Paint.seen g dial v <;>
    simp [Hyper.Paint.color, Hyper.Paint.apply, hw, hs] at hc ⊢

theorem qualified.demo :
    Hyper.Paint.qualified Hyper.demo 0 Hyper.want = [0, 1] := by decide

theorem gap.absent :
    2 ∉ Hyper.Paint.qualified Hyper.demo 0 Hyper.want := by decide

def fee (x : Nat) (axis : Bool) : Int :=
  match x, axis with
  | 0, false => 1
  | 0, true => 10
  | 1, false => 10
  | 1, true => 1
  | _, _ => 0

theorem unfiltered :
    compute [0, 1, 2] (fun _ => true) (pareto [false, true] fee) = [2] := by
  decide

theorem filtered :
    compute [0, 1, 2] (fun x => x != 2) (pareto [false, true] fee) = [0, 1] := by
  decide

theorem dropped :
    compute [0, 1, 2] (fun _ => true) (pareto [false, true] fee) ≠
      compute [0, 1, 2] (fun x => x != 2) (pareto [false, true] fee) := by
  decide

def cap (s : List Nat) : List Nat := s.take 2

theorem capped :
    compute (cap ([0, 1] ++ [2])) (fun _ => true) (pareto [false, true] fee) ≠
      compute
        (compute (cap [0, 1]) (fun _ => true) (pareto [false, true] fee) ++
          compute (cap [2]) (fun _ => true) (pareto [false, true] fee))
        (fun _ => true) (pareto [false, true] fee) := by
  decide

theorem part.bound : ¬ lower fee [0, 1] true 10 := by
  intro h
  have h1 := h 1 (by decide)
  have h2 : fee 1 true = 1 := rfl
  rw [h2] at h1
  exact (by decide : ¬ (10 : Int) ≤ 1) h1

def put (w : A → Nat) (x : A) : List A → List A
  | [] => [x]
  | y :: ys => if w x ≤ w y then x :: y :: ys else y :: put w x ys

def order (w : A → Nat) : List A → List A
  | [] => []
  | x :: xs => put w x (order w xs)

theorem put.mem {w : A → Nat} {x y : A} :
    ∀ xs : List A, y ∈ put w x xs ↔ y = x ∨ y ∈ xs := by
  intro xs
  induction xs with
  | nil => simp [put]
  | cons z zs ih =>
    by_cases h : w x ≤ w z
    · have hput : put w x (z :: zs) = x :: z :: zs := by simp [put, h]
      rw [hput]
      simp only [List.mem_cons]
    · have hput : put w x (z :: zs) = z :: put w x zs := by simp [put, h]
      rw [hput]
      constructor
      · intro hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact Or.inr (List.mem_cons.mpr (Or.inl rfl))
        · rcases ih.mp hy with rfl | hy
          · exact Or.inl rfl
          · exact Or.inr (List.mem_cons.mpr (Or.inr hy))
      · intro hy
        rcases hy with rfl | hy
        · exact List.mem_cons.mpr (Or.inr (ih.mpr (Or.inl rfl)))
        · rcases List.mem_cons.mp hy with rfl | hy
          · exact List.mem_cons.mpr (Or.inl rfl)
          · exact List.mem_cons.mpr (Or.inr (ih.mpr (Or.inr hy)))

theorem order.mem {w : A → Nat} {x : A} :
    ∀ xs : List A, x ∈ order w xs ↔ x ∈ xs := by
  intro xs
  induction xs with
  | nil => simp [order]
  | cons y ys ih =>
    have h : order w (y :: ys) = put w y (order w ys) := rfl
    rw [h, put.mem]
    constructor
    · intro hx
      rcases hx with rfl | hx
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih.mp hx)
    · intro hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Or.inl rfl
      · exact Or.inr (ih.mpr hx)

theorem reorder {xs ys : List A} (h : ∀ x, x ∈ xs ↔ x ∈ ys)
    (e : A → Bool) (d : A → A → Bool) (x : A) :
    x ∈ compute xs e d ↔ x ∈ compute ys e d := by
  rw [compute_exact, compute_exact]
  exact derived_view_extensional _ _ _ _
    (fun y => ⟨fun hy => ⟨(h y).mp hy.1, hy.2⟩, fun hy => ⟨(h y).mpr hy.1, hy.2⟩⟩)
    (fun _ _ => Iff.rfl) x

theorem weighted (w : A → Nat) (xs : List A) (e : A → Bool) (d : A → A → Bool)
    (x : A) :
    x ∈ compute (order w xs) e d ↔ x ∈ compute xs e d := by
  apply reorder _ e d x
  intro y
  exact order.mem xs

theorem reweight (w w' : A → Nat) (xs : List A) (e : A → Bool)
    (d : A → A → Bool) (x : A) :
    x ∈ compute (order w xs) e d ↔ x ∈ compute (order w' xs) e d :=
  (weighted w xs e d x).trans (weighted w' xs e d x).symm

theorem full (w : A → Nat) (xs : List A) (e : A → Bool) (d : A → A → Bool)
    (x : A) :
    x ∈ compute (order w xs) e d ↔
      Frontier (fun y => y ∈ xs ∧ e y = true) (fun y x => d y x = true) x :=
  (weighted w xs e d x).trans (compute_exact xs e d x)

def trace (w : A → Nat) (xs : List A) (e : A → Bool) (d : A → A → Bool) :
    List A × List A :=
  (order w xs, compute (order w xs) e d)

theorem trace.sound (w : A → Nat) (xs : List A) (e : A → Bool) (d : A → A → Bool)
    (x : A) :
    x ∈ (trace w xs e d).2 ↔
      Frontier (fun y => y ∈ xs ∧ e y = true) (fun y x => d y x = true) x :=
  full w xs e d x

theorem order.shift :
    order (fun x : Nat => 2 - x) [0, 1] = [1, 0] ∧
      compute (order (fun x : Nat => 2 - x) [0, 1]) (fun _ => true)
        (pareto [false, true] fee) = [1, 0] ∧
      compute [0, 1] (fun _ => true) (pareto [false, true] fee) = [0, 1] := by
  decide

#print axioms join.mem
#print axioms sat.least
#print axioms glb.join
#print axioms gub.join
#print axioms tighten
#print axioms glb.exists
#print axioms optimal
#print axioms join.frontier
#print axioms cone.list
#print axioms discharge.list
#print axioms discharge
#print axioms refuted
#print axioms qualified.seen
#print axioms dropped
#print axioms capped
#print axioms part.bound
#print axioms order.mem
#print axioms reorder
#print axioms weighted
#print axioms reweight
#print axioms full
#print axioms trace.sound
#print axioms order.shift

end Search
