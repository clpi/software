/-!
# Necessary dominance, three-valued gates, and the unresolved boundary

Proposal entries S-04 and C-03. `ThreeValuedGate` (software-optimality) already proves the
local rule: an unknown axis blocks dominance. This module proves what the rule is worth.

* `pdom_sound`: the unknown-blocking rule is sound. If it says `x` dominates `y`, then every
  completion of the missing readings agrees.
* `pdom_exact_int`: over unbounded integer costs the rule is exact. Dominance that holds in
  every completion is exactly the unknown-blocking rule.
* `pdom_strict_nat`: over costs with a least value (natural numbers) the rule is strictly
  conservative: a dominance that holds in every completion is still blocked.
* `pdom_refine`: a dominance verdict survives any refinement of the readings.
* `kept_of_frontier`: the set kept by the rule contains the exact frontier of every
  completion, and `kept_antitone` shows it only shrinks as readings arrive.
* Three-valued gates (`V`, Kleene `V.and`) agree with every completion
  (`gateLe_agrees`, `and_agrees`), and a definite verdict never flips under refinement
  (`gateLe_mono`, `and_mono`).
* `firstUnresolved_spec`: an unresolved verdict names exactly one boundary, the first
  unresolved one in priority order, with every earlier boundary passing.

Prior art: dominance under incomplete information is "necessary dominance"
(Greco, Mousseau and Slowinski 2008, robust ordinal regression; Konczak and Lang 2005 for
necessary winners). Kleene's strong three-valued logic (1938, 1952) and its monotonicity in
the information order are classical. New here is only the kernel-checked link to this
project's gate.
-/
namespace Family.Necessary

/-- A reading on each axis: `none` is unknown. Costs are smaller-is-better. -/
abbrev PVec (α κ : Type) := α → Option κ
abbrev Vec (α κ : Type) := α → κ

/-- Strict Pareto dominance on the listed axes: `x` is no worse everywhere, better somewhere. -/
def Dom {α κ : Type} [LE κ] [LT κ] (axes : List α) (x y : Vec α κ) : Prop :=
  (∀ a, a ∈ axes → x a ≤ y a) ∧ ∃ a, a ∈ axes ∧ x a < y a

/-- The unknown-blocking rule: every listed axis is known on both sides, and the known
readings dominate. -/
def PDom {α κ : Type} [LE κ] [LT κ] (axes : List α) (x y : PVec α κ) : Prop :=
  (∀ a, a ∈ axes → ∃ u v, x a = some u ∧ y a = some v ∧ u ≤ v) ∧
    ∃ a, a ∈ axes ∧ ∃ u v, x a = some u ∧ y a = some v ∧ u < v

/-- `c` fills in the unknown readings of `p` and keeps the known ones. -/
def Completes {α κ : Type} (p : PVec α κ) (c : Vec α κ) : Prop :=
  ∀ a v, p a = some v → c a = v

/-- Dominance in every completion of both sides. -/
def NDom {α κ : Type} [LE κ] [LT κ] (axes : List α) (x y : PVec α κ) : Prop :=
  ∀ cx cy, Completes x cx → Completes y cy → Dom axes cx cy

def fill {α κ : Type} (p : PVec α κ) (d : κ) : Vec α κ := fun a => (p a).getD d

theorem fill_completes {α κ : Type} (p : PVec α κ) (d : κ) : Completes p (fill p d) := by
  intro a v h
  simp [fill, h]

theorem pdom_sound {α κ : Type} [LE κ] [LT κ] (axes : List α) (x y : PVec α κ)
    (h : PDom axes x y) : NDom axes x y := by
  intro cx cy hx hy
  refine ⟨fun a ha => ?_, ?_⟩
  · obtain ⟨u, v, hu, hv, huv⟩ := h.1 a ha
    rw [hx a u hu, hy a v hv]
    exact huv
  · obtain ⟨a, ha, u, v, hu, hv, huv⟩ := h.2
    exact ⟨a, ha, by rw [hx a u hu, hy a v hv]; exact huv⟩

theorem pdom_exact_int {α : Type} (axes : List α) (x y : PVec α Int) :
    PDom axes x y ↔ NDom axes x y := by
  refine ⟨pdom_sound axes x y, fun h => ?_⟩
  -- every listed axis is known on both sides
  have known : ∀ a, a ∈ axes → (∃ u, x a = some u) ∧ ∃ v, y a = some v := by
    intro a ha
    constructor
    · cases hxa : x a with
      | some u => exact ⟨u, rfl⟩
      | none =>
        have hd := (h (fill x (fill y 0 a + 1)) (fill y 0) (fill_completes _ _)
          (fill_completes _ _)).1 a ha
        simp [fill, hxa] at hd
        omega
    · cases hya : y a with
      | some v => exact ⟨v, rfl⟩
      | none =>
        have hd := (h (fill x 0) (fill y (fill x 0 a - 1)) (fill_completes _ _)
          (fill_completes _ _)).1 a ha
        simp [fill, hya] at hd
        omega
  have hd := h (fill x 0) (fill y 0) (fill_completes _ _) (fill_completes _ _)
  refine ⟨fun a ha => ?_, ?_⟩
  · obtain ⟨⟨u, hu⟩, v, hv⟩ := known a ha
    have := hd.1 a ha
    simp [fill, hu, hv] at this
    exact ⟨u, v, hu, hv, this⟩
  · obtain ⟨a, ha, hlt⟩ := hd.2
    obtain ⟨⟨u, hu⟩, v, hv⟩ := known a ha
    simp [fill, hu, hv] at hlt
    exact ⟨a, ha, u, v, hu, hv, hlt⟩

/-- Over natural-number costs, `0` is a floor, so a known `0` beats any unknown. -/
def natX : PVec Bool Nat := fun _ => some 0
def natY : PVec Bool Nat := fun a => if a then none else some 1

theorem pdom_strict_nat :
    NDom [true, false] natX natY ∧ ¬ PDom [true, false] natX natY := by
  constructor
  · intro cx cy hx hy
    have h0 : cx true = 0 := hx true 0 rfl
    have h1 : cx false = 0 := hx false 0 rfl
    have h2 : cy false = 1 := hy false 1 rfl
    refine ⟨fun a _ => ?_, false, by simp, by omega⟩
    cases a <;> omega
  · intro h
    obtain ⟨u, v, _, hv, _⟩ := h.1 true (by simp)
    simp [natY] at hv

/-- `q` knows at least what `p` knows, and agrees with it. -/
def Refines {α κ : Type} (p q : PVec α κ) : Prop :=
  ∀ a v, p a = some v → q a = some v

theorem pdom_refine {α κ : Type} [LE κ] [LT κ] {axes : List α} {x y x' y' : PVec α κ}
    (h : PDom axes x y) (hx : Refines x x') (hy : Refines y y') : PDom axes x' y' := by
  refine ⟨fun a ha => ?_, ?_⟩
  · obtain ⟨u, v, hu, hv, huv⟩ := h.1 a ha
    exact ⟨u, v, hx a u hu, hy a v hv, huv⟩
  · obtain ⟨a, ha, u, v, hu, hv, huv⟩ := h.2
    exact ⟨a, ha, u, v, hx a u hu, hy a v hv, huv⟩

/-- Candidates kept by the rule: nothing in the list dominates them under it. -/
def Kept {α κ ι : Type} [LE κ] [LT κ] (axes : List α) (cands : List ι)
    (read : ι → PVec α κ) (x : ι) : Prop :=
  x ∈ cands ∧ ∀ y, y ∈ cands → ¬ PDom axes (read y) (read x)

/-- The exact frontier of a fully measured list. -/
def Front {α κ ι : Type} [LE κ] [LT κ] (axes : List α) (cands : List ι)
    (val : ι → Vec α κ) (x : ι) : Prop :=
  x ∈ cands ∧ ∀ y, y ∈ cands → ¬ Dom axes (val y) (val x)

/-- Whatever the unknown readings turn out to be, nothing on the true frontier was dropped. -/
theorem kept_of_frontier {α κ ι : Type} [LE κ] [LT κ] (axes : List α) (cands : List ι)
    (read : ι → PVec α κ) (val : ι → Vec α κ) (hc : ∀ i, Completes (read i) (val i))
    (x : ι) (hx : Front axes cands val x) : Kept axes cands read x :=
  ⟨hx.1, fun y hy hd => hx.2 y hy (pdom_sound axes _ _ hd (val y) (val x) (hc y) (hc x))⟩

theorem kept_antitone {α κ ι : Type} [LE κ] [LT κ] (axes : List α) (cands : List ι)
    (read read' : ι → PVec α κ) (hr : ∀ i, Refines (read i) (read' i))
    (x : ι) (hx : Kept axes cands read' x) : Kept axes cands read x :=
  ⟨hx.1, fun y hy hd => hx.2 y hy (pdom_refine hd (hr y) (hr x))⟩

/-! ## Three-valued gates -/

inductive V where
  | pass
  | fail
  | unknown
  deriving DecidableEq, Repr

/-- Kleene's strong conjunction: a failure decides, two passes pass, anything else is unknown. -/
def V.and : V → V → V
  | .fail, _ => .fail
  | _, .fail => .fail
  | .pass, .pass => .pass
  | _, _ => .unknown

/-- A definite verdict matches the two-valued answer; unknown promises nothing. -/
def Agrees (v : V) (b : Bool) : Prop :=
  (v = .pass → b = true) ∧ (v = .fail → b = false)

/-- Information order: unknown is below everything, definite verdicts only below themselves. -/
def V.le (v w : V) : Prop := v = .unknown ∨ v = w

def gateLe (x : Option Int) (budget : Int) : V :=
  match x with
  | none => .unknown
  | some u => if u ≤ budget then .pass else .fail

theorem gateLe_agrees (x : Option Int) (budget c : Int) (hc : ∀ v, x = some v → c = v) :
    Agrees (gateLe x budget) (decide (c ≤ budget)) := by
  cases x with
  | none => exact ⟨fun h => V.noConfusion h, fun h => V.noConfusion h⟩
  | some u =>
    rw [hc u rfl]
    by_cases h : u ≤ budget <;> simp [gateLe, h, Agrees]

theorem and_agrees {v w : V} {b c : Bool} (hv : Agrees v b) (hw : Agrees w c) :
    Agrees (v.and w) (b && c) := by
  obtain ⟨hv1, hv2⟩ := hv
  obtain ⟨hw1, hw2⟩ := hw
  cases v <;> cases w <;> simp_all [V.and, Agrees]

theorem gateLe_mono {x x' : Option Int} (budget : Int)
    (h : ∀ v, x = some v → x' = some v) : (gateLe x budget).le (gateLe x' budget) := by
  cases x with
  | none => exact Or.inl rfl
  | some u => rw [h u rfl]; exact Or.inr rfl

theorem and_mono {v v' w w' : V} (hv : v.le v') (hw : w.le w') : (v.and w).le (v'.and w') := by
  unfold V.le at *
  cases v <;> cases v' <;> cases w <;> cases w' <;> simp_all [V.and]

/-- A definite verdict on partial readings is already final. -/
theorem definite_final {v v' : V} (h : v.le v') (hd : v ≠ .unknown) : v' = v := by
  rcases h with h | h
  · exact absurd h hd
  · exact h.symm

/-! ## The unresolved boundary -/

/-- Boundaries in priority order, each with its verdict. -/
def overall {β : Type} : List (β × V) → V
  | [] => .pass
  | (_, v) :: rest => v.and (overall rest)

def firstUnresolved {β : Type} : List (β × V) → Option β
  | [] => none
  | (b, .unknown) :: _ => some b
  | _ :: rest => firstUnresolved rest

/-- The proposal's three boundaries, in its priority order. -/
inductive Boundary where
  | budget
  | frontier
  | rules
  deriving DecidableEq, Repr

theorem overall_fail_iff {β : Type} (bs : List (β × V)) :
    overall bs = .fail ↔ ∃ b, (b, V.fail) ∈ bs := by
  induction bs with
  | nil => simp [overall]
  | cons p rest ih =>
    obtain ⟨b, v⟩ := p
    cases v <;> cases h : overall rest <;> simp_all [overall, V.and] <;>
      first
      | exact ⟨b, Or.inl rfl⟩
      | (obtain ⟨c, hc⟩ := ih; exact ⟨c, Or.inr hc⟩)
      | (intro c hc; rcases hc with hc | hc <;> simp_all)
      | skip

/-- An unresolved overall verdict names one boundary: the first unresolved one. Every boundary
before it passed, and no boundary failed. -/
theorem firstUnresolved_spec {β : Type} (bs : List (β × V)) (h : overall bs = .unknown) :
    ∃ pre b post, bs = pre ++ (b, V.unknown) :: post ∧ (∀ p, p ∈ pre → p.2 = .pass) ∧
      firstUnresolved bs = some b ∧ ∀ c, (c, V.fail) ∉ bs := by
  induction bs with
  | nil => simp [overall] at h
  | cons p rest ih =>
    obtain ⟨b, v⟩ := p
    have nofail : ∀ c, (c, V.fail) ∉ (b, v) :: rest := by
      intro c hc
      have := (overall_fail_iff ((b, v) :: rest)).mpr ⟨c, hc⟩
      rw [h] at this
      exact V.noConfusion this
    cases v with
    | unknown => exact ⟨[], b, rest, rfl, by simp, rfl, nofail⟩
    | fail => exact absurd List.mem_cons_self (nofail b)
    | pass =>
      have hr : overall rest = .unknown := by
        cases hh : overall rest <;> simp_all [overall, V.and]
      obtain ⟨pre, c, post, he, hpre, hf, _⟩ := ih hr
      refine ⟨(b, .pass) :: pre, c, post, by simp [he], ?_, by simp [firstUnresolved, hf], nofail⟩
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · rfl
      · exact hpre q hq

example : firstUnresolved [(Boundary.budget, V.pass), (.frontier, .unknown), (.rules, .unknown)]
    = some .frontier := rfl

example : overall [(Boundary.budget, V.unknown), (.frontier, .fail), (.rules, .pass)] = .fail := rfl

end Family.Necessary
