/-
  Standing control (audited 2026-11-22). Link 1 audit: "the frontier is derived from the hypergraph".
  Audited at pins: software-frontier-is-solvable c7ffc6d03e8b (Frontier.lean),
        software-optimality af23f5d27990 (HypergraphIncremental.lean).
  Both are IMPORTED here, not mirrored. In this repo it builds against the
  dependency revisions pinned in lakefile.lean.

  The map.  Candidates `C`, atoms `A`, `qual : C → A` names the
  qualification atom of each candidate.  A hypergraph state `g`
  determines eligibility `view qual g c := derives g (qual c)`, and the
  derived frontier is `Frontier (view qual g) (Dominates cost)`.
-/
import Frontier
import HypergraphIncremental

open FrontierSolvable HypergraphIncremental

namespace FrontierLinks
variable {A C I : Type}

def view (qual : C → A) (g : Hypergraph A) (c : C) : Prop := derives g (qual c)

def F (qual : C → A) (cost : C → I → Int) (g : Hypergraph A) (c : C) : Prop :=
  Frontier (view qual g) (Dominates cost) c

/-- Append order on hypergraph states: roots and edges only grow. -/
def Extends (g g' : Hypergraph A) : Prop :=
  (∀ a, g.roots a → g'.roots a) ∧ (∀ ps a, g.edges ps a → g'.edges ps a)

theorem view_mono {qual : C → A} {g g' : Hypergraph A} (h : Extends g g') (c : C) :
    view qual g c → view qual g' c :=
  Qualification.monotone h.1 h.2 (qual c)

/-! ## Set-insertion and set-retraction (the general equations) -/

/-- Growing eligibility from `e` to `e' ⊇ e` updates the frontier by the
    set form of `insertion_exact`: Δ := e' \ e. -/
theorem frontier_grow {e e' : C → Prop} (d : C → C → Prop)
    (sub : ∀ x, e x → e' x) (x : C) :
    Frontier e' d x ↔
      (Frontier e d x ∧ ∀ z, e' z → ¬ e z → ¬ d z x) ∨
      (e' x ∧ ¬ e x ∧ ∀ y, e' y → ¬ d y x) := by
  classical
  constructor
  · rintro ⟨hx, hn⟩
    by_cases he : e x
    · exact Or.inl ⟨⟨he, fun y hy => hn y (sub y hy)⟩, fun z hz _ => hn z hz⟩
    · exact Or.inr ⟨hx, he, hn⟩
  · rintro (⟨⟨he, hn⟩, hz⟩ | ⟨hx, _, hn⟩)
    · refine ⟨sub x he, fun y hy => ?_⟩
      by_cases hey : e y
      · exact hn y hey
      · exact hz y hy hey
    · exact ⟨hx, hn⟩

/-- Shrinking eligibility from `e` to `e' ⊆ e` is exactly the repo's
    `retraction_exact` with `removed := ¬ e'`. -/
theorem frontier_shrink {e e' : C → Prop} (d : C → C → Prop)
    (sub : ∀ x, e' x → e x) (x : C) :
    Frontier e' d x ↔ e x ∧ e' x ∧ ∀ y, e y → d y x → ¬ e' y := by
  classical
  have hv : ∀ y, e' y ↔ Retract e (fun z => ¬ e' z) y := fun y =>
    ⟨fun h => ⟨sub y h, Classical.not_not.mpr h⟩, fun h => Classical.not_not.mp h.2⟩
  rw [derived_view_extensional e' (Retract e (fun z => ¬ e' z)) d d hv (fun _ _ => Iff.rfl) x,
      retraction_exact]
  simp only [Classical.not_not]

/-! ## DERIVABLE: the commuting theorems under the correct map -/

/-- Append commutes with the set-insertion update, Δ = newly derived. -/
theorem append_commutes (qual : C → A) (cost : C → I → Int)
    {g g' : Hypergraph A} (h : Extends g g') (x : C) :
    F qual cost g' x ↔
      (F qual cost g x ∧ ∀ z, view qual g' z → ¬ view qual g z → ¬ Dominates cost z x) ∨
      (view qual g' x ∧ ¬ view qual g x ∧ ∀ y, view qual g' y → ¬ Dominates cost y x) :=
  frontier_grow _ (view_mono h) x

/-- The repo's single-identity `insertion_exact` is the commuting square
    exactly when the append newly derives one qualification and nothing
    else.  That hypothesis is where the naive map fails. -/
theorem single_insert_commutes (qual : C → A) (cost : C → I → Int)
    {g g' : Hypergraph A} (z : C) (hΔ : ∀ c, view qual g' c ↔ Insert (view qual g) z c)
    (x : C) :
    F qual cost g' x ↔
      (F qual cost g x ∧ ¬ Dominates cost z x) ∨
      (x = z ∧ ∀ y, view qual g y → ¬ Dominates cost y z) := by
  rw [F, derived_view_extensional _ _ _ _ hΔ (fun _ _ => Iff.rfl) x]
  exact insertion_exact _ _ (dominates_irrefl cost) z x

/-- Withdrawal (optimality's `liveRoots`/`liveRules`) commutes with the
    repo's retraction equation, `removed := ¬ view g'`. -/
theorem withdraw_commutes (qual : C → A) (cost : C → I → Int) (g : Hypergraph A)
    (w : A → Prop) (dead : List A → A → Prop) (x : C) :
    let g' : Hypergraph A := ⟨Qualification.liveRoots g.roots w, Qualification.liveRules g.edges dead⟩
    F qual cost g' x ↔
      view qual g x ∧ view qual g' x ∧
        ∀ y, view qual g y → Dominates cost y x → ¬ view qual g' y := by
  intro g'
  exact frontier_shrink _
    (fun c h => Qualification.withdrawal_no_new_support g.roots w g.edges dead (qual c) h) x

/-! ## FALSE: the naive map (event ↦ one repo update on the touched candidate) -/

/- Smallest witness: atoms 1 (qual a) and 2 (qual b), one edge [1] → 2,
   b strictly better than a.  g0 has no roots; g1 adds root 1. -/
def qualB : Bool → Nat | false => 1 | true => 2
def costB : Bool → Unit → Int | false, _ => 1 | true, _ => 0
def g0 : Hypergraph Nat := ⟨fun _ => False, fun ps a => ps = [1] ∧ a = 2⟩
def g1 : Hypergraph Nat := ⟨fun a => a = 1, fun ps a => ps = [1] ∧ a = 2⟩

theorem g0_empty (c : Bool) : ¬ view qualB g0 c := by
  intro h
  exact Qualification.least (X := fun _ => False) (fun _ hb => hb)
    (fun ps a hr hp => by obtain ⟨rfl, -⟩ := hr; exact hp 1 (List.mem_singleton.mpr rfl))
    _ h

theorem g1_a : view qualB g1 false := Qualification.Derives.root rfl
theorem g1_b : view qualB g1 true :=
  Qualification.Derives.step (ps := [1]) ⟨rfl, rfl⟩
    (fun p hp => by rw [List.mem_singleton.mp hp]; exact Qualification.Derives.root rfl)

theorem b_dom_a : Dominates costB true false :=
  ⟨fun u => by cases u; decide, ⟨(), by decide⟩⟩

/-- Naive insertion: appending root 1 is read as "insert candidate a".
    The repo's update says a enters the frontier; the derived frontier
    says a is dominated by b, which the same append also qualified. -/
theorem naive_insert_breaks :
    Frontier (Insert (view qualB g0) false) (Dominates costB) false ∧
    ¬ F qualB costB g1 false := by
  refine ⟨⟨Or.inr rfl, fun y hy hd => ?_⟩, fun hf => hf.2 true g1_b b_dom_a⟩
  rcases hy with hy | rfl
  · exact g0_empty y hy
  · exact dominates_irrefl costB false hd

/-- Naive retraction: withdrawing root 1 is read as "retract candidate a".
    The repo's update leaves b on the frontier; the derived frontier is
    empty because b was supported only through a. -/
theorem naive_retract_breaks :
    Frontier (Retract (view qualB g1) (fun c => c = false)) (Dominates costB) true ∧
    ¬ F qualB costB g0 true := by
  refine ⟨⟨⟨g1_b, by decide⟩, fun y hy hd => ?_⟩, fun hf => g0_empty true hf.1⟩
  cases y
  · exact hy.2 rfl
  · exact dominates_irrefl costB true hd

/-! ## FALSE: costs derived from the hypergraph (the repo fixes `cost`) -/

/- Atom 0 = qual a, 1 = qual b, 2 = "b measured fast".  The append adds root 2:
   eligibility does not change, cost does. -/
def qualC : Bool → Nat | false => 0 | true => 1
noncomputable def costOf (g : Hypergraph Nat) : Bool → Unit → Int := fun c _ => by
  classical
  exact if c = true ∧ derives g 2 then 0 else 1
def h0 : Hypergraph Nat := ⟨fun a => a = 0 ∨ a = 1, fun _ _ => False⟩
def h1 : Hypergraph Nat := ⟨fun a => a = 0 ∨ a = 1 ∨ a = 2, fun _ _ => False⟩

theorem h0_no2 : ¬ derives h0 2 := by
  intro h
  exact Qualification.least (X := fun a => a = 0 ∨ a = 1) (fun _ hb => hb)
    (fun _ _ hr _ => False.elim hr) 2 h |>.elim (by decide) (by decide)

theorem cost_change_breaks :
    -- what the repo's equations say: nothing became eligible, frontier keeps a
    Frontier (Insert (view qualC h0) true) (Dominates (costOf h0)) false ∧
    -- what the hypergraph says after the append: a is dominated
    ¬ Frontier (view qualC h1) (Dominates (costOf h1)) false := by
  have c0 : ∀ c, costOf h0 c () = 1 := by
    intro c; simp [costOf, h0_no2]
  have d1 : derives h1 2 := Qualification.Derives.root (Or.inr (Or.inr rfl))
  constructor
  · refine ⟨Or.inl (Qualification.Derives.root (Or.inl rfl)), fun y _ hd => ?_⟩
    obtain ⟨_, ⟨⟩, hlt⟩ := hd
    rw [c0, c0] at hlt
    exact Int.lt_irrefl _ hlt
  · intro hf
    apply hf.2 true (Qualification.Derives.root (Or.inr (Or.inl rfl)))
    refine ⟨fun _ => ?_, (), ?_⟩ <;> simp [costOf, d1]

/-! ## Append-only log with retraction atoms (the canonical-model reading) -/

/-- If eligibility is `q ∧ ¬ r` with `q ⊆ q'` and `r ⊆ r'` (both derived,
    so monotone in the log), one append is INSERT-THEN-RETRACT, and the
    retraction set must be the whole `r'`, not only the new retractions. -/
theorem append_only_step {q q' r r' : C → Prop}
    (hq : ∀ x, q x → q' x) (hr : ∀ x, r x → r' x) (x : C) :
    (q' x ∧ ¬ r' x) ↔ (((q x ∧ ¬ r x) ∨ (q' x ∧ ¬ q x)) ∧ ¬ r' x) := by
  classical
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    by_cases hqx : q x
    · exact Or.inl ⟨hqx, fun h => h2 (hr x h)⟩
    · exact Or.inr ⟨h1, hqx⟩
  · rintro ⟨(⟨h, _⟩ | ⟨h, _⟩), h2⟩
    · exact ⟨hq x h, h2⟩
    · exact ⟨h, h2⟩

/-- Order matters: retract-then-insert is wrong when one append both
    qualifies and retracts the same candidate. -/
example : let q' : Bool → Prop := fun c => c = true
          let r' : Bool → Prop := fun c => c = true
          let e  : Bool → Prop := fun _ => False
          -- retract-then-insert says eligible
          (FrontierSolvable.Insert (Retract e r') true true) ∧
          -- the log says not eligible
          ¬ (q' true ∧ ¬ r' true) := by
  simp [FrontierSolvable.Insert, Retract]

/-- Retracting only the newly retracted set is wrong: c was retracted
    earlier, its qualification arrives later. -/
example : let q : Bool → Prop := fun _ => False
          let q' : Bool → Prop := fun c => c = true
          let r : Bool → Prop := fun c => c = true
          let r' : Bool → Prop := fun c => c = true
          let newR : Bool → Prop := fun c => r' c ∧ ¬ r c
          (Retract (fun c => (q c ∧ ¬ r c) ∨ (q' c ∧ ¬ q c)) newR true) ∧
          ¬ (q' true ∧ ¬ r' true) := by
  simp [Retract]

end FrontierLinks

#print axioms FrontierLinks.frontier_grow
#print axioms FrontierLinks.frontier_shrink
#print axioms FrontierLinks.append_commutes
#print axioms FrontierLinks.single_insert_commutes
#print axioms FrontierLinks.withdraw_commutes
#print axioms FrontierLinks.naive_insert_breaks
#print axioms FrontierLinks.naive_retract_breaks
#print axioms FrontierLinks.cost_change_breaks
#print axioms FrontierLinks.append_only_step
