import Std
namespace Fuzzing

/-- Evidence summary within ONE fixed semantics, venue and cost contract. -/
structure Summary (Goal : Type) where
  covers : Goal → Prop
  cost : Nat

def Dominates (a b : Summary G) : Prop :=
  (∀ g, b.covers g → a.covers g) ∧ a.cost ≤ b.cost

def StrictlyDominates (a b : Summary G) : Prop :=
  Dominates a b ∧ (a.cost < b.cost ∨ ∃ g, a.covers g ∧ ¬ b.covers g)

def join (a b : Summary G) : Summary G :=
  ⟨fun g => a.covers g ∨ b.covers g, a.cost + b.cost⟩

def Admissible (budget : Nat) (required : G → Prop) (p : Summary G) : Prop :=
  p.cost ≤ budget ∧ ∀ g, required g → p.covers g

theorem dominates_trans {a b c : Summary G}
    (h : Dominates a b) (k : Dominates b c) : Dominates a c :=
  ⟨fun g hg => h.1 g (k.1 g hg), Nat.le_trans h.2 k.2⟩

theorem preserves_admissibility {a b : Summary G} (h : Dominates a b)
    (ok : Admissible budget required b) : Admissible budget required a :=
  ⟨Nat.le_trans h.2 ok.1, fun g hg => h.1 g (ok.2 g hg)⟩

/-- Contextual replacement for this explicitly additive cost / union coverage algebra. -/
theorem replacement {a b c : Summary G} (h : Dominates a b) :
    Dominates (join a c) (join b c) := by
  constructor
  · intro g hg
    exact hg.elim (fun hb => Or.inl (h.1 g hb)) Or.inr
  · exact Nat.add_le_add_right h.2 c.cost

/-- Positive saved cost stays strict under additive composition. Coverage-only strictness
    need not survive, since the context can cover the missing goal. -/
theorem strict_cost_replacement {a b c : Summary G} (h : Dominates a b)
    (hc : a.cost < b.cost) : StrictlyDominates (join a c) (join b c) :=
  ⟨replacement h, Or.inl (Nat.add_lt_add_right hc c.cost)⟩

/-- A certificate says a replay produces no new goal under the SAME execution contract. -/
theorem redundant_replay (a replay : Summary G)
    (cert : ∀ g, replay.covers g → a.covers g) (positive : 0 < replay.cost) :
    StrictlyDominates a (join a replay) := by
  constructor
  · exact ⟨fun g hg => hg.elim id (cert g), Nat.le_add_right _ _⟩
  · exact Or.inl (Nat.lt_add_of_pos_right positive)

/-- Deterministic execution on explicit seeds. A list is a multiset of runs, not
    a probability distribution; duplicates really incur cost. -/
def campaign (run : Seed → Summary G) : List Seed → Summary G
  | [] => ⟨fun _ => False, 0⟩
  | s :: ss => join (run s) (campaign run ss)

theorem campaign_lift (a b : Seed → Summary G)
    (h : ∀ seed, Dominates (a seed) (b seed)) (seeds : List Seed) :
    Dominates (campaign a seeds) (campaign b seeds) := by
  induction seeds with
  | nil => exact ⟨fun _ hg => hg, Nat.le_refl _⟩
  | cons s ss ih =>
    constructor
    · intro g hg
      exact hg.elim (fun hs => Or.inl ((h s).1 g hs)) (fun ht => Or.inr (ih.1 g ht))
    · exact Nat.add_le_add (h s).2 ih.2

/-- Equal-cost, equal-seed replay is provably redundant only if the summary itself
    is deterministic and qualifications carry no fresh-sample/count requirement. -/
theorem duplicate_seed (run : Seed → Summary G) (s : Seed)
    (positive : 0 < (run s).cost) :
    StrictlyDominates (run s) (join (run s) (run s)) :=
  redundant_replay _ _ (fun _ h => h) positive

/-- Finite comparison key: policy/semantics, venue, workload and cost units.
    In production these IDs must be authenticated commitments, not submitter guesses. -/
structure Contract where
  semantics : Nat
  venue : Nat
  workload : Nat
  units : Nat
  deriving DecidableEq, Repr

def Comparable (a b : Contract) : Bool := decide (a = b)
theorem comparable_iff (a b : Contract) : Comparable a b = true ↔ a = b := by
  simp [Comparable]

#print axioms campaign_lift
#print axioms redundant_replay
#print axioms strict_cost_replacement
end Fuzzing
