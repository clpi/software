import Fuzzing
namespace Fuzzing.Tests

def one : Summary Nat := ⟨fun g => g = 7, 1⟩
def expensive : Summary Nat := ⟨fun g => g = 7, 4⟩
def empty : Summary Nat := ⟨fun _ => False, 0⟩

theorem saved_three : StrictlyDominates one expensive := by
  exact ⟨⟨fun _ h => h, by decide⟩, Or.inl (by decide)⟩
example : Admissible 1 (fun g => g = 7) one := ⟨by decide, fun _ h => h⟩
example : ¬ Admissible 1 (fun g => g = 7) expensive := by
  intro h; have := h.1; contradiction
example : ¬ Dominates empty one := by
  intro h; exact h.1 7 rfl
example : StrictlyDominates one (join one one) := duplicate_seed (fun (_ : Unit) => one) () (by decide)
example : (campaign (fun (_ : Nat) => one) [4,4,4]).cost = 3 := by decide
example : (campaign (fun (_ : Nat) => one) [4,4,4]).covers 7 := Or.inl rfl
example : ¬ (campaign (fun (_ : Nat) => one) [4,4,4]).covers 8 := by
  simp [campaign, join, one]
example : Comparable ⟨1,2,3,4⟩ ⟨1,2,3,4⟩ = true := by decide
example : Comparable ⟨1,2,3,4⟩ ⟨2,2,3,4⟩ = false := by decide
example : Comparable ⟨1,2,3,4⟩ ⟨1,3,3,4⟩ = false := by decide
example : Comparable ⟨1,2,3,4⟩ ⟨1,2,4,4⟩ = false := by decide
example : Comparable ⟨1,2,3,4⟩ ⟨1,2,3,5⟩ = false := by decide

/-- Fully specified three-world oracle. Probe discloses the world; a hit discovers
    the goal iff its argument matches. Each query costs one. No real-world
    oracle availability or cost is inferred from this finite model. -/
inductive Query where
  | probe
  | hit (target : Fin 3)
  deriving DecidableEq

def response (world : Fin 3) : Query → Option (Fin 3)
  | .probe => some world
  | .hit _ => none

def found (world : Fin 3) : Query → Bool
  | .probe => false
  | .hit t => decide (world = t)

def adaptiveNext : Option (Fin 3) → Query
  | some t => .hit t
  | none => .hit 0

def adaptiveFound (world : Fin 3) : Bool :=
  found world .probe || found world (adaptiveNext (response world .probe))

def query (i : Fin 4) : Query :=
  if h : i.val < 3 then .hit ⟨i.val, h⟩ else .probe

def fixedFound (world : Fin 3) (a b : Fin 4) : Bool :=
  found world (query a) || found world (query b)

theorem adaptive_all_worlds : ∀ world : Fin 3, adaptiveFound world = true := by decide
/-- Every fixed two-query plan misses a world, even though feedback succeeds
    within the same two-query budget. Refutes blanket fixed-over-adaptive superiority. -/
theorem fixed_two_misses : ∀ a b : Fin 4, ∃ world : Fin 3,
    fixedFound world a b = false := by
  have finiteCheck : ∀ a b : Fin 4, fixedFound 0 a b = false ∨
      fixedFound 1 a b = false ∨ fixedFound 2 a b = false := by decide
  intro a b
  rcases finiteCheck a b with h | h | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩
  · exact ⟨2, h⟩

/-- Conversely an already justified target eliminates the probe's positive cost. -/
def adaptiveSummary (world : Fin 3) : Summary Unit :=
  ⟨fun _ => adaptiveFound world = true, 2⟩
def knownTargetSummary (world : Fin 3) : Summary Unit :=
  ⟨fun _ => found world (.hit world) = true, 1⟩
theorem known_target_dominates (world : Fin 3) :
    StrictlyDominates (knownTargetSummary world) (adaptiveSummary world) := by
  exact ⟨⟨fun _ _ => by simp [knownTargetSummary, found], by simp [knownTargetSummary, adaptiveSummary]⟩, Or.inl (by simp [knownTargetSummary, adaptiveSummary])⟩

/-- Changed evidence requirements make replay valuable: a new independent sample
    is a distinct goal, unlike duplicate_seed's fixed deterministic summary. -/
def sample (n : Nat) : Summary Nat := ⟨fun g => g = n, 1⟩
theorem fresh_sample_not_redundant : ¬ Dominates (sample 0) (join (sample 0) (sample 1)) := by
  intro h
  have bad : (1 : Nat) = 0 := h.1 1 (Or.inr rfl)
  contradiction

/-- Coverage strictness can vanish in context; only the cost-strict replacement
    theorem promises strictness survives arbitrary contexts in this algebra. -/
example : StrictlyDominates (⟨fun _ : Unit => True, 0⟩ : Summary Unit) (⟨fun _ => False, 0⟩ : Summary Unit) :=
  ⟨⟨fun _ h => h.elim, by decide⟩, Or.inr ⟨(), trivial, fun h => h⟩⟩

#print axioms adaptive_all_worlds
#print axioms fixed_two_misses
#print axioms known_target_dominates
#print axioms fresh_sample_not_redundant
end Fuzzing.Tests
