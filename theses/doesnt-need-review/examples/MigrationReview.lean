import Std

namespace MigrationReview

-- CI reports tests and whether the patch drops a column. The migration owner
-- also knows whether old readers still use it.
structure Report where
  testsPass : Bool
  dropsColumn : Bool
  deriving Repr

def policy (r : Report) (retired : Bool) :=
  r.testsPass && (!r.dropsColumn || retired)

-- A sound automator may only return a verdict shared by every compatible world.
def sound (f : Report → Option Bool) :=
  ∀ r v, f r = some v → ∀ retired, policy r retired = v

def triage (r : Report) : Option Bool :=
  if !r.testsPass then some false
  else if r.dropsColumn then none else some true

theorem triage_sound : sound triage := by
  intro ⟨tests,drop⟩ v hv retired
  cases tests <;> cases drop <;> simp_all [policy,triage]

theorem review_exactly_when_needed (r : Report) :
    triage r = none ↔ policy r false ≠ policy r true := by
  rcases r with ⟨tests,drop⟩
  cases tests <;> cases drop <;> decide

theorem minimal_escalation (f : Report → Option Bool) (hf : sound f)
    (r : Report) (h : triage r = none) : f r = none := by
  cases he : f r with
  | none => rfl
  | some v =>
    exact False.elim ((review_exactly_when_needed r).mp h
      ((hf r v he false).trans (hf r v he true).symm))

def batch : List Report :=
  [⟨true,false⟩, ⟨false,false⟩, ⟨true,true⟩, ⟨false,true⟩, ⟨true,false⟩, ⟨true,true⟩]
def manual := batch.filter (fun r => (triage r).isNone)

theorem before_after : batch.length = 6 ∧ manual.length = 2 ∧
    policy ⟨true,true⟩ false ≠ policy ⟨true,true⟩ true := by decide

#eval (batch.length, manual.length, batch.map triage)
#print axioms triage_sound
#print axioms minimal_escalation
#print axioms before_after
end MigrationReview
