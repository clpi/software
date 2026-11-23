import SoftwareIsComposable.Composition

namespace ReleasePartition
open SoftwareIsComposable

-- Checkout → invoice → tax. Search → index. These are all modeled calls.
def call (a b : Nat) : Call := ⟨a,b,0,1⟩
def calls := [call 0 1, call 1 2, call 3 4]
def services := [0,1,2,3,4]
def component (s : Nat) := if s < 3 then 0 else 1
def rebuild (partition : Nat → Nat) := services.filter (fun s => partition s == partition 0)

theorem closed : InteractionClosed component calls := by
  intro c h
  simp [calls] at h
  rcases h with rfl | rfl | rfl <;> decide

theorem least_checkout_block (p : Nat → Nat) (h : InteractionClosed p calls) :
    ∀ s ∈ rebuild component, s ∈ rebuild p := by
  have hi : p 0 = p 1 := h (call 0 1) (by simp [calls])
  have ht : p 1 = p 2 := h (call 1 2) (by simp [calls])
  intro s hs
  change s ∈ [0,1,2] at hs
  simp at hs
  rcases hs with rfl | rfl | rfl <;> simp [rebuild, services, hi, ht]

theorem preserves_linked_check (exports : Nat → Nat) (release : Release) :
    composeRelease calls component exports true release =
      composeRelease calls component exports false release :=
  compose_stub calls component exports closed release

def profiles : Release := ⟨services.map (fun id => ⟨id,[0],[⟨1,1⟩]⟩)⟩
def taxChanged (s : Nat) := if s = 2 then 2 else 1
def gate (p : Nat → Nat) (stub : Bool) :=
  releaseAdmitted (composeRelease calls p (fun _ => 1) stub profiles)
                  (composeRelease calls p taxChanged stub profiles)

theorem before_after : rebuild (fun _ => 0) = [0,1,2,3,4] ∧
    rebuild component = [0,1,2] ∧ gate id true = true ∧
    gate id false = false ∧ gate component true = false := by decide

#eval (rebuild (fun _ => 0), rebuild component, gate id true, gate component true)
#print axioms least_checkout_block
#print axioms preserves_linked_check
#print axioms before_after
end ReleasePartition
