/- Loss: a compiler that identifies two programs disagreeing on the
   qualified quotient admits no recovery map, and the forgetting compiler
   is such a compiler, by a concrete pair. -/
import Basic

namespace CompilersLoseInfo

/-- The general fact: if one artifact is shared by two sources with
    different qualified quotients, no function of the artifact returns
    every source's quotient. A recovery map would have to return two
    different values for one input. -/
theorem no_recovery_of_loss {S T Q : Type} {c : S → T} {q : S → Q}
    {s₁ s₂ : S} (himg : c s₁ = c s₂) (hqual : q s₁ ≠ q s₂) :
    ¬ Recoverable c q := by
  rintro ⟨r, hr⟩
  exact hqual (by rw [← hr s₁, himg, ← hr s₂])

/-- The two-node universe of the distinguishing pair. -/
inductive Node where
  | base
  | top
deriving DecidableEq

/-- First program: both nodes are roots. The output derives directly. -/
def direct : Hypergraph Node where
  roots := fun _ => True
  edges := fun _ _ => False

/-- Second program: the base is a root and the output derives through it.
    Same behavior as the first; different premise cone for the output. -/
def linked : Hypergraph Node where
  roots := fun a => a = Node.base
  edges := fun ps a => ps = [Node.base] ∧ a = Node.top

theorem linked_edge : linked.edges [Node.base] Node.top := ⟨rfl, rfl⟩

theorem derives_direct (a : Node) : Derives direct a :=
  Derives.root True.intro

theorem derives_linked_base : Derives linked Node.base :=
  Derives.root rfl

theorem derives_linked_top : Derives linked Node.top :=
  Derives.step linked_edge (fun p hp => by
    rw [List.mem_singleton.mp hp]
    exact derives_linked_base)

theorem derives_linked (a : Node) : Derives linked a := by
  cases a with
  | base => exact derives_linked_base
  | top => exact derives_linked_top

/-- The forgetting compiler cannot tell the pair apart: same artifact. -/
theorem forget_direct_eq_linked : forget direct = forget linked := by
  funext a
  apply propext
  constructor
  · intro _; exact derives_linked a
  · intro _; exact derives_direct a

theorem reaches_linked_base_top : Reaches linked Node.base Node.top :=
  Reaches.step ⟨[Node.base], linked_edge, by simp⟩

/-- In the first program nothing reaches anything but itself: the output
    has no premises at all. -/
theorem reaches_direct_eq {a b : Node} (h : Reaches direct a b) : a = b := by
  induction h with
  | refl => rfl
  | step he => obtain ⟨ps, hf, -⟩ := he; exact False.elim hf
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The pair disagrees on the qualified quotient: the topology differs. -/
theorem qual_direct_ne_linked : qual direct ≠ qual linked := by
  intro h
  have ht : (fun a b => Reaches direct a b) = (fun a b => Reaches linked a b) :=
    congrArg Prod.snd h
  have hcon : Reaches direct Node.base Node.top
      = Reaches linked Node.base Node.top :=
    congrFun (congrFun ht Node.base) Node.top
  have hd : Reaches direct Node.base Node.top := by
    rw [hcon]
    exact reaches_linked_base_top
  exact Node.noConfusion (reaches_direct_eq hd)

/-- Non-injectivity on the qualified quotient, stated as such: two programs
    that do not agree on the quotient share one forgetting artifact. -/
theorem forget_not_injective_on_quotient :
    ∃ g₁ g₂ : Hypergraph Node, ¬ Agree g₁ g₂ ∧ forget g₁ = forget g₂ :=
  ⟨direct, linked, qual_direct_ne_linked, forget_direct_eq_linked⟩

/-- And therefore no recovery map exists for the forgetting compiler:
    exact provenance is not a function of the conventional artifact. -/
theorem forget_no_recovery :
    ¬ Recoverable (forget (A := Node)) (qual (A := Node)) :=
  no_recovery_of_loss forget_direct_eq_linked qual_direct_ne_linked

end CompilersLoseInfo
