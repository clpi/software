import Traceability

namespace ReturnControls

open Traceability

/-- Two complete premise sets sharing one head. -/
def noPremises : Derivation Bool := ⟨fun _ => false, false⟩
def onePremise : Derivation Bool := ⟨fun n => !n, false⟩

/-- A legal lifting can record a head without recording any derivation. -/
def nodeOnly (_ : Unit) : Graph Bool :=
  ⟨fun n => !n, fun _ => false⟩

theorem head_without_derivation :
    (fold nodeOnly [()]).nodes noPremises.head = true ∧
    (fold nodeOnly [()]).edges noPremises = false := by decide

/-- Deleting the contribution premise from the old claim is false. -/
theorem head_only_claim_fails :
    ¬ (∀ (lift : Unit → Graph Bool) (l : List Unit) (d : Derivation Bool),
      (fold lift l).nodes d.head = true → (fold lift l).edges d = true) := by
  intro claim
  have bad := claim nodeOnly [()] noPremises head_without_derivation.1
  rw [head_without_derivation.2] at bad
  exact Bool.false_ne_true bad

/-- The node and derivation faces are independent in the generic model. -/
def edgeOnly (_ : Unit) : Graph Bool :=
  ⟨fun _ => false, fun _ => true⟩

theorem derivation_without_head :
    (fold edgeOnly [()]).edges noPremises = true ∧
    (fold edgeOnly [()]).nodes noPremises.head = false := by decide

/-- A recorded derivation does not imply its head is on the node face. -/
theorem edge_implies_head_claim_fails :
    ¬ (∀ (lift : Unit → Graph Bool) (l : List Unit) (d : Derivation Bool),
      (fold lift l).edges d = true → (fold lift l).nodes d.head = true) := by
  intro claim
  have bad := claim edgeOnly [()] noPremises derivation_without_head.1
  rw [derivation_without_head.2] at bad
  exact Bool.false_ne_true bad

/-- Here both the head and one exact derivation are recorded. -/
def exactLift (_ : Unit) : Graph Bool :=
  ⟨fun n => !n, fun d => d.premises false && !d.premises true && !d.head⟩

theorem witnessed_head_does_not_select_premises :
    (fold exactLift [()]).nodes noPremises.head = true ∧
    onePremise.head = noPremises.head ∧
    (fold exactLift [()]).edges onePremise = true ∧
    (fold exactLift [()]).edges noPremises = false := by decide

/-- Equality of full premise functions is decidable here by checking
    both Boolean inputs. This is a finite instance, not a general rule. -/
def finiteDerivationEq (a b : Derivation Bool) : Decidable (a = b) := by
  cases a with
  | mk ap ah =>
    cases b with
    | mk bp bh =>
      by_cases heads : ah = bh
      · by_cases left : ap false = bp false
        · by_cases right : ap true = bp true
          · apply isTrue
            have premises : ap = bp := funext (fun n => by
              cases n
              · exact left
              · exact right)
            cases premises
            cases heads
            rfl
          · exact isFalse (by intro equal; cases equal; exact right rfl)
        · exact isFalse (by intro equal; cases equal; exact left rfl)
      · exact isFalse (by intro equal; cases equal; exact heads rfl)

instance : DecidableEq (Derivation Bool) := finiteDerivationEq

def record (e : Bool) : Derivation Bool := if e then onePremise else noPremises

/-- Even the restricted recording representation admits two different
    exact premise sets for one witnessed head. Its equality input is
    inhabited constructively in this example. -/
theorem same_head_distinct_recorded_premises :
    (fold (recordLift record) [false, true]).nodes noPremises.head = true ∧
    (fold (recordLift record) [false, true]).edges noPremises = true ∧
    (fold (recordLift record) [false, true]).edges onePremise = true ∧
    noPremises.head = onePremise.head ∧ noPremises ≠ onePremise := by
  refine ⟨by decide, by decide, by decide, rfl, ?_⟩
  intro equal
  have bad := congrFun (congrArg Derivation.premises equal) false
  exact Bool.false_ne_true bad

/-- Distinct source events can have exactly the same contribution. -/
def aliasedLift (_ : Bool) : Graph Bool := edgeOnly ()

/-- Source extraction correctly refuses a head with no recorded edge. -/
theorem contributor_refuses_missing_edge :
    (fold nodeOnly [()]).nodes noPremises.head = true ∧
    contributor nodeOnly [()] noPremises = none := by decide

/-- The selected first source changes with order even when the graph
    is identical. Order independence of graphs is not source identity. -/
theorem contributor_selection_is_order_sensitive :
    fold aliasedLift [false, true] = fold aliasedLift [true, false] ∧
    contributor aliasedLift [false, true] noPremises = some false ∧
    contributor aliasedLift [true, false] noPremises = some true := by
  exact ⟨rfl, rfl, rfl⟩

theorem source_from_fold_claim_fails :
    ¬ (∃ decode : Graph Bool → Bool,
      ∀ e : Bool, decode (fold aliasedLift [e]) = e) := by
  rintro ⟨decode, claim⟩
  have bad : false = true := (claim false).symm.trans (claim true)
  exact Bool.false_ne_true bad

/-- Time erasure precludes decoding even the time of a singleton stream. -/
theorem time_from_fold_claim_fails :
    ¬ (∃ decode : Graph Bool → Nat,
      ∀ time : Nat, decode (foldtimed aliasedLift [Timed.mk false time]) = time) := by
  rintro ⟨decode, claim⟩
  have bad : (0 : Nat) = 1 := (claim 0).symm.trans (claim 1)
  exact Nat.noConfusion bad

#print axioms head_without_derivation
#print axioms head_only_claim_fails
#print axioms derivation_without_head
#print axioms edge_implies_head_claim_fails
#print axioms witnessed_head_does_not_select_premises
#print axioms finiteDerivationEq
#print axioms same_head_distinct_recorded_premises
#print axioms contributor_refuses_missing_edge
#print axioms contributor_selection_is_order_sensitive
#print axioms source_from_fold_claim_fails
#print axioms time_from_fold_claim_fails

#check @ReturnControls.noPremises
#check @ReturnControls.onePremise
#check @ReturnControls.nodeOnly
#check @ReturnControls.head_without_derivation
#check @ReturnControls.head_only_claim_fails
#check @ReturnControls.edgeOnly
#check @ReturnControls.derivation_without_head
#check @ReturnControls.edge_implies_head_claim_fails
#check @ReturnControls.exactLift
#check @ReturnControls.witnessed_head_does_not_select_premises
#check @ReturnControls.finiteDerivationEq
#check @ReturnControls.record
#check @ReturnControls.same_head_distinct_recorded_premises
#check @ReturnControls.aliasedLift
#check @ReturnControls.contributor_refuses_missing_edge
#check @ReturnControls.contributor_selection_is_order_sensitive
#check @ReturnControls.source_from_fold_claim_fails
#check @ReturnControls.time_from_fold_claim_fails

end ReturnControls
