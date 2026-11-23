import SoftwareIsComposable.Profile

namespace SoftwareIsComposable
namespace InteractionModel

abbrev Component := Nat
abbrev Observation := Nat

structure Rule where
  requires : List (Component × Observation)
  effect : Observation
  deriving DecidableEq, Repr

def fires (baseObs : Component → List Observation) (selected : List Component)
    (rule : Rule) : Bool :=
  rule.requires.all fun p =>
    decide (p.1 ∈ selected) && decide (p.2 ∈ baseObs p.1)

def localObservations (baseObs : Component → List Observation)
    (selected : List Component) : List Observation :=
  selected.flatMap baseObs

def interactionObservations (baseObs : Component → List Observation)
    (selected : List Component) (rules : List Rule) : List Observation :=
  (rules.filter (fires baseObs selected)).map Rule.effect

def observations (baseObs : Component → List Observation)
    (selected : List Component) (rules : List Rule) : List Observation :=
  localObservations baseObs selected ++ interactionObservations baseObs selected rules

theorem fires_mono (baseObs : Component → List Observation) {small large : List Component}
    (hsub : ∀ c ∈ small, c ∈ large) (rule : Rule)
    (hfire : fires baseObs small rule = true) : fires baseObs large rule = true := by
  unfold fires at hfire ⊢
  apply List.all_eq_true.mpr
  intro p hp
  have hp' := (List.all_eq_true.mp hfire) p hp
  have hp' : decide (p.1 ∈ small) = true ∧ decide (p.2 ∈ baseObs p.1) = true := by
    simpa [Bool.and_eq_true] using hp'
  have hselected : p.1 ∈ large := hsub p.1 (of_decide_eq_true hp'.1)
  have hobserved : p.2 ∈ baseObs p.1 := of_decide_eq_true hp'.2
  simp [hselected, hobserved]

theorem localObservations_mono (baseObs : Component → List Observation)
    {small large : List Component} (hsub : ∀ c ∈ small, c ∈ large) :
    ∀ o, o ∈ localObservations baseObs small → o ∈ localObservations baseObs large := by
  intro o ho
  unfold localObservations at ho ⊢
  rcases List.mem_flatMap.mp ho with ⟨c, hc, hobs⟩
  exact List.mem_flatMap.mpr ⟨c, hsub c hc, hobs⟩

theorem interactionObservations_mono (baseObs : Component → List Observation)
    (rules : List Rule) {small large : List Component}
    (hsub : ∀ c ∈ small, c ∈ large) :
    ∀ o, o ∈ interactionObservations baseObs small rules →
      o ∈ interactionObservations baseObs large rules := by
  intro o ho
  unfold interactionObservations at ho ⊢
  rcases List.mem_map.mp ho with ⟨rule, hrule, heffect⟩
  rcases List.mem_filter.mp hrule with ⟨hrules, hfire⟩
  have hfireLarge := fires_mono baseObs hsub rule hfire
  apply List.mem_map.mpr
  exact ⟨rule, List.mem_filter.mpr ⟨hrules, hfireLarge⟩, heffect⟩

theorem observations_mono (baseObs : Component → List Observation) (rules : List Rule)
    {small large : List Component} (hsub : ∀ c ∈ small, c ∈ large) :
    ∀ o, o ∈ observations baseObs small rules → o ∈ observations baseObs large rules := by
  intro o ho
  unfold observations at ho ⊢
  rcases List.mem_append.mp ho with hlocal | hinteraction
  · exact List.mem_append.mpr (Or.inl (localObservations_mono baseObs hsub o hlocal))
  · exact List.mem_append.mpr
      (Or.inr (interactionObservations_mono baseObs rules hsub o hinteraction))

def inSpec (allowed : Observation → Bool) (baseObs : Component → List Observation)
    (selected : List Component) (rules : List Rule) : Prop :=
  (observations baseObs selected rules).all allowed = true

theorem inSpec_of_local_and_interaction_safe (allowed : Observation → Bool)
    (baseObs : Component → List Observation) (selected : List Component) (rules : List Rule)
    (hlocal : ∀ c ∈ selected, ∀ o ∈ baseObs c, allowed o = true)
    (hInteraction : ∀ rule ∈ rules,
      fires baseObs selected rule = true → allowed rule.effect = true) :
    inSpec allowed baseObs selected rules := by
  unfold inSpec observations
  rw [List.all_append]
  simp only [Bool.and_eq_true]
  constructor
  · apply List.all_eq_true.mpr
    intro o ho
    rcases List.mem_flatMap.mp ho with ⟨c, hc, hobs⟩
    exact hlocal c hc o hobs
  · apply List.all_eq_true.mpr
    intro o ho
    rcases List.mem_map.mp ho with ⟨rule, hrule, rfl⟩
    rcases List.mem_filter.mp hrule with ⟨hrules, hfire⟩
    exact hInteraction rule hrules hfire

def componentA : Component := 0
def componentB : Component := 1
def ready : Observation := 0
def request : Observation := 1
def leakSecret : Observation := 2

def demoLocal (c : Component) : List Observation :=
  if c = componentA then [ready] else if c = componentB then [request] else []

def pairInteraction : Rule :=
  { requires := [(componentA, ready), (componentB, request)], effect := leakSecret }

def demoRules : List Rule := [pairInteraction]

def publicSpec (o : Observation) : Bool := decide (o ≠ leakSecret)

theorem pairInteraction_fires_jointly :
    fires demoLocal [componentA, componentB] pairInteraction = true := by
  decide

theorem pairInteraction_does_not_fire_alone :
    fires demoLocal [componentA] pairInteraction = false ∧
      fires demoLocal [componentB] pairInteraction = false := by
  decide

theorem individually_safe_components_compose_to_leak :
    inSpec publicSpec demoLocal [componentA] demoRules ∧
      inSpec publicSpec demoLocal [componentB] demoRules ∧
      ¬ inSpec publicSpec demoLocal [componentA, componentB] demoRules := by
  simp [inSpec, observations, localObservations, interactionObservations, fires,
    demoRules, pairInteraction, demoLocal, publicSpec, componentA, componentB,
    ready, request, leakSecret]

end InteractionModel
end SoftwareIsComposable
