import Std

namespace Mediation

structure Sensor (n : Nat) where
  node : Fin n
  deployed : Bool
  healthy : Bool
  faithful : Bool
  deriving DecidableEq

def Sensor.ready {n : Nat} (s : Sensor n) : Prop :=
  s.deployed = true ∧ s.healthy = true ∧ s.faithful = true

structure Graph (n : Nat) where
  edges : List (Fin n × Fin n)
  sensors : List (Sensor n)

def Edge {n : Nat} (g : Graph n) (x y : Fin n) : Prop := (x,y) ∈ g.edges

inductive Path {n : Nat} (g : Graph n) : Fin n → Fin n → Prop
  | here (x) : Path g x x
  | step {x y z} : Edge g x y → Path g y z → Path g x z

def Observed {n : Nat} (g : Graph n) (x : Fin n) : Prop :=
  ∃ s ∈ g.sensors, s.ready ∧ Path g x s.node

theorem path_trans {n : Nat} {g : Graph n} {a b c : Fin n}
    (ab : Path g a b) (bc : Path g b c) : Path g a c := by
  induction ab with
  | here => exact bc
  | step h _ ih => exact .step h (ih bc)

theorem observed_of_path {n : Nat} {g : Graph n} {x y : Fin n}
    (p : Path g x y) (h : Observed g y) : Observed g x := by
  rcases h with ⟨s, hs, ready, q⟩
  exact ⟨s, hs, ready, path_trans p q⟩

structure Rule (n : Nat) where
  premises : List (Fin n)
  head : Fin n
  deriving DecidableEq

-- Full hyperedge semantics. A single mediation link is not a derivation.
inductive Closure {n : Nat} (seeds : List (Fin n)) (rules : List (Rule n)) :
    Fin n → Prop
  | seed {x} : x ∈ seeds → Closure seeds rules x
  | fire {r} : r ∈ rules → (∀ p ∈ r.premises, Closure seeds rules p) →
      Closure seeds rules r.head

-- The local rule condition mentions only wiring and sensor placement.
-- A rule may instrument its head directly or pass its observation to a
-- listed, jointly required input. The edge direction is an evidence flow
-- promise, not a reversal of the underlying computational dependency.
def Mediate {n : Nat} (g : Graph n) (r : Rule n) : Prop :=
  (∃ s ∈ g.sensors, s.node = r.head ∧ s.ready) ∨
  ∃ p ∈ r.premises, Edge g r.head p

theorem closure_observed {n : Nat} (g : Graph n) (seeds : List (Fin n))
    (rules : List (Rule n))
    (placement : ∀ x ∈ seeds, ∃ s ∈ g.sensors, s.ready ∧ Path g x s.node)
    (preserve : ∀ r ∈ rules, (∀ p ∈ r.premises, Closure seeds rules p) → Mediate g r)
    {x : Fin n} (h : Closure seeds rules x) : Observed g x := by
  induction h with
  | seed hx => exact placement _ hx
  | fire hr fired ih =>
    rcases preserve _ hr fired with ⟨s, hs, loc, ready⟩ | ⟨p, hp, link⟩
    · exact ⟨s, hs, ready, loc ▸ Path.here s.node⟩
    · exact observed_of_path (.step link (.here p)) (ih p hp)

theorem path_append {n : Nat} {g : Graph n} {x z : Fin n}
    (extra : List (Fin n × Fin n)) (news : List (Sensor n))
    (p : Path g x z) : Path ⟨g.edges ++ extra, g.sensors ++ news⟩ x z := by
  induction p with
  | here x => exact .here x
  | step h _ ih =>
    exact .step (List.mem_append_left extra h) ih

theorem observed_append {n : Nat} {g : Graph n} {x : Fin n}
    (extra : List (Fin n × Fin n)) (news : List (Sensor n))
    (h : Observed g x) : Observed ⟨g.edges ++ extra, g.sensors ++ news⟩ x := by
  obtain ⟨s, hs, ready, p⟩ := h
  exact ⟨s, List.mem_append_left news hs, ready, path_append extra news p⟩

theorem transport_path {n : Nat} {g : Graph n} {P : Fin n → Prop}
    (wiring : ∀ {x y}, Edge g x y → P y → P x)
    {x y : Fin n} (p : Path g x y) (q : P y) : P x := by
  induction p with
  | here => exact q
  | step e _ ih => exact wiring e (ih q)

-- Deployment correspondence is separate from the graph theorem. No rule
-- of graph reachability establishes these facts about the physical world.
theorem external_lift {n : Nat} (g : Graph n)
    (physical signal deploy well honest : Fin n → Prop)
    (wiring : ∀ {x y}, Edge g x y → signal y → signal x)
    (readyTruth : ∀ s ∈ g.sensors, s.ready →
      deploy s.node ∧ well s.node ∧ honest s.node)
    (base : ∀ x, deploy x → well x → honest x → signal x)
    (meaning : ∀ x, signal x → physical x)
    {x : Fin n} (obs : Observed g x) : physical x := by
  rcases obs with ⟨s, hs, ok, p⟩
  rcases readyTruth s hs ok with ⟨d, w, f⟩
  apply meaning
  have endSeen : signal s.node := base s.node d w f
  exact transport_path wiring p endSeen

theorem target_coverage {n : Nat} (g : Graph n) (seeds : List (Fin n))
    (rules : List (Rule n)) (target : Fin n → Prop)
    (represented : ∀ x, target x → Closure seeds rules x)
    (placement : ∀ x ∈ seeds, ∃ s ∈ g.sensors, s.ready ∧ Path g x s.node)
    (preserve : ∀ r ∈ rules, (∀ p ∈ r.premises, Closure seeds rules p) → Mediate g r)
    {x : Fin n} (h : target x) : Observed g x :=
  closure_observed g seeds rules placement preserve (represented x h)


-- Relational specification of marking ready sensors, then processing
-- predecessor arcs in the reverse traversal.
inductive ReverseReached {n : Nat} (g : Graph n) : Fin n → Prop
  | ready {s} : s ∈ g.sensors → s.ready → ReverseReached g s.node
  | back {x y} : Edge g x y → ReverseReached g y → ReverseReached g x

theorem reverse_sound {n : Nat} {g : Graph n} {x : Fin n}
    (h : ReverseReached g x) : Observed g x := by
  induction h with
  | ready hs ok => exact ⟨_, hs, ok, .here _⟩
  | back e _ ih => exact observed_of_path (.step e (.here _)) ih

theorem reverse_along_path {n : Nat} {g : Graph n} {x y : Fin n}
    (p : Path g x y) (h : ReverseReached g y) : ReverseReached g x := by
  induction p with
  | here => exact h
  | step e _ ih => exact .back e (ih h)

theorem reverse_complete {n : Nat} {g : Graph n} {x : Fin n}
    (h : Observed g x) : ReverseReached g x := by
  rcases h with ⟨s, hs, ok, p⟩
  exact reverse_along_path p (.ready hs ok)

theorem reverse_exact {n : Nat} (g : Graph n) (x : Fin n) :
    ReverseReached g x ↔ Observed g x := ⟨reverse_sound, reverse_complete⟩

end Mediation
