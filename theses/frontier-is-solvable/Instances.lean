import ComparisonContract
import FiniteSchedules
import Fuzz
import Hyper
import Solve
import ThreeValuedGate

namespace Instances

def duration : Nat → Nat := fun _ => 1

def cover (job : Nat) : List Nat :=
  match job with
  | 0 => [0]
  | 1 => [1]
  | _ => []

def good : List Nat := Hyper.Paint.qualified Hyper.demo 0 Hyper.want

def chaindeps : List (Nat × Nat) := [(0, 1), (1, 2)]

theorem chainforward : Solve.Sched.forward chaindeps := by
  intro edge member
  simp [Solve.Sched.forward, chaindeps] at member ⊢
  rcases member with rfl | rfl <;> decide

theorem chainacyclic (node : Nat) :
    ¬ Relation.TransGen (fun left right => (left, right) ∈ chaindeps) node node :=
  Solve.Sched.acyclic chaindeps chainforward node

def showsched (jobs venues horizon : Nat) (deps : List (Nat × Nat)) (states : List Nat)
    (covers : Nat → List Nat) :=
  let sp := Solve.Sched.space jobs venues horizon duration deps states covers
  let listed := Solve.Sched.plans jobs venues horizon duration deps
  (Solve.run sp).map fun index => (listed.get index, sp.readings index)

def showbench (jobs venues horizon : Nat) (deps : List (Nat × Nat)) :=
  let sp := Solve.Bench.space jobs venues horizon duration deps
  let listed := Solve.Sched.plans jobs venues horizon duration deps
  (Solve.run sp).map fun index => (listed.get index, sp.readings index)

def atoms (job : Nat) : List Fuzz.Atom :=
  if job = 0 then [⟨1, 2⟩, ⟨1, 0⟩] else [⟨2, 1⟩]

def gain (plan : FiniteSchedules.Schedule) : Nat :=
  (List.range plan.length).foldl (fun acc index =>
    acc + if FiniteSchedules.start plan index = 0 then Fuzz.expect (atoms index) else 0) 0

def fuzzread (plan : FiniteSchedules.Schedule) : List (Option Int) :=
  [some (Int.ofNat (gain plan)),
    some (Int.ofNat (Solve.Sched.span duration plan)),
    some (Int.ofNat (Solve.Sched.used plan))]

def fuzzcontract : ComparisonContract.Contract :=
  ⟨[⟨0, 0, .maximize, 0⟩, ⟨1, 0, .minimize, 0⟩, ⟨2, 0, .minimize, 0⟩], 0, 0, 0⟩

def fuzzspace (jobs venues horizon : Nat) (deps : List (Nat × Nat)) :
    ThreeValuedGate.FiniteSpace
      (Fin (Solve.Sched.plans jobs venues horizon duration deps).length) fuzzcontract :=
  let listed := Solve.Sched.plans jobs venues horizon duration deps
  { candidates := List.finRange listed.length
    readings := fun index => fuzzread (listed.get index)
    nothingOutside := fun index => by simp [List.finRange, List.mem_ofFn]
    noCoverageGaps := fun _index _mem i hi => by
      have hi3 : i < 3 := by simpa [fuzzcontract] using hi
      match i with
      | 0 => simp [fuzzread, ThreeValuedGate.reading]
      | 1 => simp [fuzzread, ThreeValuedGate.reading]
      | 2 => simp [fuzzread, ThreeValuedGate.reading]
      | n + 3 => omega }

def showfuzz (jobs venues horizon : Nat) (deps : List (Nat × Nat)) :=
  let sp := fuzzspace jobs venues horizon deps
  let listed := Solve.Sched.plans jobs venues horizon duration deps
  (Solve.run sp).map fun index => (listed.get index, sp.readings index)

def matrixrows : List (List Int) :=
  (List.range Hyper.demo.nedges).map fun edge =>
    (List.range (Hyper.demo.states + 2)).map fun row => Hyper.matrix Hyper.demo row edge

def observedrows : List (List Bool) :=
  (List.range Hyper.demo.nedges).map fun edge =>
    (List.range Hyper.demo.states).map fun state =>
      (Hyper.Observed.mask Hyper.demo 0).tail edge state ||
        (Hyper.Observed.mask Hyper.demo 0).head edge state

def colors : List Hyper.Paint.Color :=
  (List.range Hyper.demo.states).map (Hyper.Paint.color Hyper.demo 0 Hyper.want)

#eval showsched 3 1 2 chaindeps good cover
#eval showsched 2 3 0 [] good cover
#eval showbench 2 2 1 []
#eval showfuzz 2 2 1 []
#eval (matrixrows, observedrows, colors, showsched 2 2 1 [(0, 1)] good cover)

end Instances
