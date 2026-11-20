import Family.Dataflow

/-!
# Worked example 2: a concurrent queue

A schedule is the linearization order of the producers' and consumers' operations; every
property below quantifies over every schedule, so it covers every interleaving. Components:

* `buffer`: the storage algorithm, run over the schedule.
* `queue`: the public queue, which reports what the buffer returned (linearizable FIFO spec).
* `consumer`: sees only the results of its dequeues.
* `metrics`: counts empty dequeues.
* `logger`: echoes the schedule; it depends on nothing above.

Properties: the buffer's own unit spec checks occupancy only (same number of successful
dequeues as a reference queue, one result per operation). The queue must agree with a
sequential FIFO reference on every schedule. Consumer and metrics must agree with the
reference view.

* `good_change_admitted`: the buffer is replaced by a two-stack (amortized O(1)) queue. The
  proof that it agrees with the list queue on every schedule is `tsRun_eq`. Rechecking the cone
  admits the release; `logger` is not re-run.
* `bad_change`: the buffer is replaced by a stack. Its own occupancy spec still passes
  (`stack_count`), so a changed-only check admits it. The queue's FIFO spec fails on the
  schedule `enq 1, enq 2, deq`, and the queue is in the cone, so the cone check refuses.

Premises: `Local` is `dataflow_local`. The schedule-as-linearization model is a premise about
the implementation (it is linearizable at all); the FIFO reference is the trusted spec.
-/
namespace Family.Examples.ConcurrentQueue

open Family.Dataflow Family.Selection SoftwareIsIncrementallySafe.OrderedIncrement

inductive Op where
  | enq (v : Nat)
  | deq
  deriving DecidableEq, Repr

abbrev Res := List (Option Nat)

/-- Reference sequential FIFO queue. -/
def listRun : List Nat → List Op → Res
  | _, [] => []
  | q, .enq v :: os => none :: listRun (q ++ [v]) os
  | [], .deq :: os => none :: listRun [] os
  | x :: q, .deq :: os => some x :: listRun q os

/-- Two-stack queue: front list and reversed back list. -/
def tsRun : List Nat → List Nat → List Op → Res
  | _, _, [] => []
  | f, b, .enq v :: os => none :: tsRun f (v :: b) os
  | x :: f, b, .deq :: os => some x :: tsRun f b os
  | [], b, .deq :: os =>
    match b.reverse with
    | [] => none :: tsRun [] [] os
    | x :: f => some x :: tsRun f [] os

theorem tsRun_eq : ∀ os f b, tsRun f b os = listRun (f ++ b.reverse) os
  | [], _, _ => by simp [tsRun, listRun]
  | .enq v :: os, f, b => by
    simp [tsRun, listRun, tsRun_eq os f (v :: b)]
  | .deq :: os, x :: f, b => by
    simp [tsRun, listRun, tsRun_eq os f b]
  | .deq :: os, [], b => by
    cases h : b.reverse with
    | nil => simp [tsRun, listRun, h, tsRun_eq os [] []]
    | cons x f => simp [tsRun, listRun, h, tsRun_eq os f []]

/-- A stack: last in, first out. -/
def stackRun : List Nat → List Op → Res
  | _, [] => []
  | s, .enq v :: os => none :: stackRun (v :: s) os
  | [], .deq :: os => none :: stackRun [] os
  | x :: s, .deq :: os => some x :: stackRun s os

def countSome : Res → Nat
  | [] => 0
  | none :: rs => countSome rs
  | some _ :: rs => countSome rs + 1

theorem stack_count : ∀ os (s q : List Nat), s.length = q.length →
    countSome (stackRun s os) = countSome (listRun q os) ∧
      (stackRun s os).length = (listRun q os).length
  | [], _, _, _ => by simp [stackRun, listRun]
  | .enq v :: os, s, q, h => by
    have := stack_count os (v :: s) (q ++ [v]) (by simp [h])
    simp [stackRun, listRun, countSome, this]
  | .deq :: os, [], [], _ => by
    have := stack_count os [] [] rfl
    simp [stackRun, listRun, countSome, this]
  | .deq :: os, x :: s, y :: q, h => by
    have := stack_count os s q (by simpa using h)
    simp [stackRun, listRun, countSome, this]
  | .deq :: _, [], _ :: _, h => by simp at h
  | .deq :: _, _ :: _, [], h => by simp at h

inductive Sym where
  | buffer | queue | consumer | metrics | logger
  deriving DecidableEq, Repr

def parent : Sym → Option Sym
  | .queue => some .buffer
  | .consumer => some .queue
  | .metrics => some .queue
  | _ => none

def dep (s t : Sym) : Bool := parent s == some t

abbrev Beh := List Op → Res
/-- A component's code reads the schedule and its dependency's results. -/
abbrev Code := List Op → Res → Res

def step (s : Sym) (c : Code) (f : Sym → Beh) : Beh :=
  match parent s with
  | none => fun os => c os []
  | some p => fun os => c os (f p os)

def sem (I : Sym → Code) (s : Sym) : Beh := run dep step (fun _ => []) I 3 s

def deqs : List Op → Res → Res
  | [], _ => []
  | _, [] => []
  | .deq :: os, r :: rs => r :: deqs os rs
  | .enq _ :: os, _ :: rs => deqs os rs

def empties : Res → Nat
  | [] => 0
  | none :: rs => empties rs + 1
  | some _ :: rs => empties rs

def enqs : List Op → Nat
  | [] => 0
  | .enq _ :: os => enqs os + 1
  | .deq :: os => enqs os

def Q : Sym → Beh → Prop
  | .buffer, b => ∀ os, countSome (b os) = countSome (listRun [] os) ∧
      (b os).length = (listRun [] os).length
  | .queue, b => ∀ os, b os = listRun [] os
  | .consumer, b => ∀ os, b os = deqs os (listRun [] os)
  | .metrics, b => ∀ os, b os = [some (empties (listRun [] os) - enqs os)]
  | .logger, b => ∀ os, (b os).length = os.length

def old : Sym → Code
  | .buffer => fun os _ => listRun [] os
  | .queue => fun _ r => r
  | .consumer => fun os r => deqs os r
  | .metrics => fun os r => [some (empties r - enqs os)]
  | .logger => fun os _ => os.map (fun _ => none)

theorem sem_local : Local (Deps dep) sem := dataflow_local dep step _ 3

theorem old_good : ∀ s, Q s (sem old s) := by
  intro s; cases s <;> intro os <;> simp [Q, sem, run, step, parent, dep, old]

def onlyBuffer : Sym → Bool := fun s => s == .buffer

def K (s : Sym) : Prop := s ≠ .logger

theorem K_changed : ∀ s, onlyBuffer s = true → K s := by
  intro s; cases s <;> simp [onlyBuffer, K]

theorem K_deps : ∀ s t, Deps dep s t → K t → K s := by
  intro s t; cases s <;> cases t <;> simp [Deps, dep, parent, K]

def twoStack : Sym → Code := fun _ os _ => tsRun [] [] os

theorem good_change_admitted : ∀ s, Q s (sem (update old onlyBuffer twoStack) s) := by
  refine closed_witness_sound K K_changed K_deps sem_local old_good ?_
  intro s _
  cases s <;> intro os <;>
    simp [Q, sem, run, step, parent, dep, old, update, onlyBuffer, twoStack, tsRun_eq]

theorem logger_not_rerun (new : Sym → Code) :
    sem (update old onlyBuffer new) .logger = sem old .logger :=
  outside_closed_unchanged K K_changed K_deps sem_local .logger (by simp [K])

def stack : Sym → Code := fun _ os _ => stackRun [] os

theorem bad_change :
    Q .buffer (sem (update old onlyBuffer stack) .buffer) ∧
      ¬ Q .queue (sem (update old onlyBuffer stack) .queue) ∧
      Cone (Deps dep) onlyBuffer .queue := by
  refine ⟨?_, ?_, ?_⟩
  · intro os
    simpa [sem, run, step, parent, dep, update, onlyBuffer, stack] using stack_count os [] [] rfl
  · intro h
    have := h [.enq 1, .enq 2, .deq]
    simp [sem, run, step, parent, dep, update, onlyBuffer, stack, old, stackRun, listRun] at this
  · exact reach_cone ⟨.buffer, .step (show Deps dep .queue .buffer by rfl) (.refl _), rfl⟩

end Family.Examples.ConcurrentQueue
