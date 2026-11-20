import Family.Dataflow

/-!
# Worked example 4: a protocol state machine

A handshake: the peer sends `hello`, then `keys`, then data. The handshake component emits
`opened` once keys are in place and delivers data only after that. Components: `handshake`,
`session` (what the application sees), `audit` (counts delivered records), `billing` (bills from
the audit), and `ui`, which is unrelated.

The session property is an ordered safety property, "no data before `opened`", over every input
sequence. `noDataBefore_prefixClosed` shows it is prefix-closed in the sense of the upstream
`PrefixClosed`, so it is a safety property in the Alpern and Schneider sense, which the old
order-blind allow-lists could not express (audit finding C5). The handshake's own spec is
weaker: it never delivers more records than it received.

* `good_change_admitted`: the handshake is refactored from a numeric state to an explicit state
  type (`refactor_eq` proves the two agree on every input). Rechecking the cone admits it; `ui`
  is not re-run.
* `bad_change`: the handshake starts delivering data after `hello` but before `keys`. Its own
  spec still holds (`early_count`), so a changed-only check admits it; the session's ordered
  safety property fails on `hello, data 5, keys`. The session is in the cone, so the cone check
  refuses.

Premises: `Local` is `dataflow_local`. The session property is the trusted spec.
-/
namespace Family.Examples.Protocol

open Family.Dataflow Family.Selection SoftwareIsIncrementallySafe.OrderedIncrement

inductive In where
  | hello
  | keys
  | data (n : Nat)
  deriving DecidableEq, Repr

inductive Out where
  | opened
  | data (n : Nat)
  deriving DecidableEq, Repr

/-- The original handshake: state 0 idle, 1 hello seen, 2 ready. -/
def hsRun : Nat → List In → List Out
  | _, [] => []
  | 0, .hello :: es => hsRun 1 es
  | 1, .keys :: es => .opened :: hsRun 2 es
  | 2, .data n :: es => .data n :: hsRun 2 es
  | s, _ :: es => hsRun s es

inductive St where
  | idle
  | greeted
  | ready
  deriving DecidableEq, Repr

def St.num : St → Nat
  | .idle => 0
  | .greeted => 1
  | .ready => 2

/-- The refactor: an explicit state type. -/
def stRun : St → List In → List Out
  | _, [] => []
  | .idle, .hello :: es => stRun .greeted es
  | .greeted, .keys :: es => .opened :: stRun .ready es
  | .ready, .data n :: es => .data n :: stRun .ready es
  | s, _ :: es => stRun s es

theorem refactor_eq : ∀ es s, stRun s es = hsRun s.num es
  | [], s => by cases s <;> rfl
  | e :: es, s => by
    cases s <;> cases e <;> simp [stRun, hsRun, St.num, refactor_eq es]

/-- The broken handshake: delivers data once `hello` is seen. -/
def earlyRun : Nat → List In → List Out
  | _, [] => []
  | 0, .hello :: es => earlyRun 1 es
  | 1, .keys :: es => .opened :: earlyRun 2 es
  | 1, .data n :: es => .data n :: earlyRun 1 es
  | 2, .data n :: es => .data n :: earlyRun 2 es
  | s, _ :: es => earlyRun s es

def inData : List In → Nat
  | [] => 0
  | .data _ :: es => inData es + 1
  | _ :: es => inData es

def outData : List Out → Nat
  | [] => 0
  | .data _ :: os => outData os + 1
  | _ :: os => outData os

theorem early_count : ∀ es s, outData (earlyRun s es) ≤ inData es
  | [], _ => by simp [earlyRun, outData]
  | e :: es, s => by
    have ih := early_count es
    match s, e with
    | 0, .hello => simp [earlyRun, inData]; exact ih 1
    | 1, .keys => simp [earlyRun, outData, inData]; exact ih 2
    | 1, .data n => simp [earlyRun, outData, inData]; exact ih 1
    | 2, .data n => simp [earlyRun, outData, inData]; exact ih 2
    | 0, .keys => simp [earlyRun, inData]; exact ih 0
    | 0, .data n => simp [earlyRun, inData]; have := ih 0; omega
    | 1, .hello => simp [earlyRun, inData]; exact ih 1
    | 2, .hello => simp [earlyRun, inData]; exact ih 2
    | 2, .keys => simp [earlyRun, inData]; exact ih 2
    | s + 3, .hello => simp [earlyRun, inData]; exact ih _
    | s + 3, .keys => simp [earlyRun, inData]; exact ih _
    | s + 3, .data n => simp [earlyRun, inData]; have := ih (s + 3); omega

theorem hs_count : ∀ es s, outData (hsRun s es) ≤ inData es
  | [], _ => by simp [hsRun, outData]
  | e :: es, s => by
    have ih := hs_count es
    match s, e with
    | 0, .hello => simp [hsRun, inData]; exact ih 1
    | 1, .keys => simp [hsRun, outData, inData]; exact ih 2
    | 2, .data n => simp [hsRun, outData, inData]; exact ih 2
    | 0, .keys => simp [hsRun, inData]; exact ih 0
    | 0, .data n => simp [hsRun, inData]; have := ih 0; omega
    | 1, .hello => simp [hsRun, inData]; exact ih 1
    | 1, .data n => simp [hsRun, inData]; have := ih 1; omega
    | 2, .hello => simp [hsRun, inData]; exact ih 2
    | 2, .keys => simp [hsRun, inData]; exact ih 2
    | s + 3, .hello => simp [hsRun, inData]; exact ih _
    | s + 3, .keys => simp [hsRun, inData]; exact ih _
    | s + 3, .data n => simp [hsRun, inData]; have := ih (s + 3); omega

/-- "No data before `opened`", tracking whether `opened` has been seen. -/
def ok : Bool → List Out → Bool
  | _, [] => true
  | _, .opened :: os => ok true os
  | o, .data _ :: os => o && ok o os

def NoDataBefore (t : List Out) : Prop := ok false t = true

theorem ok_append : ∀ (o : Bool) (p q : List Out), ok o (p ++ q) = true → ok o p = true
  | _, [], _, _ => rfl
  | _, .opened :: p, q, h => by simp [ok] at h ⊢; exact ok_append true p q h
  | o, .data _ :: p, q, h => by
    simp [ok] at h ⊢; exact ⟨h.1, ok_append o p q h.2⟩

theorem noDataBefore_prefixClosed : PrefixClosed NoDataBefore := by
  rintro t p h ⟨q, rfl⟩
  exact ok_append false p q h

theorem hs_ok : ∀ es s, ok (decide (s = 2)) (hsRun s es) = true
  | [], s => by simp [hsRun, ok]
  | e :: es, s => by
    have ih := hs_ok es
    match s, e with
    | 0, .hello => simpa [hsRun] using ih 1
    | 1, .keys => simpa [hsRun, ok] using ih 2
    | 2, .data n => simpa [hsRun, ok] using ih 2
    | 0, .keys => simpa [hsRun] using ih 0
    | 0, .data n => simpa [hsRun] using ih 0
    | 1, .hello => simpa [hsRun] using ih 1
    | 1, .data n => simpa [hsRun] using ih 1
    | 2, .hello => simpa [hsRun] using ih 2
    | 2, .keys => simpa [hsRun] using ih 2
    | s + 3, .hello => simpa [hsRun] using ih (s + 3)
    | s + 3, .keys => simpa [hsRun] using ih (s + 3)
    | s + 3, .data n => simpa [hsRun] using ih (s + 3)

inductive Sym where
  | handshake | session | audit | billing | ui
  deriving DecidableEq, Repr

def parent : Sym → Option Sym
  | .session => some .handshake
  | .audit => some .session
  | .billing => some .audit
  | _ => none

def dep (s t : Sym) : Bool := parent s == some t

abbrev Beh := List In → List Out
abbrev Code := Beh → Beh

def step (s : Sym) (c : Code) (f : Sym → Beh) : Beh :=
  match parent s with
  | none => c (fun _ => [])
  | some p => c (f p)

def sem (I : Sym → Code) (s : Sym) : Beh := run dep step (fun _ => []) I 4 s

def Q : Sym → Beh → Prop
  | .handshake, b => ∀ es, outData (b es) ≤ inData es
  | .session, b => ∀ es, NoDataBefore (b es)
  | .audit, b => ∀ es, outData (b es) ≤ inData es
  | .billing, b => ∀ es, outData (b es) ≤ inData es
  | .ui, b => ∀ es, b es = []

def old : Sym → Code
  | .handshake => fun _ => hsRun 0
  | .ui => fun _ _ => []
  | _ => fun f => f

theorem sem_local : Local (Deps dep) sem := dataflow_local dep step _ 4

theorem old_good : ∀ s, Q s (sem old s) := by
  intro s; cases s <;> intro es <;>
    simp [Q, sem, run, step, parent, dep, old, hs_count, NoDataBefore] <;>
    simpa using hs_ok es 0

def onlyHs : Sym → Bool := fun s => s == .handshake

def K (s : Sym) : Prop := s ≠ .ui

theorem K_changed : ∀ s, onlyHs s = true → K s := by
  intro s; cases s <;> simp [onlyHs, K]

theorem K_deps : ∀ s t, Deps dep s t → K t → K s := by
  intro s t; cases s <;> cases t <;> simp [Deps, dep, parent, K]

def refactored : Sym → Code := fun _ _ => stRun .idle

set_option linter.unnecessarySimpa false in
theorem good_change_admitted : ∀ s, Q s (sem (update old onlyHs refactored) s) := by
  refine closed_witness_sound K K_changed K_deps sem_local old_good ?_
  intro s _
  have h := old_good s
  cases s <;>
    simpa [Q, sem, run, step, parent, dep, old, update, onlyHs, refactored, refactor_eq,
      St.num] using h

theorem ui_not_rerun (new : Sym → Code) :
    sem (update old onlyHs new) .ui = sem old .ui :=
  outside_closed_unchanged K K_changed K_deps sem_local .ui (by simp [K])

def early : Sym → Code := fun _ _ => earlyRun 0

theorem bad_change :
    Q .handshake (sem (update old onlyHs early) .handshake) ∧
      ¬ Q .session (sem (update old onlyHs early) .session) ∧
      Cone (Deps dep) onlyHs .session := by
  refine ⟨?_, ?_, ?_⟩
  · intro es; simpa [sem, run, step, parent, dep, update, onlyHs, early] using early_count es 0
  · intro h
    have := h [.hello, .data 5, .keys]
    simp [sem, run, step, parent, dep, update, onlyHs, early, old, earlyRun, NoDataBefore,
      ok] at this
  · exact reach_cone ⟨.handshake, .step (show Deps dep .session .handshake by rfl) (.refl _), rfl⟩

end Family.Examples.Protocol
