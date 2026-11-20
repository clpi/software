import Family.Dataflow

/-!
# Worked example 5: a data pipeline with a two-run noninterference spec

Records are `(email, amount)`; the email is personal data. Components: `ingest`, `clean`
(drops zero-amount rows), `aggregate` (total amount), `publish` (a public dashboard),
`archive` (internal, may see emails), and `alerts`, which is unrelated.

The spec on `aggregate` and `publish` is two-run noninterference: any two inputs that agree on
the amounts (the public view) give the same output, whatever the emails are. This is a
hyperproperty (Goguen and Meseguer; Clarkson and Schneider), the kind audit finding C6 showed a
per-run profile check cannot see. `clean`'s own spec is that it never adds rows.

* `good_change_admitted`: `clean` is rewritten as explicit recursion (`cleanRec_eq`). Rechecking
  the cone admits the release; `alerts` is not re-run.
* `bad_change`: `clean` starts de-duplicating rows by email. It still never adds rows
  (`dedupe_length`), so a changed-only check admits it. The published total now depends on
  whether two customers share an email: the inputs `[(1,5),(1,5)]` and `[(1,5),(2,5)]` agree on
  amounts and publish 5 and 10. That is a leak of personal data through a public aggregate. The
  dashboard is in the cone, so the cone check refuses.

Premises: `Local` is `dataflow_local`. Which fields are public is the trusted spec.
-/
namespace Family.Examples.DataPipeline

open Family.Dataflow Family.Selection SoftwareIsIncrementallySafe.OrderedIncrement

abbrev Rec := Nat × Nat

def low (r : List Rec) : List Nat := r.map Prod.snd

def total : List Rec → Nat
  | [] => 0
  | x :: r => x.2 + total r

def keep (x : Rec) : Bool := x.2 != 0

def cleanRec : List Rec → List Rec
  | [] => []
  | x :: r => if x.2 = 0 then cleanRec r else x :: cleanRec r

theorem cleanRec_eq : ∀ r, cleanRec r = r.filter keep
  | [] => rfl
  | x :: r => by
    by_cases h : x.2 = 0
    · have hk : keep x = false := by simp [keep, h]
      simp [cleanRec, List.filter, hk, h, cleanRec_eq r]
    · have hk : keep x = true := by simp [keep, h]
      simp [cleanRec, List.filter, hk, h, cleanRec_eq r]

/-- The cleaned total depends only on the amounts. -/
def lowTotal : List Nat → Nat
  | [] => 0
  | a :: as => (if a = 0 then 0 else a) + lowTotal as

theorem total_clean : ∀ r, total (r.filter keep) = lowTotal (low r)
  | [] => rfl
  | x :: r => by
    have ih := total_clean r
    simp only [low, List.map] at ih ⊢
    by_cases h : x.2 = 0
    · have hk : keep x = false := by simp [keep, h]
      simp [List.filter, hk, h, lowTotal, ih]
    · have hk : keep x = true := by simp [keep, h]
      simp [List.filter, hk, h, total, lowTotal, ih]

def dedupe : List Nat → List Rec → List Rec
  | _, [] => []
  | seen, x :: r => if x.1 ∈ seen then dedupe seen r else x :: dedupe (x.1 :: seen) r

theorem dedupe_length : ∀ seen r, (dedupe seen r).length ≤ r.length
  | _, [] => by simp [dedupe]
  | seen, x :: r => by
    by_cases h : x.1 ∈ seen
    · simp [dedupe, h]; have := dedupe_length seen r; omega
    · simp [dedupe, h]; exact dedupe_length (x.1 :: seen) r

inductive Sym where
  | ingest | clean | aggregate | publish | archive | alerts
  deriving DecidableEq, Repr

def parent : Sym → Option Sym
  | .clean => some .ingest
  | .aggregate => some .clean
  | .publish => some .aggregate
  | .archive => some .clean
  | _ => none

def dep (s t : Sym) : Bool := parent s == some t

abbrev Beh := List Rec → List Rec
abbrev Code := Beh → Beh

def step (s : Sym) (c : Code) (f : Sym → Beh) : Beh :=
  match parent s with
  | none => c id
  | some p => c (f p)

def sem (I : Sym → Code) (s : Sym) : Beh := run dep step id I 4 s

/-- Two-run noninterference: equal public views give equal outputs. -/
def NI (b : Beh) : Prop := ∀ r r', low r = low r' → b r = b r'

def Q : Sym → Beh → Prop
  | .ingest, b => ∀ r, b r = r
  | .clean, b => ∀ r, (b r).length ≤ r.length
  | .aggregate, b => NI b
  | .publish, b => NI b
  | .archive, b => ∀ r, (b r).length ≤ r.length
  | .alerts, b => ∀ r, b r = []

def old : Sym → Code
  | .ingest => fun f => f
  | .clean => fun f r => (f r).filter keep
  | .aggregate => fun f r => [(0, total (f r))]
  | .publish => fun f => f
  | .archive => fun f => f
  | .alerts => fun _ _ => []

theorem sem_local : Local (Deps dep) sem := dataflow_local dep step _ 4

theorem old_good : ∀ s, Q s (sem old s) := by
  intro s
  cases s
  · intro r; simp [sem, run, step, parent, dep, old]
  · intro r; simp [sem, run, step, parent, dep, old, List.length_filter_le]
  · intro r r' h; simp [sem, run, step, parent, dep, old, total_clean, h]
  · intro r r' h; simp [sem, run, step, parent, dep, old, total_clean, h]
  · intro r; simp [sem, run, step, parent, dep, old, List.length_filter_le]
  · intro r; simp [sem, run, step, parent, dep, old]

def onlyClean : Sym → Bool := fun s => s == .clean

def K (s : Sym) : Prop := s ≠ .alerts ∧ s ≠ .ingest

theorem K_changed : ∀ s, onlyClean s = true → K s := by
  intro s; cases s <;> simp [onlyClean, K]

theorem K_deps : ∀ s t, Deps dep s t → K t → K s := by
  intro s t; cases s <;> cases t <;> simp [Deps, dep, parent, K]

def rewritten : Sym → Code := fun _ f r => cleanRec (f r)

theorem good_change_admitted : ∀ s, Q s (sem (update old onlyClean rewritten) s) := by
  refine closed_witness_sound K K_changed K_deps sem_local old_good ?_
  intro s _
  cases s
  · intro r; simp [sem, run, step, parent, dep, old, update, onlyClean]
  · intro r; simp [sem, run, step, parent, dep, old, update, onlyClean, rewritten, cleanRec_eq,
      List.length_filter_le]
  · intro r r' h; simp [sem, run, step, parent, dep, old, update, onlyClean, rewritten,
      cleanRec_eq, total_clean, h]
  · intro r r' h; simp [sem, run, step, parent, dep, old, update, onlyClean, rewritten,
      cleanRec_eq, total_clean, h]
  · intro r; simp [sem, run, step, parent, dep, old, update, onlyClean, rewritten, cleanRec_eq,
      List.length_filter_le]
  · intro r; simp [sem, run, step, parent, dep, old, update, onlyClean]

theorem alerts_not_rerun (new : Sym → Code) :
    sem (update old onlyClean new) .alerts = sem old .alerts :=
  outside_closed_unchanged K K_changed K_deps sem_local .alerts (by simp [K])

def deduped : Sym → Code := fun _ f r => dedupe [] (f r)

theorem bad_change :
    Q .clean (sem (update old onlyClean deduped) .clean) ∧
      ¬ Q .publish (sem (update old onlyClean deduped) .publish) ∧
      Cone (Deps dep) onlyClean .publish := by
  refine ⟨?_, ?_, ?_⟩
  · intro r
    simpa [sem, run, step, parent, dep, update, onlyClean, deduped, old] using dedupe_length [] r
  · intro h
    have := h [(1, 5), (1, 5)] [(1, 5), (2, 5)] rfl
    simp [sem, run, step, parent, dep, update, onlyClean, deduped, old, dedupe, total] at this
  · exact reach_cone ⟨.clean, .step (show Deps dep .publish .aggregate by rfl)
      (.step (show Deps dep .aggregate .clean by rfl) (.refl _)), rfl⟩

end Family.Examples.DataPipeline
