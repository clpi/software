import Candidate
import Search
import Frontier
import Std

namespace Pipeline

open FrontierSolvable

/- The derivation-to-action pipeline, stated over the candidate home.

   A log is a list of candidate records. The space of a log is the
   projection of the candidate module. The derived view of a log
   under an epoch is the solved set of its space. The intent vector
   of a log is the reading of its space. The ranking of a log is
   the weighted order of the search module over its candidates.
   The selected action is the head of the derived view.

   Premise labels. The theorems below are about the model. The
   following are premises, not theorems, each with its route to
   being checked outside this module.
   P1 extraction fidelity: the records of a real log faithfully
   carry the data they claim to carry. Route: the extraction
   checker of the owning system, run on the log.
   P2 witness honesty: a record marked seen and wanted was in
   fact seen and is in fact wanted. Route: witness audit.
   P3 the six score axes are readings of the record alone; what
   speed, power, width and ease mean in the world is not computed
   from the log. Route: the measurement campaign of the owning
   system; this module proves facts about the readings as data.
   P4 threshold choice: the stop threshold is a choice of the
   caller. The stop results are proved for every threshold.
   P5 execution fidelity: that an external executor performs the
   selected action as modeled is outside this module. Route: the
   executor receipt check of the owning system.
   P6 progress: the stop completeness result is conditional on a
   stated progress hypothesis on the step function; the hypothesis
   is a premise about the caller's step, labeled where used. -/

abbrev Log := List Candidate.Record

def spaceOf (log : Log) : Candidate.Space := Candidate.project log

def derive (e : Candidate.Epoch) (log : Log) : List Nat :=
  Candidate.solved (spaceOf log) e

def intent (log : Log) (x i : Nat) : Int := (spaceOf log).read x i

def qualify (log : Log) (x : Nat) : Bool := (spaceOf log).ok x

def ranked (e : Candidate.Epoch) (log : Log) : List Nat :=
  Search.order e.weight (spaceOf log).cands

def select (e : Candidate.Epoch) (log : Log) : Option Nat :=
  (derive e log).head?

def deriveS (e : Candidate.Epoch) (s : Candidate.Space) : List Nat :=
  Candidate.solved s e

/- Item 3: the selected action is undominated in the pool, and the
   head of the ranking is the weighted best of the pool. -/

theorem select_mem {e : Candidate.Epoch} {log : Log} {a : Nat}
    (h : select e log = some a) : a ∈ derive e log := by
  cases hd : derive e log with
  | nil => simp [select, hd] at h
  | cons b t =>
    have hb : b = a := by simpa [select, hd] using h
    rw [← hb]
    simp

theorem selected_frontier {e : Candidate.Epoch} {log : Log} {a : Nat}
    (h : select e log = some a) :
    Frontier (Candidate.elig (spaceOf log) (spaceOf log).cands)
      (Candidate.dom e (spaceOf log)) a :=
  (Candidate.exact (spaceOf log) e a).mp (select_mem h)

theorem selected_undominated {e : Candidate.Epoch} {log : Log} {a : Nat}
    (h : select e log = some a) :
    ∀ y, Candidate.elig (spaceOf log) (spaceOf log).cands y →
      ¬ Candidate.dom e (spaceOf log) y a :=
  (selected_frontier h).2

theorem selected_qualified {e : Candidate.Epoch} {log : Log} {a : Nat}
    (h : select e log = some a) :
    a ∈ (spaceOf log).cands ∧ qualify log a = true :=
  ⟨(selected_frontier h).1.1, (selected_frontier h).1.2⟩

theorem put_head {w : Nat → Nat} {x : Nat} :
    ∀ (ys : List Nat) (h : Nat), (Search.put w x ys).head? = some h →
      (h = x ∧ ∀ u, ys.head? = some u → w x ≤ w u) ∨
        (ys.head? = some h ∧ w h < w x) := by
  intro ys
  cases ys with
  | nil =>
    intro h hh
    have hx : x = h := by simpa [Search.put] using hh
    refine Or.inl ⟨hx.symm, ?_⟩
    · intro u hu; simp at hu
  | cons z zs =>
    intro h hh
    by_cases hle : w x ≤ w z
    · have hput : Search.put w x (z :: zs) = x :: z :: zs := by
        simp [Search.put, hle]
      rw [hput] at hh
      have hx : x = h := by simpa using hh
      refine Or.inl ⟨hx.symm, ?_⟩
      intro u hu
      have huz : z = u := by simpa using hu
      rw [← huz]; exact hle
    · have hput : Search.put w x (z :: zs) = z :: Search.put w x zs := by
        simp [Search.put, hle]
      rw [hput] at hh
      have hz : z = h := by simpa using hh
      refine Or.inr ⟨by simpa using congrArg some hz, ?_⟩
      rw [← hz]; exact Nat.lt_of_not_le hle

theorem order_head_best {w : Nat → Nat} :
    ∀ (xs : List Nat) (h : Nat), (Search.order w xs).head? = some h →
      h ∈ xs ∧ ∀ y ∈ xs, w h ≤ w y := by
  intro xs
  induction xs with
  | nil => intro h hh; simp [Search.order] at hh
  | cons x xs ih =>
    intro h hh
    cases xs with
    | nil =>
      have hx : x = h := by simpa [Search.order, Search.put] using hh
      subst hx
      refine ⟨by simp, ?_⟩
      intro y hy
      have hyx : y = x := by simpa using hy
      rw [hyx]
      exact Nat.le_refl _
    | cons z zs =>
      have hord : Search.order w (x :: z :: zs) =
          Search.put w x (Search.order w (z :: zs)) := rfl
      rw [hord] at hh
      rcases put_head (Search.order w (z :: zs)) h hh with
        ⟨rfl, hle⟩ | ⟨hhd, hlt⟩
      · refine ⟨by simp, ?_⟩
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact Nat.le_refl _
        · have hne : (Search.order w (z :: zs)) ≠ [] := by
            have h1 : Search.order w (z :: zs) =
                Search.put w z (Search.order w zs) := rfl
            rw [h1]
            cases hzs : Search.order w zs with
            | nil => simp [Search.put]
            | cons u us =>
              by_cases hle2 : w z ≤ w u
              · simp [Search.put, hle2]
              · simp [Search.put, hle2]
          obtain ⟨h', hh'⟩ : ∃ h', (Search.order w (z :: zs)).head? = some h' := by
            cases hc : Search.order w (z :: zs) with
            | nil => exact absurd hc hne
            | cons u us => exact ⟨u, rfl⟩
          obtain ⟨hm', hmin'⟩ := ih h' hh'
          exact Nat.le_trans (hle h' hh') (hmin' y hy)
      · have hhead : (Search.order w (z :: zs)).head? = some h := hhd
        obtain ⟨hm', hmin'⟩ := ih h hhead
        refine ⟨List.mem_cons_of_mem x hm', ?_⟩
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact Nat.le_of_lt hlt
        · exact hmin' y hy

theorem ranked_head_best {e : Candidate.Epoch} {log : Log} {h : Nat}
    (hh : (ranked e log).head? = some h) :
    h ∈ (spaceOf log).cands ∧
      ∀ y ∈ (spaceOf log).cands, e.weight h ≤ e.weight y :=
  order_head_best (spaceOf log).cands h hh

/- Item 1: determinism. The derived view, the intent vector, the
   qualification view and the selection are functions of the log
   alone, and the derived view is exactly the frontier predicate
   of the candidate module over the log. -/

theorem derive_congr {e : Candidate.Epoch} {l₁ l₂ : Log} (h : l₁ = l₂) :
    derive e l₁ = derive e l₂ := by rw [h]

theorem intent_congr {l₁ l₂ : Log} (h : l₁ = l₂) (x i : Nat) :
    intent l₁ x i = intent l₂ x i := by rw [h]

theorem select_congr {e : Candidate.Epoch} {l₁ l₂ : Log} (h : l₁ = l₂) :
    select e l₁ = select e l₂ := by rw [h]

theorem derive_of_space_eq {e : Candidate.Epoch} {l₁ l₂ : Log}
    (h : spaceOf l₁ = spaceOf l₂) : derive e l₁ = derive e l₂ := by
  unfold derive
  rw [h]

theorem derive_exact (e : Candidate.Epoch) (log : Log) (x : Nat) :
    x ∈ derive e log ↔
      Frontier (Candidate.elig (spaceOf log) (spaceOf log).cands)
        (Candidate.dom e (spaceOf log)) x :=
  Candidate.exact (spaceOf log) e x

theorem derive_reweight {l : Log} {e e' : Candidate.Epoch}
    (h : e.axes = e'.axes) (x : Nat) :
    x ∈ derive e l ↔ x ∈ derive e' l :=
  Candidate.same h x

/- Item 4: incremental reevaluation equals full reevaluation.
   The update predicate is the frontier of the old space filtered
   by the appended candidate, plus the appended candidate when
   nothing old dominates it. The engine is the candidate module
   step result; the from-scratch form is its weighted result. -/

def incrFrontier (s : Candidate.Space) (e : Candidate.Epoch) (z x : Nat) :
    Prop :=
  (Frontier (Candidate.elig s s.cands) (Candidate.dom e s) x ∧
      ¬ Candidate.dom e s z x) ∨
    (x = z ∧ ∀ y, Candidate.elig s s.cands y → ¬ Candidate.dom e s y z)

theorem incremental_equals_full {s : Candidate.Space}
    {e : Candidate.Epoch} {z : Nat} (hz : s.ok z = true) (x : Nat) :
    incrFrontier s e z x ↔ x ∈ deriveS e (Candidate.grown s z) :=
  (Candidate.step s e z hz x).symm

theorem full_from_scratch (s : Candidate.Space) (e : Candidate.Epoch)
    (z x : Nat) :
    x ∈ deriveS e (Candidate.grown s z) ↔
      x ∈ FrontierSolvable.compute (s.cands ++ [z]) s.ok
        (FrontierSolvable.pareto e.axes s.read) :=
  Candidate.fresh.solve s e z x

theorem append_unqualified_no_change {s : Candidate.Space}
    {e : Candidate.Epoch} {z : Nat} (hz : s.ok z = false) (x : Nat) :
    x ∈ deriveS e (Candidate.grown s z) ↔ x ∈ deriveS e s :=
  Candidate.grow.dead s e z hz x

theorem incremental_log {e : Candidate.Epoch} {log : Log}
    {r : Candidate.Record}
    (hproj : spaceOf (log ++ [r]) =
      Candidate.grown (spaceOf log) r.entry.term)
    (hz : (spaceOf log).ok r.entry.term = true) (x : Nat) :
    x ∈ derive e (log ++ [r]) ↔ incrFrontier (spaceOf log) e r.entry.term x := by
  have h1 : derive e (log ++ [r]) = deriveS e (spaceOf (log ++ [r])) := rfl
  rw [h1, hproj]
  exact (incremental_equals_full hz x).symm

/- Item 2: reversibility of the action step. An action appends a
   candidate to the space. Its inverse is a compensating
   retraction of exactly that candidate from the eligibility
   view. For a fresh candidate the compensated view equals the
   prior view at every point: the strongest form the append model
   honestly supports, proved here in full. The log level inverse
   is the last-step removal, proved directly. -/

theorem dom_grown (e : Candidate.Epoch) (s : Candidate.Space) (z : Nat) :
    Candidate.dom e (Candidate.grown s z) = Candidate.dom e s := rfl

theorem elig_grown {s : Candidate.Space} {z : Nat} (hz : s.ok z = true)
    (y : Nat) :
    Candidate.elig (Candidate.grown s z) (Candidate.grown s z).cands y ↔
      Candidate.elig s s.cands y ∨ y = z := by
  constructor
  · rintro ⟨hm, hok⟩
    rw [Candidate.grown] at hm
    simp only [List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | rfl
    · exact Or.inl ⟨hm, hok⟩
    · exact Or.inr rfl
  · rintro (⟨hm, hok⟩ | rfl)
    · refine ⟨?_, hok⟩
      rw [Candidate.grown]
      simp only [List.mem_append]
      exact Or.inl hm
    · refine ⟨?_, hz⟩
      rw [Candidate.grown]
      simp only [List.mem_append, List.mem_singleton]
      exact Or.inr (by simp)

def compensated (s : Candidate.Space) (e : Candidate.Epoch) (z x : Nat) :
    Prop :=
  Frontier
    (FrontierSolvable.Retract
      (Candidate.elig (Candidate.grown s z) (Candidate.grown s z).cands)
      (fun y => y = z))
    (Candidate.dom e (Candidate.grown s z)) x

theorem compensate_restores {s : Candidate.Space} {e : Candidate.Epoch}
    {z : Nat} (hz : s.ok z = true) (hfresh : z ∉ s.cands) (x : Nat) :
    compensated s e z x ↔
      Frontier (Candidate.elig s s.cands) (Candidate.dom e s) x := by
  have hview : ∀ y,
      FrontierSolvable.Retract
          (Candidate.elig (Candidate.grown s z) (Candidate.grown s z).cands)
          (fun y => y = z) y ↔
        FrontierSolvable.Retract (Candidate.elig s s.cands)
          (fun y => y = z) y := by
    intro y
    constructor
    · rintro ⟨hy, hyz⟩
      rcases (elig_grown hz y).mp hy with hy | hy
      · exact ⟨hy, hyz⟩
      · exact absurd hy hyz
    · rintro ⟨hy, hyz⟩
      exact ⟨(elig_grown hz y).mpr (Or.inl hy), hyz⟩
  have h1 : compensated s e z x ↔
      Frontier (FrontierSolvable.Retract (Candidate.elig s s.cands)
        (fun y => y = z)) (Candidate.dom e s) x :=
    derived_view_extensional _ _ _ _ hview
      (fun a b => by rw [dom_grown]) x
  refine h1.trans ⟨?_, ?_⟩
  · intro hf
    have hd := (Candidate.drop s e (fun y => y = z) x).mp hf
    refine ⟨hd.1, ?_⟩
    intro y hy hdy
    have hyz := hd.2.2 y hy hdy
    exact absurd (hyz ▸ hy.1) hfresh
  · intro hf
    refine (Candidate.drop s e (fun y => y = z) x).mpr ⟨hf.1, ?_, ?_⟩
    · intro hxz
      exact hfresh (hxz ▸ hf.1.1)
    · intro y hy hdy
      exact absurd hdy (hf.2 y hy)

theorem compensated_solved {s : Candidate.Space} {e : Candidate.Epoch}
    {z : Nat} (hz : s.ok z = true) (hfresh : z ∉ s.cands) (x : Nat) :
    compensated s e z x ↔ x ∈ deriveS e s :=
  (compensate_restores hz hfresh x).trans (Candidate.exact s e x).symm

theorem append_dropLast : ∀ (log : Log) (r : Candidate.Record),
    (log ++ [r]).dropLast = log := by
  intro log r
  rw [List.dropLast_append_of_ne_nil (by simp)]
  simp

/- Item 5: stop soundness. The signal of a log is the length of
   its derived view. Sufficiency is the threshold reaching the
   signal. The loop appends the next record while the signal is
   not sufficient, bounded by fuel. Exit is sound: the loop
   leaves its input unchanged the moment the signal is
   sufficient, and if it returns early it is only because the
   signal was sufficient. Completeness is conditional on the
   progress premise P6, stated as a hypothesis. -/

def signal (e : Candidate.Epoch) (log : Log) : Nat := (derive e log).length

abbrev Sufficient (threshold v : Nat) : Prop := threshold ≤ v

def stepOnce (next : Log → Candidate.Record) (log : Log) : Log :=
  log ++ [next log]

def run (e : Candidate.Epoch) (next : Log → Candidate.Record)
    (threshold : Nat) : Nat → Log → Log
  | 0, log => log
  | fuel + 1, log =>
    if Sufficient threshold (signal e log) then log
    else run e next threshold fuel (stepOnce next log)

theorem run_sound (e : Candidate.Epoch) (next : Log → Candidate.Record)
    (threshold : Nat) :
    ∀ (fuel : Nat) (log : Log),
      Sufficient threshold (signal e (run e next threshold fuel log)) ∨
        log.length + fuel ≤ (run e next threshold fuel log).length := by
  intro fuel
  induction fuel with
  | zero =>
    intro log
    exact Or.inr (by simp [run])
  | succ fuel ih =>
    intro log
    by_cases hs : Sufficient threshold (signal e log)
    · have hrun : run e next threshold (fuel + 1) log = log := by
        simp [run, hs]
      rw [hrun]
      exact Or.inl hs
    · have hrun : run e next threshold (fuel + 1) log =
          run e next threshold fuel (stepOnce next log) := by
        simp [run, hs]
      rw [hrun]
      rcases ih (stepOnce next log) with h | h
      · exact Or.inl h
      · refine Or.inr ?_
        have hlen : (stepOnce next log).length = log.length + 1 := by
          simp [stepOnce]
        omega

theorem run_stops_only_when_sufficient (e : Candidate.Epoch)
    (next : Log → Candidate.Record) (threshold fuel : Nat) (log : Log)
    (h : (run e next threshold fuel log).length < log.length + fuel) :
    Sufficient threshold (signal e (run e next threshold fuel log)) := by
  rcases run_sound e next threshold fuel log with h1 | h1
  · exact h1
  · omega

theorem run_complete (e : Candidate.Epoch)
    (next : Log → Candidate.Record) (threshold : Nat)
    (hprog : ∀ log, ¬ Sufficient threshold (signal e log) →
      signal e log + 1 ≤ signal e (stepOnce next log)) :
    ∀ (fuel : Nat) (log : Log), threshold < signal e log + fuel →
      Sufficient threshold (signal e (run e next threshold fuel log)) := by
  intro fuel
  induction fuel with
  | zero =>
    intro log h
    have hrun : run e next threshold 0 log = log := rfl
    rw [hrun]
    exact Nat.le_of_lt (by simpa using h)
  | succ fuel ih =>
    intro log h
    by_cases hs : Sufficient threshold (signal e log)
    · have hrun : run e next threshold (fuel + 1) log = log := by
        simp [run, hs]
      rw [hrun]
      exact hs
    · have hrun : run e next threshold (fuel + 1) log =
          run e next threshold fuel (stepOnce next log) := by
        simp [run, hs]
      rw [hrun]
      apply ih
      have hp := hprog log hs
      omega

/- Standing controls. Each is a proved statement over a named
   concrete instance. A control that starts failing is a defect
   in the technique. -/

/- Refuted control for the uncompensated action: appending a
   dominating candidate with no compensation removes a solved
   member, so reversibility needs the compensation step. This is
   the candidate module loss control, cited. -/
theorem control_uncompensated :
    0 ∈ deriveS Candidate.epoch.both Candidate.demo ∧
      0 ∉ deriveS Candidate.epoch.both (Candidate.grown Candidate.demo 2) :=
  Candidate.loss

/- Refuted control for selection by ranking head alone: under a
   constant weighting the head of the ranking is candidate zero
   while candidate one dominates it on both axes of the control
   space, so the head of a ranking is the weighted best only for
   its key, and Pareto optimality of the pipeline selection
   comes from the frontier filter, not from the ranking. -/
def controlSpace : Candidate.Space where
  cands := [0, 1]
  read := fun x _ => if x == 0 then 5 else 1
  ok := fun _ => true

theorem control_rank_head :
    (Search.order (fun _ => 0) [0, 1]).head? = some 0 ∧
      Candidate.dom Candidate.epoch.both controlSpace 1 0 := by
  refine ⟨by decide, ?_⟩
  show FrontierSolvable.pareto Candidate.epoch.both.axes controlSpace.read
    1 0 = true
  decide

/- Refuted control for unconditional stop completeness: a step
   whose record never qualifies never raises the signal, so the
   loop spends all its fuel and the signal stays below the
   threshold. Completeness needs the progress premise P6. -/
def controlRecord : Candidate.Record where
  entry := ⟨0, [], []⟩
  score := ⟨0, 0, 0, 0, 0, 0⟩
  seen := false
  wanted := false

theorem control_no_progress :
    signal Candidate.epoch.both
        (run Candidate.epoch.both (fun _ => controlRecord) 1 2 []) = 0 ∧
      (run Candidate.epoch.both (fun _ => controlRecord) 1 2 []).length = 2 := by
  decide

#print axioms select_mem
#print axioms selected_frontier
#print axioms selected_undominated
#print axioms selected_qualified
#print axioms put_head
#print axioms order_head_best
#print axioms ranked_head_best
#print axioms derive_congr
#print axioms intent_congr
#print axioms select_congr
#print axioms derive_of_space_eq
#print axioms derive_exact
#print axioms derive_reweight
#print axioms incremental_equals_full
#print axioms full_from_scratch
#print axioms append_unqualified_no_change
#print axioms incremental_log
#print axioms dom_grown
#print axioms elig_grown
#print axioms compensate_restores
#print axioms compensated_solved
#print axioms append_dropLast
#print axioms run_sound
#print axioms run_stops_only_when_sufficient
#print axioms run_complete
#print axioms control_uncompensated
#print axioms control_rank_head
#print axioms control_no_progress

end Pipeline
