import Frontier
import Hyper
import Search
import Std

namespace Candidate

open FrontierSolvable

/- The candidate record: the behavior a candidate carries, stated as data.
   The term is its own node in the graph. The parts are the terms it is
   composed from. The links are the premise terms it builds on. -/
structure Entry where
  term : Nat
  parts : List Nat
  links : List Nat

/- Net-newness: what the candidate adds that the carried list does not
   already carry. One for its own term when that term is new, plus one
   for each part that is not carried. Computable from the record and
   the carried list alone. -/
def fresh (carried : List Nat) (e : Entry) : Nat :=
  (e.parts.filter (fun p => p ∉ carried)).length +
    (if e.term ∈ carried then 0 else 1)

theorem fresh.done {carried : List Nat} {e : Entry}
    (hp : e.parts = []) (ht : e.term ∈ carried) : fresh carried e = 0 := by
  simp [fresh, hp, ht]

theorem fresh.one {carried : List Nat} {e : Entry}
    (hp : e.parts = []) (ht : e.term ∉ carried) : fresh carried e = 1 := by
  simp [fresh, hp, ht]

/- Impact: how many entries of the space are composed from this
   candidate's term. Computable from the space and the record alone. -/
def reach (space : List Entry) (e : Entry) : Nat :=
  (space.filter (fun d => e.term ∈ d.parts)).length

theorem reach.nil (e : Entry) : reach [] e = 0 := rfl

/- Novelty of composition: a new term composed from carried parts.
   Zero when the term is already carried; otherwise the count of its
   parts that are carried, so a wholly new composition of new parts
   and a recombination of old parts read differently. -/
def blend (carried : List Nat) (e : Entry) : Nat :=
  if e.term ∈ carried then 0
  else (e.parts.filter (fun p => p ∈ carried)).length

theorem blend.done {carried : List Nat} {e : Entry} (hp : e.parts = []) :
    blend carried e = 0 := by
  unfold blend
  rw [hp]
  split <;> rfl

/- The six improvement axes as one score record. Every field is a
   natural number and higher is better on every axis: gain is the
   better axis, speed is the faster axis, lean is the less redundant
   axis, power is the more powerful axis, width is the more expressive
   axis, ease is the more ergonomic axis. The reading turns a score
   into a cost by negation, so the existing dominance vocabulary,
   where lower is better, applies unchanged. Readings off the six
   axes are zero. -/
structure Score where
  gain : Nat
  speed : Nat
  lean : Nat
  power : Nat
  width : Nat
  ease : Nat

def read (s : Score) (i : Nat) : Int :=
  match i with
  | 0 => -(s.gain : Int)
  | 1 => -(s.speed : Int)
  | 2 => -(s.lean : Int)
  | 3 => -(s.power : Int)
  | 4 => -(s.width : Int)
  | 5 => -(s.ease : Int)
  | _ => 0

def axes : List Nat := [0, 1, 2, 3, 4, 5]

namespace score

theorem tie (x y : Score) (h : ∀ i, read x i = read y i) :
    ¬ Dominates read x y :=
  ties_not_dominated read h

theorem exact (x y : Score) :
    pareto axes read x y = true ↔
      (∀ i, i ∈ axes → read x i ≤ read y i) ∧
        ∃ i, i ∈ axes ∧ read x i < read y i :=
  pareto_exact axes read x y

end score

/- A candidate record also carries its two filter inputs. The seen
   input is the observed filter. The wanted input is the intended
   side. Qualification is the intended coloring of the hypergraph
   module applied to exactly these two inputs, so the two filters
   are never conflated here either. -/
structure Record where
  entry : Entry
  score : Score
  seen : Bool
  wanted : Bool

def color (r : Record) : Hyper.Paint.Color :=
  Hyper.Paint.apply r.wanted r.seen

def qualified (r : Record) : Bool := r.seen && r.wanted

namespace record

theorem intended (r : Record) (h : qualified r = true) :
    color r = .intended := by
  have hs : r.seen = true := by
    cases hb : r.seen <;> simp [qualified, hb] at h ⊢ <;> exact hb
  have hw : r.wanted = true := by
    cases hb : r.wanted <;> simp [qualified, hb, hs] at h ⊢ <;> exact hb
  simp [color, Hyper.Paint.apply, hw, hs]

end record

/- The space: a finite list of candidate identifiers, a reading
   function giving each candidate a cost on each axis, and the
   qualification coloring as a boolean predicate. An epoch carries
   the active axes and the confidence weighting. The solved set
   under an epoch is the evaluator of the frontier module run over
   the weighted order, exactly as the search module defines it. -/
structure Space where
  cands : List Nat
  read : Nat → Nat → Int
  ok : Nat → Bool

structure Epoch where
  axes : List Nat
  weight : Nat → Nat

def solved (s : Space) (e : Epoch) : List Nat :=
  compute (Search.order e.weight s.cands) s.ok (pareto e.axes s.read)

def elig (s : Space) (l : List Nat) (y : Nat) : Prop :=
  y ∈ l ∧ s.ok y = true

def dom (e : Epoch) (s : Space) (y x : Nat) : Prop :=
  pareto e.axes s.read y x = true

/- The projection from a list of records to a space: identifiers are
   the record terms, the reading of an identifier is the reading of
   its record's score, and the qualification of an identifier is the
   qualification of its record. An identifier with no record reads
   zero and does not qualify. The solved set of the projected space
   is the solved set of the records, by the definition of solved. -/
def project (rs : List Record) : Space where
  cands := rs.map (fun r => r.entry.term)
  read := fun x i =>
    match rs.find? (fun r => r.entry.term == x) with
    | some r => read r.score i
    | none => 0
  ok := fun x =>
    match rs.find? (fun r => r.entry.term == x) with
    | some r => qualified r
    | none => false

theorem irr (e : Epoch) (s : Space) (x : Nat) : ¬ dom e s x x := by
  intro h
  obtain ⟨-, i, -, hi⟩ := (pareto_exact e.axes s.read x x).mp h
  exact Int.lt_irrefl _ hi

/- The solved set under a weighting epoch is exactly the
   nondominated qualified set of candidates under that epoch's
   measures. This is the search module's full statement joined to
   the candidate space by unfolding two definitions; the frontier
   result itself is cited, not re-proved. -/
theorem exact (s : Space) (e : Epoch) (x : Nat) :
    x ∈ solved s e ↔
      Frontier (elig s s.cands) (dom e s) x :=
  Search.full e.weight s.cands s.ok (pareto e.axes s.read) x

/- Membership in the solved set does not depend on the weighting at
   all, only on the epoch's axes: the weighting orders the search
   and never bounds it. Two epochs with the same axes solve the
   same set. -/
theorem same {s : Space} {e e' : Epoch} (h : e.axes = e'.axes) (x : Nat) :
    x ∈ solved s e ↔ x ∈ solved s e' := by
  have hd : pareto e'.axes s.read = pareto e.axes s.read := by rw [h]
  show x ∈ compute (Search.order e.weight s.cands) s.ok (pareto e.axes s.read) ↔
    x ∈ compute (Search.order e'.weight s.cands) s.ok (pareto e'.axes s.read)
  rw [hd]
  exact Search.reweight e.weight e'.weight s.cands s.ok (pareto e.axes s.read) x

def grown (s : Space) (z : Nat) : Space :=
  { s with cands := s.cands ++ [z] }

/- Semi-persistence, from-scratch form: the solved set of the grown
   space, computed through the epoch's weighted order, has exactly
   the members of a from-scratch solve of the grown candidate list.
   This is the search module's weighted statement applied to the
   grown list. -/
theorem fresh.solve (s : Space) (e : Epoch) (z x : Nat) :
    x ∈ solved (grown s z) e ↔
      x ∈ compute (s.cands ++ [z]) s.ok (pareto e.axes s.read) :=
  Search.weighted e.weight (s.cands ++ [z]) s.ok (pareto e.axes s.read) x

/- Semi-persistence, incremental form: when a qualified candidate
   is appended, the new frontier predicate is the old frontier
   filtered by the appended candidate, plus the appended candidate
   when nothing old dominates it. This is the frontier module's
   insertion exactness, transported to list append by view
   extensionality. The side condition is that the appended
   candidate is qualified; the next result covers the other case. -/
theorem grow (s : Space) (e : Epoch) (z : Nat) (hz : s.ok z = true) (x : Nat) :
    Frontier (elig s (s.cands ++ [z])) (dom e s) x ↔
      (Frontier (elig s s.cands) (dom e s) x ∧ ¬ dom e s z x) ∨
        (x = z ∧ ∀ y, elig s s.cands y → ¬ dom e s y z) := by
  have hview : ∀ y, elig s (s.cands ++ [z]) y ↔ Insert (elig s s.cands) z y := by
    intro y
    constructor
    · rintro ⟨hy, hok⟩
      rw [List.mem_append] at hy
      rcases hy with hy | hy
      · exact Or.inl ⟨hy, hok⟩
      · exact Or.inr (List.mem_singleton.mp hy)
    · rintro (⟨hy, hok⟩ | rfl)
      · exact ⟨List.mem_append.mpr (Or.inl hy), hok⟩
      · exact ⟨List.mem_append.mpr (Or.inr (List.mem_singleton_self _)), hz⟩
  exact (derived_view_extensional _ _ _ _ hview (fun _ _ => Iff.rfl) x).trans
    (insertion_exact (elig s s.cands) (dom e s) (irr e s) z x)

/- The solved-set form of the same update, through the epoch. -/
theorem step (s : Space) (e : Epoch) (z : Nat) (hz : s.ok z = true) (x : Nat) :
    x ∈ solved (grown s z) e ↔
      (Frontier (elig s s.cands) (dom e s) x ∧ ¬ dom e s z x) ∨
        (x = z ∧ ∀ y, elig s s.cands y → ¬ dom e s y z) :=
  (exact (grown s z) e x).trans (grow s e z hz x)

/- Appending a disqualified candidate changes nothing: its
   eligibility view is the old view, so the frontiers agree by
   extensionality. Disqualification is a coloring change, and this
   is its exact update. -/
theorem grow.dead (s : Space) (e : Epoch) (z : Nat) (hz : s.ok z = false)
    (x : Nat) :
    x ∈ solved (grown s z) e ↔ x ∈ solved s e := by
  have hview : ∀ y, elig s (s.cands ++ [z]) y ↔ elig s s.cands y := by
    intro y
    constructor
    · rintro ⟨hy, hok⟩
      rw [List.mem_append] at hy
      rcases hy with hy | hy
      · exact ⟨hy, hok⟩
      · have hyz : y = z := List.mem_singleton.mp hy
        rw [hyz, hz] at hok
        exact absurd hok (by decide)
    · rintro ⟨hy, hok⟩
      exact ⟨List.mem_append.mpr (Or.inl hy), hok⟩
  exact (exact (grown s z) e x).trans
    ((derived_view_extensional _ _ _ _ hview (fun _ _ => Iff.rfl) x).trans
      (exact s e x).symm)

def joined (s : Space) (extra : List Nat) : Space :=
  { s with cands := s.cands ++ extra }

/- Joining a second candidate list: the solved predicate of the
   joined space is the frontier predicate over the joined
   membership. This is the search module's join frontier statement
   joined through the epoch weighting. -/
theorem join (s : Space) (e : Epoch) (extra : List Nat) (x : Nat) :
    x ∈ solved (joined s extra) e ↔
      Frontier (fun y => (y ∈ s.cands ∨ y ∈ extra) ∧ s.ok y = true)
        (dom e s) x := by
  have h1 : x ∈ solved (joined s extra) e ↔
      x ∈ compute (s.cands ++ extra) s.ok (pareto e.axes s.read) :=
    Search.weighted e.weight (s.cands ++ extra) s.ok (pareto e.axes s.read) x
  exact h1.trans (Search.join.frontier s.cands extra s.ok (pareto e.axes s.read) x)

/- Retraction, the coloring-change update in the other direction:
   removing an eligibility set exposes exactly the candidates whose
   every former dominator was removed. This is the frontier
   module's retraction exactness, stated for the candidate space. -/
theorem drop (s : Space) (e : Epoch) (gone : Nat → Prop) (x : Nat) :
    Frontier (Retract (elig s s.cands) gone) (dom e s) x ↔
      elig s s.cands x ∧ ¬ gone x ∧
        ∀ y, elig s s.cands y → dom e s y x → gone y :=
  retraction_exact (elig s s.cands) gone (dom e s) x

/- Epochs as appended records. The solved set at an epoch index is
   a function of that index's record alone. -/
def history (epochs : List Epoch) (s : Space) (k : Nat) : List Nat :=
  match epochs[k]? with
  | some e => solved s e
  | none => []

theorem replay {epochs epochs' : List Epoch} {k : Nat}
    (h : epochs[k]? = epochs'[k]?) (s : Space) :
    history epochs s k = history epochs' s k := by
  unfold history
  rw [h]

theorem keep : ∀ (epochs : List Epoch) (k : Nat), k < epochs.length →
    ∀ (e : Epoch) (s : Space),
      history (epochs ++ [e]) s k = history epochs s k := by
  intro epochs
  induction epochs with
  | nil =>
    intro k hk
    simp at hk
  | cons a rest ih =>
    intro k hk e s
    cases k with
    | zero => rfl
    | succ k =>
      have hk' : k < rest.length := by
        simpa using hk
      exact ih k hk' e s

/- A gap is a first-class object of the same space: a list of axes
   and a target reading on them, carried under its own term. A
   candidate closes the gap when it dominates the target reading on
   the gap's axes, under the reading that sends the gap's term to
   its target and every other term to the space's reading. The
   gap's own size measure is its axis count. -/
structure Gap where
  axes : List Nat
  mark : Nat → Int
  term : Nat
  since : Nat

def gsize (g : Gap) : Nat := g.axes.length

def closes (s : Space) (g : Gap) (c : Nat) : Bool :=
  pareto g.axes
    (fun x i => if x == g.term then g.mark i else s.read x i) c g.term

def solves (s : Space) (gaps : List Gap) (c : Nat) : Nat :=
  (gaps.filter (fun g => closes s g c)).length

/- The rest of the gap's own measure vector. Reach: the count of
   candidates of the space that close the gap, the dual of impact.
   Open width: the count of the gap's axes on which every candidate
   still reads above the mark. Age: the count of epoch records
   since the epoch index at which the gap entered. -/
def greach (s : Space) (g : Gap) : Nat :=
  (s.cands.filter (closes s g)).length

def gopen (s : Space) (g : Gap) : Nat :=
  (g.axes.filter (fun i => s.cands.all (fun c => g.mark i < s.read c i))).length

def gage (epochs : List Epoch) (g : Gap) : Nat :=
  epochs.length - g.since

def scan (s : Space) (g : Gap) : Option Nat :=
  s.cands.find? (closes s g)

theorem hit {s : Space} {g : Gap} {c : Nat} (h : scan s g = some c) :
    c ∈ s.cands ∧ closes s g c = true := by
  have hmem : c ∈ s.cands := List.mem_of_find?_eq_some h
  obtain ⟨hp, -, -, -, -⟩ := List.find?_eq_some_iff_append.mp h
  exact ⟨hmem, hp⟩

theorem miss {s : Space} {g : Gap} (h : scan s g = none) :
    ∀ c ∈ s.cands, closes s g c = false := by
  intro c hc
  have hall := List.find?_eq_none.mp h c hc
  cases hc' : closes s g c with
  | false => rfl
  | true => exact absurd hc' (by simpa using hall)

def solvable (s : Space) (g : Gap) :
    Decidable (∃ c, c ∈ s.cands ∧ closes s g c = true) :=
  List.decidableBEx (fun c => closes s g c = true) s.cands

theorem bound (s : Space) (g : Gap) :
    (s.cands.filter (closes s g)).length ≤ s.cands.length :=
  List.length_filter_le _ _

/- Standing controls. Each is a proved statement over a named
   concrete instance, in the style of the search module's controls.
   A control that starts failing is a defect in the technique. -/

def demo : Space where
  cands := [0, 1]
  read := fun x i =>
    match x, i with
    | 0, 0 => 1
    | 0, _ => 10
    | 1, 0 => 10
    | 1, _ => 1
    | _, _ => 0
  ok := fun _ => true

namespace epoch

def first : Epoch := ⟨[0], fun _ => 0⟩
def second : Epoch := ⟨[1], fun _ => 0⟩
def both : Epoch := ⟨[0, 1], fun _ => 0⟩

/- Refuted control: a change of epoch axes preserves the solved
   set. On the demo space the first axis alone solves candidate
   zero and the second axis alone solves candidate one, so the
   solved sets differ. An epoch change is a change of measures,
   not a reweighting; the same-axes result above is the exact
   boundary of what a reweighting preserves. -/
theorem shift : solved demo first ≠ solved demo second := by decide

end epoch

/- Refuted control: appending a candidate never removes a solved
   member. Candidate two of the demo readings dominates both axes,
   so appending it to the demo space removes candidate zero from
   the solved set under the two-axis epoch. Semi-persistence is
   exactness of the update, not monotonicity of membership. -/
theorem loss :
    0 ∈ solved demo epoch.both ∧ 0 ∉ solved (grown demo 2) epoch.both := by
  decide

#print axioms exact
#print axioms same
#print axioms irr
#print axioms fresh.solve
#print axioms grow
#print axioms step
#print axioms grow.dead
#print axioms join
#print axioms drop
#print axioms replay
#print axioms keep
#print axioms hit
#print axioms miss
#print axioms bound
#print axioms score.tie
#print axioms score.exact
#print axioms record.intended
#print axioms fresh.done
#print axioms blend.done
#print axioms epoch.shift
#print axioms loss

end Candidate
