import CanonicalDominance
import ComparisonContract
import FiniteFrontier
import FiniteSchedules
import GeneralPareto
import Hyper
import SoftwareIsQuantifiable.Interface
import ThreeValuedGate

open SoftwareIsQuantifiable

namespace Solve

def run {Impl : Type} {c : ComparisonContract.Contract}
    (space : ThreeValuedGate.FiniteSpace Impl c) : List Impl :=
  FiniteFrontier.frontier space.candidates
    (fun y z => ThreeValuedGate.dominatesB c (space.readings y) (space.readings z))

def dominator {Impl : Type} {c : ComparisonContract.Contract}
    (space : ThreeValuedGate.FiniteSpace Impl c) (point : Impl) : Option Impl :=
  space.candidates.find? fun other =>
    ThreeValuedGate.dominatesB c (space.readings other) (space.readings point)

def accept {Impl : Type} {c : ComparisonContract.Contract}
    [DecidableEq Impl] (space : ThreeValuedGate.FiniteSpace Impl c) : Bool :=
  FiniteFrontier.certificate space.candidates (run space)
    (fun y z => ThreeValuedGate.dominatesB c (space.readings y) (space.readings z))

structure Card (Impl : Type) where
  point : Impl
  dominator : Option Impl
  accept : Bool
  deriving Repr

def cards {Impl : Type} {c : ComparisonContract.Contract} [DecidableEq Impl]
    (space : ThreeValuedGate.FiniteSpace Impl c) : List (Card Impl) :=
  (run space).map fun point =>
    { point := point
      dominator := dominator space point
      accept := accept space }

theorem refused (c : ComparisonContract.Contract) (x y : List (Option Int)) (i : Nat)
    (hi : i ∈ List.range c.axes.length)
    (hu : ThreeValuedGate.axisVerdict c x y i = .unknown) :
    ¬ ThreeValuedGate.dominates c x y ∧
      ¬ Interface.dominates (ThreeValuedGate.measureSpace c)
        (ThreeValuedGate.toProfile c x) (ThreeValuedGate.toProfile c y) :=
  ⟨ThreeValuedGate.unknown_blocks_dominance c x y i hi hu,
    ThreeValuedGate.unknown_blocks_dominance_canonical c x y i hi hu⟩

theorem canonical {c : ComparisonContract.Contract} (ns ms : List Nat)
    (hn : ns.length = c.axes.length) (hm : ms.length = c.axes.length) :
    ThreeValuedGate.dominates c (ns.map fun n => some (Int.ofNat n))
        (ms.map fun n => some (Int.ofNat n)) ↔
      Interface.dominates (ThreeValuedGate.measureSpace c)
        (ThreeValuedGate.toProfile c (ns.map fun n => some (Int.ofNat n)))
        (ThreeValuedGate.toProfile c (ms.map fun n => some (Int.ofNat n))) :=
  ThreeValuedGate.known_agrees_canonical c ns ms hn hm

def mat {Impl : Type} (c : ComparisonContract.Contract) (read : Impl → List (Option Int))
    (point : Impl) (i : Nat) : Int :=
  ComparisonContract.cost c (ThreeValuedGate.materialized c (read point)) i

theorem present (ns : List Nat) (i : Nat) (hi : i < ns.length) :
    ThreeValuedGate.reading (ns.map fun n => some (Int.ofNat n)) i ≠ none := by
  simp [ThreeValuedGate.reading, List.getElem?_map, List.getElem?_eq_getElem hi]

theorem gaps {Impl : Type} {c : ComparisonContract.Contract}
    (space : ThreeValuedGate.FiniteSpace Impl c)
    (hshape : ∀ x, ∃ ns : List Nat, ns.length = c.axes.length ∧
      space.readings x = ns.map fun n => some (Int.ofNat n))
    (x : Impl) (i : Nat) (hi : i < c.axes.length) :
    ThreeValuedGate.reading (space.readings x) i ≠ none := by
  obtain ⟨ns, hlen, hx⟩ := hshape x
  rw [hx]
  exact present ns i (by omega)

theorem bridge {Impl : Type} {c : ComparisonContract.Contract}
    (space : ThreeValuedGate.FiniteSpace Impl c)
    (hshape : ∀ x, ∃ ns : List Nat, ns.length = c.axes.length ∧
      space.readings x = ns.map fun n => some (Int.ofNat n))
    (y z : Impl) :
    ThreeValuedGate.dominatesB c (space.readings y) (space.readings z) = true ↔
      FiniteFrontier.strictPareto (List.range c.axes.length) (mat c space.readings) y z = true := by
  obtain ⟨ny, hny, hy⟩ := hshape y
  obtain ⟨nz, hnz, hz⟩ := hshape z
  have hmy : ThreeValuedGate.materialized c (ny.map fun n => some (Int.ofNat n)) = ny.map Int.ofNat := by
    apply List.ext_getElem
    · simp [ThreeValuedGate.materialized, hny]
    · intro i hi _
      have hidx : i < ny.length := by
        simpa [ThreeValuedGate.materialized, hny] using hi
      have hget : ny[i]? = some ny[i] := List.getElem?_eq_getElem hidx
      simp [ThreeValuedGate.materialized, ThreeValuedGate.reading, List.getElem_map,
        List.getElem_range, hget]
  have hmz : ThreeValuedGate.materialized c (nz.map fun n => some (Int.ofNat n)) = nz.map Int.ofNat := by
    apply List.ext_getElem
    · simp [ThreeValuedGate.materialized, hnz]
    · intro i hi _
      have hidx : i < nz.length := by
        simpa [ThreeValuedGate.materialized, hnz] using hi
      have hget : nz[i]? = some nz[i] := List.getElem?_eq_getElem hidx
      simp [ThreeValuedGate.materialized, ThreeValuedGate.reading, List.getElem_map,
        List.getElem_range, hget]
  have hcosty : ∀ i, mat c space.readings y i =
      ComparisonContract.cost c (ny.map Int.ofNat) i := by
    intro i
    simp only [mat]
    rw [hy, hmy]
  have hcostz : ∀ i, mat c space.readings z i =
      ComparisonContract.cost c (nz.map Int.ofNat) i := by
    intro i
    simp only [mat]
    rw [hz, hmz]
  rw [ThreeValuedGate.dominatesB_iff, hy, hz]
  rw [ThreeValuedGate.dominates_materialized c
      (ny.map fun n => some (Int.ofNat n)) (nz.map fun n => some (Int.ofNat n))
      (fun i hi => present ny i (by omega)) (fun i hi => present nz i (by omega))]
  rw [hmy, hmz]
  rw [ThreeValuedGate.known_dominates_iff_bool c (ny.map Int.ofNat) (nz.map Int.ofNat)
    (by simp [hny]) (by simp [hnz])]
  rw [ComparisonContract.dominates, FiniteFrontier.pareto_exact, FiniteFrontier.pareto_exact]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro i hi
      simpa [hcosty, hcostz] using h.1 i hi
    · obtain ⟨i, hi, hlt⟩ := h.2
      exact ⟨i, hi, by simpa [hcosty, hcostz] using hlt⟩
  · intro h
    refine ⟨?_, ?_⟩
    · intro i hi
      simpa [hcosty, hcostz] using h.1 i hi
    · obtain ⟨i, hi, hlt⟩ := h.2
      exact ⟨i, hi, by simpa [hcosty, hcostz] using hlt⟩

theorem samepred {Impl : Type} {c : ComparisonContract.Contract}
    (space : ThreeValuedGate.FiniteSpace Impl c)
    (hshape : ∀ x, ∃ ns : List Nat, ns.length = c.axes.length ∧
      space.readings x = ns.map fun n => some (Int.ofNat n)) :
    (fun y z => ThreeValuedGate.dominatesB c (space.readings y) (space.readings z)) =
      fun y z => FiniteFrontier.strictPareto (List.range c.axes.length) (mat c space.readings) y z := by
  funext y z
  cases hb : ThreeValuedGate.dominatesB c (space.readings y) (space.readings z) <;>
    cases hs : FiniteFrontier.strictPareto (List.range c.axes.length) (mat c space.readings) y z
  · rfl
  · exact absurd ((bridge space hshape y z).mpr hs) (by simp [hb])
  · exact absurd ((bridge space hshape y z).mp hb) (by simp [hs])
  · rfl

theorem main {Impl : Type} {c : ComparisonContract.Contract}
    (space : ThreeValuedGate.FiniteSpace Impl c)
    (hshape : ∀ x, ∃ ns : List Nat, ns.length = c.axes.length ∧
      space.readings x = ns.map fun n => some (Int.ofNat n)) :
    run space = FiniteFrontier.frontier space.candidates
        (fun y z => ThreeValuedGate.dominatesB c (space.readings y) (space.readings z)) ∧
      (∀ x, x ∈ run space → ∀ impl,
        ComparisonContract.dominates c
          (ThreeValuedGate.materialized c (space.readings impl))
          (ThreeValuedGate.materialized c (space.readings x)) = false) ∧
      (∀ x, x ∈ run space → ∀ y,
        ¬ Interface.dominates (ThreeValuedGate.measureSpace c)
          (ThreeValuedGate.toProfile c (space.readings y))
          (ThreeValuedGate.toProfile c (space.readings x))) ∧
      (∀ x, (∀ y, ¬ Interface.dominates (ThreeValuedGate.measureSpace c)
          (ThreeValuedGate.toProfile c (space.readings y))
          (ThreeValuedGate.toProfile c (space.readings x))) → x ∈ run space) ∧
      (∀ x, (∀ y, ¬ Interface.dominates (ThreeValuedGate.measureSpace c)
          (ThreeValuedGate.toProfile c (space.readings y))
          (ThreeValuedGate.toProfile c (space.readings x))) →
        ∃ z, z ∈ run space ∧ space.readings z = space.readings x) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · intro x hx impl
    exact ThreeValuedGate.frontier_no_dominator space x (by simpa [run] using hx) impl
  · intro x hx y hdom
    obtain ⟨ny, hny, hy⟩ := hshape y
    obtain ⟨nx, hnx, hxeq⟩ := hshape x
    have hkv : ThreeValuedGate.dominates c (space.readings y) (space.readings x) := by
      rw [hy, hxeq]
      exact (canonical ny nx hny hnx).mpr (by simpa [hy, hxeq] using hdom)
    have hb := (ThreeValuedGate.dominatesB_iff c (space.readings y) (space.readings x)).mpr hkv
    have hnd := ((FiniteFrontier.frontier_exact space.candidates
      (fun a b => ThreeValuedGate.dominatesB c (space.readings a) (space.readings b)) x).mp
      (by simpa [run] using hx)).2 y (space.nothingOutside y)
    rw [hb] at hnd
    cases hnd
  · intro x hnot
    have hbool : ∀ y, ThreeValuedGate.dominatesB c (space.readings y) (space.readings x) = false := by
      intro y
      cases hb : ThreeValuedGate.dominatesB c (space.readings y) (space.readings x) with
      | false => rfl
      | true =>
        have hkv := (ThreeValuedGate.dominatesB_iff c (space.readings y) (space.readings x)).mp hb
        obtain ⟨ny, hny, hy⟩ := hshape y
        obtain ⟨nx, hnx, hxeq⟩ := hshape x
        have hdom : Interface.dominates (ThreeValuedGate.measureSpace c)
            (ThreeValuedGate.toProfile c (space.readings y))
            (ThreeValuedGate.toProfile c (space.readings x)) := by
          rw [hy, hxeq]
          exact (canonical ny nx hny hnx).mp (by simpa [hy, hxeq] using hkv)
        exact False.elim (hnot y hdom)
    exact (FiniteFrontier.frontier_exact space.candidates
      (fun a b => ThreeValuedGate.dominatesB c (space.readings a) (space.readings b)) x).mpr
      ⟨space.nothingOutside x, fun y _ => hbool y⟩
  · intro x hnot
    exact ⟨x, (by
      have hbool : ∀ y, ThreeValuedGate.dominatesB c (space.readings y) (space.readings x) = false := by
        intro y
        cases hb : ThreeValuedGate.dominatesB c (space.readings y) (space.readings x) with
        | false => rfl
        | true =>
          have hkv := (ThreeValuedGate.dominatesB_iff c (space.readings y) (space.readings x)).mp hb
          obtain ⟨ny, hny, hy⟩ := hshape y
          obtain ⟨nx, hnx, hxeq⟩ := hshape x
          have hdom : Interface.dominates (ThreeValuedGate.measureSpace c)
              (ThreeValuedGate.toProfile c (space.readings y))
              (ThreeValuedGate.toProfile c (space.readings x)) := by
            rw [hy, hxeq]
            exact (canonical ny nx hny hnx).mp (by simpa [hy, hxeq] using hkv)
          exact False.elim (hnot y hdom)
      exact (FiniteFrontier.frontier_exact space.candidates
        (fun a b => ThreeValuedGate.dominatesB c (space.readings a) (space.readings b)) x).mpr
        ⟨space.nothingOutside x, fun y _ => hbool y⟩), rfl⟩

theorem checked {Impl : Type} {c : ComparisonContract.Contract} [DecidableEq Impl]
    (space : ThreeValuedGate.FiniteSpace Impl c)
    (hshape : ∀ x, ∃ ns : List Nat, ns.length = c.axes.length ∧
      space.readings x = ns.map fun n => some (Int.ofNat n)) :
    accept space = true := by
  have hsame := samepred space hshape
  apply (FiniteFrontier.certificate_exact space.candidates (run space)
    (fun y z => ThreeValuedGate.dominatesB c (space.readings y) (space.readings z))).mpr
  constructor
  · intro x hx
    exact (FiniteFrontier.frontier_exact space.candidates
      (fun y z => ThreeValuedGate.dominatesB c (space.readings y) (space.readings z)) x).mp hx
  · intro x hx
    have hxfront : x ∈ FiniteFrontier.frontier space.candidates
        (fun y z => FiniteFrontier.strictPareto (List.range c.axes.length) (mat c space.readings) y z) ∨
        ∃ y, y ∈ FiniteFrontier.frontier space.candidates
          (fun y z => FiniteFrontier.strictPareto (List.range c.axes.length) (mat c space.readings) y z) ∧
          FiniteFrontier.strictPareto (List.range c.axes.length) (mat c space.readings) y x = true :=
      GeneralPareto.frontier_complete hx
    have hfront : FiniteFrontier.frontier space.candidates
        (fun y z => FiniteFrontier.strictPareto (List.range c.axes.length) (mat c space.readings) y z) =
        run space := by
      simp only [run]
      congr 1
      exact hsame.symm
    rcases hxfront with hin | ⟨y, hy, hd⟩
    · exact Or.inl (by simpa [hfront] using hin)
    · refine Or.inr ⟨y, by simpa [hfront] using hy, ?_⟩
      exact (bridge space hshape y x).mpr hd

theorem witness {Impl : Type} {c : ComparisonContract.Contract}
    (space : ThreeValuedGate.FiniteSpace Impl c) (point other : Impl)
    (h : dominator space point = some other) :
    other ∈ space.candidates ∧
      ThreeValuedGate.dominatesB c (space.readings other) (space.readings point) = true := by
  have hmem := (List.find?_eq_some_iff_append.mp h).1
  exact ⟨List.mem_of_find?_eq_some h, hmem⟩

theorem named {Impl : Type} {c : ComparisonContract.Contract}
    (space : ThreeValuedGate.FiniteSpace Impl c)
    (hshape : ∀ x, ∃ ns : List Nat, ns.length = c.axes.length ∧
      space.readings x = ns.map fun n => some (Int.ofNat n))
    (point : Impl) (h : point ∉ run space) :
    ∃ other, dominator space point = some other ∧
      Interface.dominates (ThreeValuedGate.measureSpace c)
        (ThreeValuedGate.toProfile c (space.readings other))
        (ThreeValuedGate.toProfile c (space.readings point)) := by
  have hmem := space.nothingOutside point
  have hsame := samepred space hshape
  have hfront : point ∈ FiniteFrontier.frontier space.candidates
      (fun y z => FiniteFrontier.strictPareto (List.range c.axes.length) (mat c space.readings) y z) ∨
      ∃ y, y ∈ FiniteFrontier.frontier space.candidates
        (fun y z => FiniteFrontier.strictPareto (List.range c.axes.length) (mat c space.readings) y z) ∧
        FiniteFrontier.strictPareto (List.range c.axes.length) (mat c space.readings) y point = true :=
    GeneralPareto.frontier_complete hmem
  have hrun : FiniteFrontier.frontier space.candidates
      (fun y z => FiniteFrontier.strictPareto (List.range c.axes.length) (mat c space.readings) y z) =
      run space := by
    simp only [run]
    congr 1
    exact hsame.symm
  rcases hfront with hin | ⟨y, _, hd⟩
  · exact False.elim (h (by simpa [hrun] using hin))
  · have hb := (bridge space hshape y point).mpr hd
    have hfind : dominator space point ≠ none := by
      intro hnone
      have hall := (List.find?_eq_none.mp (by simpa [dominator] using hnone)) y
        (space.nothingOutside y)
      exact hall hb
    cases hf : dominator space point with
    | none => exact False.elim (hfind hf)
    | some other =>
      have hbeat := (witness space point other hf).2
      obtain ⟨no, hno, ho⟩ := hshape other
      obtain ⟨np, hnp, hp⟩ := hshape point
      refine ⟨other, rfl, ?_⟩
      rw [ho, hp]
      exact (canonical no np hno hnp).mp
        ((ThreeValuedGate.dominatesB_iff c
          (no.map fun n => some (Int.ofNat n)) (np.map fun n => some (Int.ofNat n))).mp
          (by simpa [ho, hp] using hbeat))

theorem cardsound {Impl : Type} {c : ComparisonContract.Contract} [DecidableEq Impl]
    (space : ThreeValuedGate.FiniteSpace Impl c)
    (hshape : ∀ x, ∃ ns : List Nat, ns.length = c.axes.length ∧
      space.readings x = ns.map fun n => some (Int.ofNat n))
    (card : Card Impl) (h : card ∈ cards space) :
    card.accept = true ∧ card.dominator = none := by
  simp only [cards, List.mem_map] at h
  obtain ⟨point, hpoint, rfl⟩ := h
  refine ⟨by simpa [accept] using checked space hshape, ?_⟩
  cases hd : dominator space point with
  | none => rfl
  | some other =>
    have hbeat := (witness space point other hd).2
    have hnd := ((FiniteFrontier.frontier_exact space.candidates
      (fun y z => ThreeValuedGate.dominatesB c (space.readings y) (space.readings z)) point).mp
      hpoint).2 other (space.nothingOutside other)
    rw [hbeat] at hnd
    cases hnd

namespace Sched

def contract : ComparisonContract.Contract :=
  ⟨[⟨0, 0, .maximize, 0⟩, ⟨1, 0, .minimize, 0⟩, ⟨2, 0, .minimize, 0⟩], 0, 0, 0⟩

def clarified (good : List Nat) (covers : Nat → List Nat) (plan : FiniteSchedules.Schedule) : Nat :=
  (good.filter fun state => ((List.range plan.length).flatMap covers).contains state).length

def span (duration : Nat → Nat) (plan : FiniteSchedules.Schedule) : Nat :=
  (List.range plan.length).foldl
    (fun acc i => max acc (FiniteSchedules.start plan i + duration i)) 0

def used (plan : FiniteSchedules.Schedule) : Nat :=
  ((List.range plan.length).map (FiniteSchedules.venue plan)).eraseDups.length

def readings (good : List Nat) (covers : Nat → List Nat) (duration : Nat → Nat)
    (plan : FiniteSchedules.Schedule) : List (Option Int) :=
  [some (Int.ofNat (clarified good covers plan)),
    some (Int.ofNat (span duration plan)),
    some (Int.ofNat (used plan))]

def plans (jobs venues horizon : Nat) (duration : Nat → Nat) (deps : List (Nat × Nat)) :=
  FiniteSchedules.feasibleSchedules jobs venues horizon duration deps

def forward (deps : List (Nat × Nat)) : Prop :=
  ∀ edge, edge ∈ deps → edge.1 < edge.2

theorem acyclic (deps : List (Nat × Nat)) (h : forward deps) (node : Nat) :
    ¬ Relation.TransGen (fun left right => (left, right) ∈ deps) node node := by
  intro loop
  have climb : ∀ left right,
      Relation.TransGen (fun left right => (left, right) ∈ deps) left right → left < right := by
    intro left right step
    induction step with
    | single hs => exact h _ hs
    | tail _ hs ih => exact Nat.lt_trans ih (h _ hs)
  exact Nat.lt_irrefl node (climb node node loop)

def space (jobs venues horizon : Nat) (duration : Nat → Nat) (deps : List (Nat × Nat))
    (good : List Nat) (covers : Nat → List Nat) :
    ThreeValuedGate.FiniteSpace (Fin (plans jobs venues horizon duration deps).length) contract :=
  let listed := plans jobs venues horizon duration deps
  { candidates := List.finRange listed.length
    readings := fun index => readings good covers duration (listed.get index)
    nothingOutside := fun index => by simp [List.finRange, List.mem_ofFn]
    noCoverageGaps := fun _index _mem i hi => by
      have hi3 : i < 3 := by simpa [contract] using hi
      match i with
      | 0 => simp [readings, ThreeValuedGate.reading]
      | 1 => simp [readings, ThreeValuedGate.reading]
      | 2 => simp [readings, ThreeValuedGate.reading]
      | n + 3 => omega }

theorem shape (jobs venues horizon : Nat) (duration : Nat → Nat) (deps : List (Nat × Nat))
    (good : List Nat) (covers : Nat → List Nat) :
    ∀ index, ∃ ns : List Nat, ns.length = contract.axes.length ∧
      (space jobs venues horizon duration deps good covers).readings index =
        ns.map fun n => some (Int.ofNat n) := by
  intro index
  let plan := (plans jobs venues horizon duration deps).get index
  refine ⟨[clarified good covers plan, span duration plan, used plan], ?_, ?_⟩
  · simp [contract]
  · simp [space, readings, plan]

theorem admitted (jobs venues horizon : Nat) (duration : Nat → Nat) (deps : List (Nat × Nat))
    (plan : FiniteSchedules.Schedule)
    (h : plan ∈ plans jobs venues horizon duration deps) :
    FiniteSchedules.Feasible jobs venues horizon duration deps plan :=
  (FiniteSchedules.feasibleSchedules_exact jobs venues horizon duration deps plan).mp h

theorem frontier (jobs venues horizon : Nat) (duration : Nat → Nat) (deps : List (Nat × Nat))
    (good : List Nat) (covers : Nat → List Nat) :
    let sp := space jobs venues horizon duration deps good covers
    _root_.Solve.run sp = FiniteFrontier.frontier sp.candidates
        (fun y z => ThreeValuedGate.dominatesB contract (sp.readings y) (sp.readings z)) ∧
      (∀ x, x ∈ _root_.Solve.run sp → ∀ impl,
        ComparisonContract.dominates contract
          (ThreeValuedGate.materialized contract (sp.readings impl))
          (ThreeValuedGate.materialized contract (sp.readings x)) = false) ∧
      (∀ x, x ∈ _root_.Solve.run sp → ∀ y,
        ¬ Interface.dominates (ThreeValuedGate.measureSpace contract)
          (ThreeValuedGate.toProfile contract (sp.readings y))
          (ThreeValuedGate.toProfile contract (sp.readings x))) ∧
      (∀ x, (∀ y, ¬ Interface.dominates (ThreeValuedGate.measureSpace contract)
          (ThreeValuedGate.toProfile contract (sp.readings y))
          (ThreeValuedGate.toProfile contract (sp.readings x))) → x ∈ _root_.Solve.run sp) ∧
      (∀ x, (∀ y, ¬ Interface.dominates (ThreeValuedGate.measureSpace contract)
          (ThreeValuedGate.toProfile contract (sp.readings y))
          (ThreeValuedGate.toProfile contract (sp.readings x))) →
        ∃ z, z ∈ _root_.Solve.run sp ∧ sp.readings z = sp.readings x) :=
  main (space jobs venues horizon duration deps good covers)
    (shape jobs venues horizon duration deps good covers)

def slot (tone : Hyper.Paint.Color) : List (Option Int) :=
  match tone with
  | .unknown => [none]
  | .intended => [some 1]
  | .stray => [some 0]
  | .gap => [some 0]

theorem gapblocks (tone : Hyper.Paint.Color) (h : tone = .unknown) :
    ¬ ThreeValuedGate.dominates ThreeValuedGate.contractMin (slot tone) [some 1] ∧
      ¬ Interface.dominates (ThreeValuedGate.measureSpace ThreeValuedGate.contractMin)
        (ThreeValuedGate.toProfile ThreeValuedGate.contractMin (slot tone))
        (ThreeValuedGate.toProfile ThreeValuedGate.contractMin [some 1]) := by
  subst h
  exact Solve.refused ThreeValuedGate.contractMin [none] [some 1] 0
    (by simp [ThreeValuedGate.contractMin]) (by decide)

theorem skipped (g : Hyper.Graph) (dial : Nat) (want : Nat → Bool) (state : Nat)
    (h : Hyper.Paint.color g dial want state = .unknown) :
    state ∉ Hyper.Paint.qualified g dial want := by
  intro member
  have meant := Hyper.Paint.qualifiedmeant g dial want state member
  rw [h] at meant
  simp [Hyper.Paint.meant] at meant

end Sched

namespace Bench

def contract : ComparisonContract.Contract :=
  ⟨[⟨0, 0, .maximize, 0⟩, ⟨1, 0, .minimize, 0⟩, ⟨2, 0, .minimize, 0⟩], 0, 0, 0⟩

def reduction (plan : FiniteSchedules.Schedule) : Nat :=
  (List.range plan.length).foldl
    (fun acc i => acc + if FiniteSchedules.venue plan i = 0 then 3 else 1) 0

def readings (duration : Nat → Nat) (plan : FiniteSchedules.Schedule) : List (Option Int) :=
  [some (Int.ofNat (reduction plan)),
    some (Int.ofNat (Sched.span duration plan)),
    some (Int.ofNat (Sched.used plan))]

def space (jobs venues horizon : Nat) (duration : Nat → Nat) (deps : List (Nat × Nat)) :
    ThreeValuedGate.FiniteSpace
      (Fin (Sched.plans jobs venues horizon duration deps).length) contract :=
  let listed := Sched.plans jobs venues horizon duration deps
  { candidates := List.finRange listed.length
    readings := fun index => readings duration (listed.get index)
    nothingOutside := fun index => by simp [List.finRange, List.mem_ofFn]
    noCoverageGaps := fun _index _mem i hi => by
      have hi3 : i < 3 := by simpa [contract] using hi
      match i with
      | 0 => simp [readings, ThreeValuedGate.reading]
      | 1 => simp [readings, ThreeValuedGate.reading]
      | 2 => simp [readings, ThreeValuedGate.reading]
      | n + 3 => omega }

theorem shape (jobs venues horizon : Nat) (duration : Nat → Nat) (deps : List (Nat × Nat)) :
    ∀ index, ∃ ns : List Nat, ns.length = contract.axes.length ∧
      (space jobs venues horizon duration deps).readings index =
        ns.map fun n => some (Int.ofNat n) := by
  intro index
  let plan := (Sched.plans jobs venues horizon duration deps).get index
  refine ⟨[reduction plan, Sched.span duration plan, Sched.used plan], ?_, ?_⟩
  · simp [contract]
  · simp [space, readings, plan]

theorem corollary (jobs venues horizon : Nat) (duration : Nat → Nat) (deps : List (Nat × Nat)) :
    let sp := space jobs venues horizon duration deps
    _root_.Solve.run sp = FiniteFrontier.frontier sp.candidates
      (fun y z => ThreeValuedGate.dominatesB contract (sp.readings y) (sp.readings z)) :=
  (_root_.Solve.main (space jobs venues horizon duration deps)
    (shape jobs venues horizon duration deps)).1

end Bench

end Solve

#print axioms Solve.main
#print axioms Solve.Sched.frontier
#print axioms Solve.Bench.corollary
#print axioms Solve.checked
#print axioms Solve.named
