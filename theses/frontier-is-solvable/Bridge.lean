import Canon
import Worklist

/-!
The bridge to the canonical view: census lemma L-close of the
reversible home, proved.

Provenance. The canonical definitions live in the expands home
(clpi/software-redundant-compute-expands) at pin 4da720a7. Its
canonical file is carried in this repo as the module Canon, byte
for byte (sha256
e64a154a8c81d379a7bced18ce718242e6c613eff621f6de7e374e129266c366,
checked against the expands clone at that pin), so the view in
every statement below is the canonical view itself, not a
restatement of it. The edge list of a fixed view (the records
definition below) is the expands home's own edge-list form,
copied exactly, and its exactness against the view is re-proved
in place. The worklist side is this repo's Worklist module at
eb29b7de, used through its proved results only: its closure
theorem, its append theorem, its termination theorem, and its
bridge from its own derivation predicate to the generic
roots-and-edges closure.

Route. Bridge form, on exactly the fragment where the two
constructions agree: a fixed chain, log, level and color test;
terms read after projection, as the canonical layer defines
them; empty roots on the canonical side and empty seed on the
worklist side; edges and premises read by membership on both
sides, so duplicate premises and duplicate records are inert on
both sides. On that fragment the two least closures are the same
predicate (the same theorem), the fixed-view equality is the
worklist closure theorem composed with that bridge, and the
append form is the worklist append theorem composed the same
way, with the carried set any list whose membership is exactly
the canonical closure of the old view. The append form is the
append-prefix statement: a growing log is a chain of single
appends, and the theorem is stated for an arbitrary old log and
an arbitrary appended part, so it covers every prefix.

Named differences, carried from the worklist record of
2026-11-20 and checked again here. The candidate layer's
qualification filter is not the canonical color test; this
bridge runs through the edge list of the view, where the color
test has already been applied, and claims nothing about the
qualification filter. Rule identity is positional in the
worklist module and shared in the expands home's written
reference; the bridge is insensitive to it, because both
derivation predicates read edge membership only. The expands
home's scanning closure is a second algorithm, whose equality
with the view is proved in that home; its closure list
satisfies the carried-set hypothesis of the append theorem
here by that home's exactness theorem, so the append form
covers resuming from either algorithm's carried set. The
instantiation proved below uses the worklist's own drained
derived list as the carried set.
-/

namespace Bridge

/-- The admitted records of a fixed canonical view as an edge
    list: filter the log by level and color test, then project.
    The exact definition the expands home proves exact against
    the canonical view in its closure worklist module. -/
def records (ch : Canon.Chain) (log : List Canon.Rec) (r : Nat)
    (color : List Nat → Bool) : List (List Nat × Nat) :=
  (log.filter (fun e => decide (e.level ≤ r) && color e.colors)).map
    (Canon.proj ch r)

/-- The edge list of a view is exactly the view's edge
    predicate. -/
theorem listed (ch : Canon.Chain) (log : List Canon.Rec) (r : Nat)
    (color : List Nat → Bool) (ps : List Nat) (a : Nat) :
    (ps, a) ∈ records ch log r color ↔
      (Canon.viewC ch log r color).edges ps a := by
  simp [records, Canon.viewC, and_assoc]

/-- Transfer from the generic closure of the worklist module to
    the canonical closure, along a root map and an edge map. -/
theorem forth {B C : Nat → Prop} {R S : List Nat → Nat → Prop}
    (hb : ∀ a, B a → C a) (hr : ∀ ps a, R ps a → S ps a) {x : Nat}
    (h : Worklist.GDerives B R x) : Canon.Derives C S x := by
  induction h with
  | root hb' => exact Canon.Derives.root (hb _ hb')
  | step he _ ih => exact Canon.Derives.step (hr _ _ he) ih

/-- Transfer from the canonical closure to the generic closure
    of the worklist module, along a root map and an edge map. -/
theorem back {B C : Nat → Prop} {R S : List Nat → Nat → Prop}
    (hb : ∀ a, B a → C a) (hr : ∀ ps a, R ps a → S ps a) {x : Nat}
    (h : Canon.Derives B R x) : Worklist.GDerives C S x := by
  induction h with
  | root hb' => exact Worklist.GDerives.root (hb _ hb')
  | step he _ ih => exact Worklist.GDerives.step (hr _ _ he) ih

/-- The bridge at the predicate level: the worklist module's
    least full closure of the view's edge list is the canonical
    derivation in the view. -/
theorem same (ch : Canon.Chain) (log : List Canon.Rec) (r : Nat)
    (color : List Nat → Bool) {x : Nat} :
    Worklist.Deriv ((records ch log r color).map Worklist.ruleOfEdge) x ↔
      Canon.derives (Canon.viewC ch log r color) x := by
  constructor
  · intro h
    have h1 : Worklist.GDerives (fun _ => False)
        (Worklist.edgeOf ((records ch log r color).map Worklist.ruleOfEdge))
        x :=
      Worklist.deriv_iff_gderives.mp h
    have h2 : Canon.Derives (fun _ => False)
        (fun ps a => (ps, a) ∈ records ch log r color) x :=
      forth (fun a ha => ha)
        (fun ps a he => Worklist.edgeOf_map.mp he) h1
    exact Canon.Derives.mono
      (B := (fun _ => False)) (C := (Canon.viewC ch log r color).roots)
      (R := (fun ps a => (ps, a) ∈ records ch log r color))
      (S := (Canon.viewC ch log r color).edges)
      (fun a ha => ha)
      (fun ps a he => (listed ch log r color ps a).mp he) x h2
  · intro h
    have h2 : Canon.Derives (fun _ => False)
        (fun ps a => (ps, a) ∈ records ch log r color) x :=
      Canon.Derives.mono
        (B := (Canon.viewC ch log r color).roots) (C := (fun _ => False))
        (R := (Canon.viewC ch log r color).edges)
        (S := (fun ps a => (ps, a) ∈ records ch log r color))
        (fun a ha => ha)
        (fun ps a he => (listed ch log r color ps a).mpr he) x h
    have h1 : Worklist.GDerives (fun _ => False)
        (Worklist.edgeOf ((records ch log r color).map Worklist.ruleOfEdge))
        x :=
      back (fun a ha => ha)
        (fun ps a he => Worklist.edgeOf_map.mpr he) h2
    exact Worklist.deriv_iff_gderives.mpr h1

/-- A derived term of an unseeded closure is the head of one of
    its rules, so a bound on heads bounds the whole closure. -/
theorem bounded {rs : List Worklist.Rule} {bound : List Nat}
    (hrb : ∀ r ∈ rs, r.head ∈ bound) {y : Nat}
    (hy : Worklist.Deriv rs y) : y ∈ bound :=
  Worklist.derivFrom_least (fun _x hx => (List.not_mem_nil hx).elim)
    (fun r hr _ => hrb r hr) hy

/-- Fixed view: the drained worklist over the view's edge list
    computes exactly the canonical derivation in the view. The
    bound and fuel hypotheses are the worklist module's own
    termination form: a finite term bound holding every head,
    and fuel at least the bound's size. -/
theorem fixed (ch : Canon.Chain) (log : List Canon.Rec) (r : Nat)
    (color : List Nat → Bool) {bound : List Nat} (hb : bound.Nodup)
    (hrb : ∀ e ∈ records ch log r color, e.2 ∈ bound)
    {fuel : Nat} (hfuel : bound.length ≤ fuel) {x : Nat} :
    x ∈ (Worklist.go fuel ((records ch log r color).map Worklist.ruleOfEdge)
      (Worklist.seedSt ((records ch log r color).map Worklist.ruleOfEdge)
        [])).derived ↔
      Canon.derives (Canon.viewC ch log r color) x := by
  have hr : ∀ r' ∈ (records ch log r color).map Worklist.ruleOfEdge,
      r'.head ∈ bound := by
    intro r' hr'
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hr'
    exact hrb e he
  exact (Worklist.worklist_closure hb hr hfuel).trans (same ch log r color)

/-- The edge list of a joined log is the join of the edge lists,
    at the same fixed view. -/
theorem joins (ch : Canon.Chain) (log extra : List Canon.Rec) (r : Nat)
    (color : List Nat → Bool) :
    records ch (log ++ extra) r color =
      records ch log r color ++ records ch extra r color := by
  simp only [records, List.filter_append, List.map_append]

/-- Append form, L-close: resuming the worklist over the grown
    log from any carried list whose membership is exactly the
    canonical closure of the old view computes exactly the
    canonical derivation in the grown view. Rules incomplete
    before the append keep their remaining counts by the
    worklist module's append theorem underneath. -/
theorem grown (ch : Canon.Chain) (log extra : List Canon.Rec) (r : Nat)
    (color : List Nat → Bool) {bound : List Nat} (hb : bound.Nodup)
    {D : List Nat} (hDnd : D.Nodup) (hDb : ∀ y ∈ D, y ∈ bound)
    (hD : ∀ y, y ∈ D ↔ Canon.derives (Canon.viewC ch log r color) y)
    (hrb : ∀ e ∈ records ch (log ++ extra) r color, e.2 ∈ bound)
    {fuel : Nat} (hfuel : bound.length - D.length ≤ fuel) {x : Nat} :
    x ∈ (Worklist.go fuel
      ((records ch (log ++ extra) r color).map Worklist.ruleOfEdge)
      (Worklist.admitSt
        ((records ch (log ++ extra) r color).map Worklist.ruleOfEdge)
        D)).derived ↔
      Canon.derives (Canon.viewC ch (log ++ extra) r color) x := by
  have hrec : (records ch (log ++ extra) r color).map Worklist.ruleOfEdge
      = (records ch log r color).map Worklist.ruleOfEdge
        ++ (records ch extra r color).map Worklist.ruleOfEdge := by
    rw [joins, List.map_append]
  have hr : ∀ r' ∈ (records ch log r color).map Worklist.ruleOfEdge
      ++ (records ch extra r color).map Worklist.ruleOfEdge,
      r'.head ∈ bound := by
    intro r' hr'
    rcases List.mem_append.mp hr' with h | h
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
      exact hrb e (by rw [joins]; exact List.mem_append.mpr (Or.inl he))
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
      exact hrb e (by rw [joins]; exact List.mem_append.mpr (Or.inr he))
  have hD' : ∀ y, y ∈ D ↔
      Worklist.Deriv ((records ch log r color).map Worklist.ruleOfEdge) y :=
    fun y => (hD y).trans (same ch log r color).symm
  have key : x ∈ (Worklist.go fuel
      ((records ch log r color).map Worklist.ruleOfEdge
        ++ (records ch extra r color).map Worklist.ruleOfEdge)
      (Worklist.admitSt
        ((records ch log r color).map Worklist.ruleOfEdge
          ++ (records ch extra r color).map Worklist.ruleOfEdge)
        D)).derived ↔
      Worklist.Deriv
        ((records ch log r color).map Worklist.ruleOfEdge
          ++ (records ch extra r color).map Worklist.ruleOfEdge) x :=
    Worklist.append_eq hb hDnd hDb hr hD' hfuel
  have hsame : Worklist.Deriv
      ((records ch log r color).map Worklist.ruleOfEdge
        ++ (records ch extra r color).map Worklist.ruleOfEdge) x ↔
      Canon.derives (Canon.viewC ch (log ++ extra) r color) x := by
    rw [← List.map_append, ← joins]
    exact same ch (log ++ extra) r color
  rw [hrec]
  exact key.trans hsame

/-- The append form with the carried set instantiated: the
    drained derived list of the worklist over the old view,
    run at the bound's own fuel. -/
theorem carried (ch : Canon.Chain) (log extra : List Canon.Rec) (r : Nat)
    (color : List Nat → Bool) {bound : List Nat} (hb : bound.Nodup)
    (hrb₁ : ∀ e ∈ records ch log r color, e.2 ∈ bound)
    (hrb : ∀ e ∈ records ch (log ++ extra) r color, e.2 ∈ bound)
    {x : Nat} :
    x ∈ (Worklist.go bound.length
      ((records ch (log ++ extra) r color).map Worklist.ruleOfEdge)
      (Worklist.admitSt
        ((records ch (log ++ extra) r color).map Worklist.ruleOfEdge)
        (Worklist.go bound.length
          ((records ch log r color).map Worklist.ruleOfEdge)
          (Worklist.seedSt ((records ch log r color).map Worklist.ruleOfEdge)
            [])).derived)).derived ↔
      Canon.derives (Canon.viewC ch (log ++ extra) r color) x := by
  have hr₁ : ∀ r' ∈ (records ch log r color).map Worklist.ruleOfEdge,
      r'.head ∈ bound := by
    intro r' hr'
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hr'
    exact hrb₁ e he
  have hterm := Worklist.terminates (S := []) hb List.nodup_nil
    (fun y hy => (List.not_mem_nil hy).elim) hr₁
  have hDb : ∀ y ∈ (Worklist.go bound.length
      ((records ch log r color).map Worklist.ruleOfEdge)
      (Worklist.seedSt ((records ch log r color).map Worklist.ruleOfEdge)
        [])).derived, y ∈ bound :=
    fun y hy => bounded hr₁
      ((Worklist.worklist_closure hb hr₁ (Nat.le_refl _)).mp hy)
  have hD : ∀ y, y ∈ (Worklist.go bound.length
      ((records ch log r color).map Worklist.ruleOfEdge)
      (Worklist.seedSt ((records ch log r color).map Worklist.ruleOfEdge)
        [])).derived ↔
      Canon.derives (Canon.viewC ch log r color) y :=
    fun y => (Worklist.worklist_closure (x := y) hb hr₁
      (Nat.le_refl _)).trans (same ch log r color)
  exact grown ch log extra r color hb hterm.2.1 hDb hD hrb (Nat.sub_le _ _)

/-- The identity chain of the control: every level is its own
    class, so projection is the identity. -/
def chain : Canon.Chain := ⟨fun _ c => c, 0, 0, Nat.le_refl 0⟩

/-- The control log: a zero-premise record with head 5 and a
    record with premise 5 and head 7, both at level 0. -/
def log : List Canon.Rec := [⟨0, 0, [], [], 5⟩, ⟨1, 0, [], [5], 7⟩]

/-- Control: the bridge is not vacuous. Through the fixed-view
    equality, the canonical view of the control log derives 7
    and does not derive 9, and the worklist computes exactly
    the two expected terms. -/
theorem control :
    (Worklist.go 10 ((records chain log 0 (fun _ => true)).map
        Worklist.ruleOfEdge)
      (Worklist.seedSt ((records chain log 0 (fun _ => true)).map
        Worklist.ruleOfEdge) [])).derived = [5, 7] ∧
    Canon.derives (Canon.viewC chain log 0 (fun _ => true)) 7 ∧
    ¬ Canon.derives (Canon.viewC chain log 0 (fun _ => true)) 9 := by
  have hcomp : (Worklist.go 10 ((records chain log 0 (fun _ => true)).map
      Worklist.ruleOfEdge)
    (Worklist.seedSt ((records chain log 0 (fun _ => true)).map
      Worklist.ruleOfEdge) [])).derived = [5, 7] := by decide
  have hfix : ∀ x, x ∈ (Worklist.go 10
      ((records chain log 0 (fun _ => true)).map Worklist.ruleOfEdge)
      (Worklist.seedSt ((records chain log 0 (fun _ => true)).map
        Worklist.ruleOfEdge) [])).derived ↔
      Canon.derives (Canon.viewC chain log 0 (fun _ => true)) x :=
    fun x => fixed chain log 0 (fun _ => true) (bound := [5, 7])
      (by decide) (by decide) (fuel := 10) (by decide) (x := x)
  refine ⟨hcomp, (hfix 7).mp (by rw [hcomp]; decide), fun h9 => ?_⟩
  have h9' := (hfix 9).mpr h9
  rw [hcomp] at h9'
  exact absurd h9' (by decide)

#print axioms listed
#print axioms forth
#print axioms back
#print axioms same
#print axioms bounded
#print axioms fixed
#print axioms joins
#print axioms grown
#print axioms carried
#print axioms control

end Bridge
