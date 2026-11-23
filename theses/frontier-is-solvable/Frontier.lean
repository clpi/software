import Std
namespace FrontierSolvable
variable {A I : Type}

def NoWorse (cost : A → I → Int) (x y : A) : Prop := ∀ i, cost x i ≤ cost y i
def Dominates (cost : A → I → Int) (x y : A) : Prop :=
  NoWorse cost x y ∧ ∃ i, cost x i < cost y i

theorem dominates_irrefl (cost : A → I → Int) (x : A) : ¬ Dominates cost x x := by
  rintro ⟨_, i, h⟩
  exact (Int.lt_irrefl _ h)

theorem dominates_trans (cost : A → I → Int) {x y z : A}
    (h : Dominates cost x y) (k : Dominates cost y z) : Dominates cost x z := by
  refine ⟨fun i => Int.le_trans (h.1 i) (k.1 i), ?_⟩
  obtain ⟨i, hi⟩ := h.2
  exact ⟨i, Int.lt_of_lt_of_le hi (k.1 i)⟩

theorem ties_not_dominated (cost : A → I → Int) {x y : A}
    (h : ∀ i, cost x i = cost y i) : ¬ Dominates cost x y := by
  rintro ⟨_, i, hi⟩
  rw [h i] at hi
  exact Int.lt_irrefl _ hi

def Frontier (eligible : A → Prop) (d : A → A → Prop) (x : A) : Prop :=
  eligible x ∧ ∀ y, eligible y → ¬ d y x

def Insert (eligible : A → Prop) (z : A) (x : A) : Prop := eligible x ∨ x = z

def Retract (eligible removed : A → Prop) (x : A) : Prop := eligible x ∧ ¬ removed x

-- Exact update: filter the existing frontier, then include z iff no incumbent dominates it.
theorem insertion_exact (eligible : A → Prop) (d : A → A → Prop)
    (irr : ∀ x, ¬ d x x) (z x : A) :
    Frontier (Insert eligible z) d x ↔
      (Frontier eligible d x ∧ ¬ d z x) ∨
      (x = z ∧ ∀ y, eligible y → ¬ d y z) := by
  constructor
  · rintro ⟨hx, hn⟩
    rcases hx with he | hz
    · exact Or.inl ⟨⟨he, fun y hy => hn y (Or.inl hy)⟩, hn z (Or.inr rfl)⟩
    · subst x
      exact Or.inr ⟨rfl, fun y hy => hn y (Or.inl hy)⟩
  · rintro (⟨⟨he, hn⟩, hz⟩ | ⟨rfl, hn⟩)
    · refine ⟨Or.inl he, fun y hy => ?_⟩
      rcases hy with hy | rfl
      · exact hn y hy
      · exact hz
    · refine ⟨Or.inr rfl, fun y hy => ?_⟩
      rcases hy with hy | rfl
      · exact hn y hy
      · exact irr _

-- Removal exposes exactly candidates whose every former dominator was removed.
theorem retraction_exact (eligible removed : A → Prop) (d : A → A → Prop) (x : A) :
    Frontier (Retract eligible removed) d x ↔
      eligible x ∧ ¬ removed x ∧ ∀ y, eligible y → d y x → removed y := by
  classical
  constructor
  · rintro ⟨⟨he, hr⟩, hn⟩
    refine ⟨he, hr, fun y hy hd => ?_⟩
    apply Classical.byContradiction
    intro h
    exact hn y ⟨hy, h⟩ hd
  · rintro ⟨he, hr, hn⟩
    exact ⟨⟨he, hr⟩, fun y hy hd => hy.2 (hn y hy.1 hd)⟩

theorem surviving_frontier (eligible removed : A → Prop) (d : A → A → Prop)
    {x : A} (hf : Frontier eligible d x) (hr : ¬ removed x) :
    Frontier (Retract eligible removed) d x :=
  ⟨⟨hf.1, hr⟩, fun y hy => hf.2 y hy.1⟩

-- A still-live dominator prevents false resurrection.
theorem live_dominator_blocks (eligible removed : A → Prop) (d : A → A → Prop)
    {x y : A} (hy : eligible y) (hr : ¬ removed y) (hd : d y x) :
    ¬ Frontier (Retract eligible removed) d x := by
  intro hf
  exact hf.2 y ⟨hy, hr⟩ hd

-- Qualification and costs are views, not another authoritative graph.
theorem derived_view_extensional (e f : A → Prop) (d r : A → A → Prop)
    (he : ∀ x, e x ↔ f x) (hd : ∀ x y, d x y ↔ r x y) (x : A) :
    Frontier e d x ↔ Frontier f r x := by
  constructor
  · intro h
    exact ⟨(he x).mp h.1, fun y hy hr => h.2 y ((he y).mpr hy) ((hd y x).mpr hr)⟩
  · intro h
    exact ⟨(he x).mpr h.1, fun y hy hr => h.2 y ((he y).mp hy) ((hd y x).mp hr)⟩

def Guarded (eligible : A → Prop) (cost : A → I → Int) (baseline x : A) : Prop :=
  eligible x ∧ NoWorse cost x baseline

theorem guarded_no_regression (eligible : A → Prop) (cost : A → I → Int)
    (baseline x : A) (hf : Frontier (Guarded eligible cost baseline) (Dominates cost) x) :
    NoWorse cost x baseline := hf.1.2

theorem guarded_global_frontier (eligible : A → Prop) (cost : A → I → Int)
    (baseline x : A) (hf : Frontier (Guarded eligible cost baseline) (Dominates cost) x) :
    Frontier eligible (Dominates cost) x := by
  refine ⟨hf.1.1, fun y hy hd => ?_⟩
  exact hf.2 y ⟨hy, fun i => Int.le_trans (hd.1 i) (hf.1.2 i)⟩ hd

-- Executable finite evaluator; repetitions preserve membership, not multiplicity.
def compute (candidates : List A) (eligible : A → Bool) (d : A → A → Bool) : List A :=
  let live := candidates.filter eligible
  live.filter (fun x => !(live.any (fun y => d y x)))

theorem compute_exact (candidates : List A) (eligible : A → Bool)
    (d : A → A → Bool) (x : A) :
    x ∈ compute candidates eligible d ↔
      Frontier (fun x => x ∈ candidates ∧ eligible x = true) (fun y x => d y x = true) x := by
  simp [compute, Frontier, List.any_eq_true]
  constructor
  · rintro ⟨hx, hn, he⟩
    exact ⟨⟨hx, he⟩, hn⟩
  · rintro ⟨⟨hx, he⟩, hn⟩
    exact ⟨hx, hn, he⟩

def pareto (axes : List I) (cost : A → I → Int) (x y : A) : Bool :=
  axes.all (fun i => decide (cost x i ≤ cost y i)) &&
  axes.any (fun i => decide (cost x i < cost y i))

theorem pareto_exact (axes : List I) (cost : A → I → Int) (x y : A) :
    pareto axes cost x y = true ↔
      (∀ i, i ∈ axes → cost x i ≤ cost y i) ∧ ∃ i, i ∈ axes ∧ cost x i < cost y i := by
  simp [pareto, List.all_eq_true, List.any_eq_true]

-- A finite nonempty eligible list has a frontier member for every strict partial order.
theorem frontier_exists (d : A → A → Prop) (irr : ∀ x, ¬ d x x)
    (trans : ∀ {x y z}, d x y → d y z → d x z)
    (xs : List A) (nonempty : xs ≠ []) : ∃ x, Frontier (fun y => y ∈ xs) d x := by
  classical
  induction xs with
  | nil => exact False.elim (nonempty rfl)
  | cons a tail ih =>
    by_cases ht : tail = []
    · subst tail
      exact ⟨a, by simpa [Frontier] using irr a⟩
    · obtain ⟨b, hb, hn⟩ := ih ht
      by_cases hab : d a b
      · refine ⟨a, List.mem_cons_self, fun y hy hya => ?_⟩
        rcases List.mem_cons.mp hy with rfl | hy
        · exact irr _ hya
        · exact hn y hy (trans hya hab)
      · refine ⟨b, List.mem_cons_of_mem a hb, fun y hy hyb => ?_⟩
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hab hyb
        · exact hn y hy hyb

-- Qualification cannot make the baseline-guarded frontier empty while the baseline remains eligible.
theorem guarded_frontier_exists (xs : List A) (eligible : A → Prop)
    (cost : A → I → Int) (baseline : A) (hb : baseline ∈ xs) (he : eligible baseline) :
    ∃ x, Frontier (fun y => y ∈ xs ∧ Guarded eligible cost baseline y) (Dominates cost) x := by
  classical
  let live := xs.filter (fun y => decide (Guarded eligible cost baseline y))
  have hm : baseline ∈ live := by
    simp only [live, List.mem_filter, decide_eq_true_eq]
    exact ⟨hb, he, fun _ => Int.le_refl _⟩
  have hne : live ≠ [] := by
    intro h
    rw [h] at hm
    exact List.not_mem_nil hm
  obtain ⟨x, hx⟩ := frontier_exists (Dominates cost) (dominates_irrefl cost)
    (fun h k => dominates_trans cost h k) live hne
  refine ⟨x, ?_⟩
  simpa only [Frontier, live, List.mem_filter, decide_eq_true_eq] using hx

#print axioms dominates_irrefl
#print axioms dominates_trans
#print axioms ties_not_dominated
#print axioms surviving_frontier
#print axioms live_dominator_blocks
#print axioms derived_view_extensional
#print axioms guarded_no_regression
#print axioms pareto_exact
#print axioms guarded_frontier_exists

#print axioms insertion_exact
#print axioms retraction_exact
#print axioms guarded_global_frontier
#print axioms compute_exact
#print axioms frontier_exists
end FrontierSolvable
