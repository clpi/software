import Family.Necessary
import FrontierComposition

/-!
# P-00 with unknowns: the frontier can be solved in parallel even when readings are missing

Upstream `FrontierComposition.partition_exact` (software-optimality) proves that the frontier
of a union equals the frontier of the union of the parts' frontiers, for any transitive,
irreflexive dominance. That is the formal content of "solve the Pareto frontier in parallel".
It needs the comparison to be transitive and irreflexive. This module shows the unknown-blocking
rule of S-04 and C-03 is both (`pdom_trans`, `pdom_irrefl`), so the parallel solve stays exact
when some readings are unknown (`parallel_exact_unknown`).

Prior art: divide-and-conquer skyline computation (Kung, Luccio and Preparata 1975; Borzsonyi,
Kossmann and Stocker 2001). Not new; the link to the three-valued rule is the contribution.
-/
namespace Family.ParallelUnknown

open Classical Family.Necessary

theorem pdom_irrefl {α : Type} (axes : List α) (x : PVec α Int) : ¬ PDom axes x x := by
  rintro ⟨_, a, _, u, v, hu, hv, huv⟩
  rw [hu] at hv
  cases hv
  omega

theorem pdom_trans {α : Type} (axes : List α) (x y z : PVec α Int)
    (hxy : PDom axes x y) (hyz : PDom axes y z) : PDom axes x z := by
  refine ⟨fun a ha => ?_, ?_⟩
  · obtain ⟨u, v, hu, hv, huv⟩ := hxy.1 a ha
    obtain ⟨v', w, hv', hw, hvw⟩ := hyz.1 a ha
    rw [hv] at hv'; cases hv'
    exact ⟨u, w, hu, hw, by omega⟩
  · obtain ⟨a, ha, u, v, hu, hv, huv⟩ := hxy.2
    obtain ⟨v', w, hv', hw, hvw⟩ := hyz.1 a ha
    rw [hv] at hv'; cases hv'
    exact ⟨a, ha, u, w, hu, hw, by omega⟩

/-- The rule as a Boolean comparator on candidates. -/
noncomputable def pdomB {α ι : Type} (axes : List α) (read : ι → PVec α Int) (x y : ι) : Bool :=
  decide (PDom axes (read x) (read y))

theorem parallel_exact_unknown {α ι : Type} (axes : List α) (read : ι → PVec α Int)
    (left right : List ι) (x : ι) :
    x ∈ FiniteFrontier.frontier (left ++ right) (pdomB axes read) ↔
      x ∈ FiniteFrontier.frontier
        (FiniteFrontier.frontier left (pdomB axes read) ++
          FiniteFrontier.frontier right (pdomB axes read)) (pdomB axes read) :=
  FrontierComposition.partition_exact (pdomB axes read)
    (fun {a b c} hab hbc => by
      simp only [pdomB, decide_eq_true_eq] at hab hbc ⊢
      exact pdom_trans axes _ _ _ hab hbc)
    (fun a => by simp [pdomB, pdom_irrefl]) left right x

end Family.ParallelUnknown
