import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.LinearAlgebra.Matrix.ToLin

open Projectivization Matrix
open scoped LinearAlgebra.Projectivization

/-- `GL n F` acts transitively on the projective space of `F^n`: send one representative to the
other by a linear automorphism extended from the two lines, then take its matrix. No primitivity
or multiple transitivity. -/
lemma New.isPretransitive_GL_projectivization {n F : Type*} [Fintype n] [DecidableEq n] [Field F] :
    MulAction.IsPretransitive (GL n F) (ℙ F (n → F)) := by
  refine ⟨fun D E ↦ ?_⟩
  let f : (F ∙ D.rep) ≃ₗ[F] (F ∙ E.rep) :=
    (LinearEquiv.toSpanNonzeroSingleton F _ D.rep D.rep_nonzero).symm ≪≫ₗ
      LinearEquiv.toSpanNonzeroSingleton F _ E.rep E.rep_nonzero
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  have hgD : g D.rep = E.rep := by
    have := hg ⟨D.rep, Submodule.mem_span_singleton_self _⟩
    have h1 : (LinearEquiv.toSpanNonzeroSingleton F _ D.rep D.rep_nonzero).symm
        ⟨D.rep, Submodule.mem_span_singleton_self _⟩ = 1 := by
      rw [LinearEquiv.symm_apply_eq, LinearEquiv.toSpanNonzeroSingleton_one]
    rw [← this]
    simp [f, h1]
  let M : GL n F :=
    ⟨LinearMap.toMatrix' g.toLinearMap, LinearMap.toMatrix' g.symm.toLinearMap,
      by rw [← LinearMap.toMatrix'_mul, ← LinearMap.toMatrix'_id]; congr 1; ext x; simp,
      by rw [← LinearMap.toMatrix'_mul, ← LinearMap.toMatrix'_id]; congr 1; ext x; simp⟩
  refine ⟨M, ?_⟩
  rw [← mk_rep D, ← mk_rep E, smul_mk, mk_eq_mk_iff]
  refine ⟨1, ?_⟩
  rw [one_smul, Units.smul_def]
  change E.rep = Matrix.mulVec (LinearMap.toMatrix' g.toLinearMap) D.rep
  rw [LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe, hgD]
