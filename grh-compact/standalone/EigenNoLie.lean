import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

open Module Submodule LinearMap

variable {k W : Type*} {ι : Sort*} [Field k] [IsAlgClosed k] [AddCommGroup W] [Module k W]
  (φ : ι → End k W) {S : Submodule k W} [Module.Finite k S]

/-- Common eigenvector in a joint generalised eigenspace of commuting endomorphisms, without Lie
algebras: a nonzero invariant subspace of least dimension inside it is killed by every `f m - χ m`. -/
lemma exists_eigenvector_of_le_iInf_maxGenEigenspace {V : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] {ι : Sort*} (f : ι → End k V) (h_comm : ∀ m n, Commute (f m) (f n))
    (χ : ι → k) (h_ne : (⨅ m, (f m).maxGenEigenspace (χ m)) ≠ ⊥) :
    ∃ x ∈ ⨅ m, (f m).maxGenEigenspace (χ m), x ≠ 0 ∧ ∀ m, f m x = χ m • x := by
  set E := ⨅ m, (f m).maxGenEigenspace (χ m)
  let P : Submodule k V → Prop := fun K ↦ K ≤ E ∧ K ≠ ⊥ ∧ ∀ m, ∀ y ∈ K, f m y ∈ K
  have hE_inv : ∀ m, ∀ y ∈ E, f m y ∈ E := fun m y hy ↦ by
    simp only [E, mem_iInf] at hy ⊢
    exact fun n ↦ Module.End.mapsTo_maxGenEigenspace_of_comm (h_comm n m) (χ n) (hy n)
  have hex : ∃ d, ∃ K, P K ∧ finrank k K = d := ⟨_, E, ⟨le_rfl, h_ne, hE_inv⟩, rfl⟩
  classical
  obtain ⟨K, ⟨hKE, hK_ne, hK_inv⟩, hK_dim⟩ := Nat.find_spec hex
  -- every `f m - χ m` vanishes on `K`
  have h_kill : ∀ m, ∀ y ∈ K, f m y = χ m • y := by
    intro m
    let g : End k V := f m - χ m • 1
    let K' : Submodule k V := K ⊓ LinearMap.ker g
    have hg_comm : ∀ n, Commute g (f n) := fun n ↦
      ((h_comm m n).sub_left (Commute.smul_left (Commute.one_left _) _))
    have hK'_inv : ∀ n, ∀ y ∈ K', f n y ∈ K' := fun n y hy ↦ by
      refine ⟨hK_inv n y hy.1, LinearMap.mem_ker.2 ?_⟩
      have h2 : g y = 0 := LinearMap.mem_ker.1 hy.2
      rw [← Module.End.mul_apply, (hg_comm n).eq, Module.End.mul_apply, h2, map_zero]
    have hK'_ne : K' ≠ ⊥ := by
      obtain ⟨y, hyK, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK_ne
      have hy_gen : ∃ j : ℕ, (g ^ j) y = 0 :=
        (Module.End.mem_maxGenEigenspace _ _ _).1 ((mem_iInf _).1 (hKE hyK) m)
      have hpow_mem : ∀ j : ℕ, (g ^ j) y ∈ K := by
        intro j
        induction j with
        | zero => simpa using hyK
        | succ j ih =>
          rw [pow_succ', Module.End.mul_apply]
          exact K.sub_mem (hK_inv m _ ih) (K.smul_mem _ (by simpa using ih))
      let j := Nat.find hy_gen
      have hj0 : j ≠ 0 := fun h ↦ by
        have := Nat.find_spec hy_gen
        rw [show Nat.find hy_gen = 0 from h, pow_zero, Module.End.one_apply] at this
        exact hy0 this
      obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hj0
      have hz0 : (g ^ i) y ≠ 0 := Nat.find_min hy_gen (by omega)
      refine fun h ↦ hz0 ?_
      have hz : (g ^ i) y ∈ K' := by
        refine ⟨hpow_mem i, LinearMap.mem_ker.2 ?_⟩
        rw [← Module.End.mul_apply, ← pow_succ']
        have := Nat.find_spec hy_gen
        rwa [show Nat.find hy_gen = i + 1 from hi] at this
      simpa [h] using hz
    have hle : K' ≤ K := inf_le_left
    have hdim : finrank k K ≤ finrank k K' := by
      rw [hK_dim]; exact Nat.find_min' hex ⟨K', ⟨hle.trans hKE, hK'_ne, hK'_inv⟩, rfl⟩
    have hEq : K' = K := Submodule.eq_of_le_of_finrank_le hle hdim
    intro y hy
    have : y ∈ LinearMap.ker g := (hEq ▸ hy : y ∈ K').2
    simpa [g, sub_eq_zero] using this
  obtain ⟨x, hxK, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK_ne
  exact ⟨x, hKE hxK, hx0, fun m ↦ h_kill m x hxK⟩

/-- Same statement as `New.exists_eigenvector_of_commute`, proved without Lie algebras. -/
lemma exists_eigenvector_of_commute' (hS : ∀ m : ι, ∀ x ∈ S, φ m x ∈ S)
    (h_comm : ∀ m n : ι, ∀ x ∈ S, φ m (φ n x) = φ n (φ m x)) {U : Submodule k S} (hU_ne : U ≠ ⊤) :
    ∃ χ : ι → k,
      ¬(⨅ m : ι, End.maxGenEigenspace (restrict (φ m) (hS m)) (χ m) ≤ U) ∧
      ∃ x ∈ S, x ≠ 0 ∧ ∀ m : ι, φ m x = χ m • x := by
  let f : PLift ι → End k S := fun m ↦ restrict (φ m.down) (hS m.down)
  have hf : ∀ m n, Commute (f m) (f n) := fun m n ↦
    LinearMap.ext fun x ↦ Subtype.ext (h_comm m.down n.down x x.2)
  have h_top := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    f (fun m n _ ↦ hf m n) fun m ↦ Module.End.iSup_maxGenEigenspace_eq_top _
  obtain ⟨χ, hχ⟩ : ∃ χ : PLift ι → k, ¬(⨅ m, (f m).maxGenEigenspace (χ m)) ≤ U := by
    by_contra! h
    exact hU_ne (eq_top_iff.2 (h_top ▸ iSup_le h))
  have hχ' : ¬(⨅ m : ι, End.maxGenEigenspace (restrict (φ m) (hS m)) (χ ⟨m⟩)) ≤ U := by
    intro h; apply hχ; rw [← iInf_plift_up]; exact h
  obtain ⟨x, -, hx0, hx⟩ := exists_eigenvector_of_le_iInf_maxGenEigenspace f hf χ
    (fun h ↦ hχ (h ▸ bot_le))
  exact ⟨fun m ↦ χ ⟨m⟩, hχ', x, x.2, by simpa using hx0,
    fun m ↦ congrArg Subtype.val (hx ⟨m⟩)⟩
