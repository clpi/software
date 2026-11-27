import Lib.GaloisRep.Main.OddRank
section QuadraticDescent
open NumberField Ideal Subgroup Module.End New.QZChar
lemma New.GaloisRep.probe_weak_baseChange {E E' n : Type} [Field E] [CMType E] [Field E']
    [Algebra E E'] [CMTypeOver E E'] [Fintype n] [DecidableEq n] [HasPrimitiveRoot5040 E']
    {μ : (𝔸f E)ˣ →* ℂˣ} (hμ : IsStep (E := E) E' μ) {κ : Weight E}
    {f : Gf E n → WeylIndex n κ.1 → ℂ} (hf : f ∈ (stdSpace E n).forms κ) (hf_ne : f ≠ 0) :
    ∃ (F : (stdSpace E' n).forms κ.baseChange) (P' : FinPlace E' → Polynomial ℂ),
      IsEigenform F.val P' ∧ IsWeakBaseChange μ ∅ f F.val := by
  classical
  -- This is the transfer for trivial local data, whose only operator is the identity; its trace
  -- on a space containing `f ≠ 0` is not zero.
  let π : Representation ℂ Unit ((stdSpace E n).forms κ) :=
    localFormTranslation κ (1 : Unit →* Gf E n)
  have h_id : heckeFun π ⊤ 1 = 1 := by
    have : Unique (Unit ⧸ (⊤ : Subgroup Unit)) := by
      haveI := QuotientGroup.subsingleton_quotient_top (G := Unit)
      exact .mk' _
    simp [heckeFun, finsum_unique, π]
  have h_trace : HasNonzeroTraceAround π (heckeFun π ⊤ 1)
      (heckeGenEigenspace π ⊤ ((1 : Unit → Unit → ℂ) ∘ ![]) 0) ⟨f, hf⟩ := by
    intro W hW _
    refine trace_restrict_ne_zero one_ne_zero (fun h_bot ↦ hf_ne ?_) fun x _ ↦ ?_
    · exact congrArg Subtype.val (h_bot.le ⟨by simp [π], hW⟩)
    · exact eigenspace_le_maxGenEigenspace (by simp [h_id])
  obtain ⟨F, P', hF, h_bc, -⟩ := exists_isWeakBaseChange_of_matching (hμ := hμ) ⟨f, hf⟩
    isLocalMatching_empty (o := ![]) (θ := 0) (j₀ := ()) (hj₀ := rfl) (h_comm := by simp)
    (h_stable := nofun) (h_trace := h_trace)
  exact ⟨F, P', hF, h_bc⟩

end QuadraticDescent
open Lean Elab Command Meta in
partial def findParents (e : Expr) (target : Name) (acc : Array Name) : Array Name :=
  match e with
  | .app .. =>
    let args := e.getAppArgs
    let acc := if args.any (fun a => a.isAppOf target) then acc.push e.getAppFn.constName! else acc
    args.foldl (fun acc a => findParents a target acc) (findParents e.getAppFn target acc)
  | .lam _ t b _ => findParents b target (findParents t target acc)
  | .forallE _ t b _ => findParents b target (findParents t target acc)
  | .letE _ t v b _ => findParents b target (findParents v target (findParents t target acc))
  | .mdata _ b => findParents b target acc
  | .proj _ _ b => findParents b target acc
  | _ => acc

open Lean Elab Command Meta in
elab "#zgpar " id:ident : command => do
  let env ← getEnv
  let some ci := env.find? id.getId | throwError "no"
  let .thmInfo t := ci | throwError "not thm"
  logInfo m!"{findParents t.value ``IsZGroup.instIsCyclicOfFiniteOfIsNilpotent #[]} | {findParents t.value ``IsCyclic.isMulCommutative #[]} | {findParents t.value ``IsZGroup.instQuotientSubgroupOfFinite #[]}"
#zgpar New.GaloisRep.probe_weak_baseChange
