/- Completeness: the carried artifact determines the source up to exactly
   the qualified quotient, in both directions. The information the
   forgetting compiler loses is exactly the derivation structure, and
   carrying exactly that is sufficient. -/
import Basic

namespace CompilersLoseInfo

variable {A : Type}

/-- Same carried artifact if and only if same qualified quotient. The
    forward direction is recovery (Preservation): the quotient is a
    function of the artifact. The reverse is the meeting of the two halves:
    the artifact carries nothing the quotient does not see, and misses
    nothing it does — two programs the machinery cannot tell apart have
    the same carried artifact, and two it can tell apart never do. -/
theorem carry_eq_iff_qual_eq (g₁ g₂ : Hypergraph A) :
    carry g₁ = carry g₂ ↔ qual g₁ = qual g₂ := by
  constructor
  · intro h
    have hb : (qual g₁).1 = (qual g₂).1 := congrArg Artifact.behavior h
    have ht : (qual g₁).2 = (qual g₂).2 := congrArg Artifact.topology h
    calc qual g₁ = ((qual g₁).1, (qual g₁).2) := rfl
      _ = ((qual g₂).1, (qual g₂).2) := by rw [hb, ht]
      _ = qual g₂ := rfl
  · intro h
    have hb : (carry g₁).behavior = (carry g₂).behavior := congrArg Prod.fst h
    have ht : (carry g₁).topology = (carry g₂).topology := congrArg Prod.snd h
    calc carry g₁ = ⟨(carry g₁).behavior, (carry g₁).topology⟩ := rfl
      _ = ⟨(carry g₂).behavior, (carry g₂).topology⟩ := by rw [hb, ht]
      _ = carry g₂ := rfl

/-- The same statement in the quotient's own terms: carrying identifies
    exactly the programs that agree. -/
theorem carry_eq_iff_agree (g₁ g₂ : Hypergraph A) :
    carry g₁ = carry g₂ ↔ Agree g₁ g₂ :=
  carry_eq_iff_qual_eq g₁ g₂

end CompilersLoseInfo
