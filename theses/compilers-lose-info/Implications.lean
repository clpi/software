/- Implications that are proven corollaries of the thesis. The remaining
   implications — about Idol's implementation rather than the model — are
   stated as labeled proposals in IMPLICATIONS.md, not here. -/
import Basic
import Loss
import Preservation

namespace CompilersLoseInfo

variable {A : Type}

/-- Any compiler that factors through a lossy one inherits the loss: no
    recovery map exists for it either, whatever its artifact type. Post-hoc
    tooling built on a forgetting artifact is in this class by
    construction — its input is a function of the behavior alone. -/
theorem no_recovery_of_factor {S T U Q : Type} {f : S → U} {q : S → Q}
    {c : S → T} (hfac : ∃ g : U → T, ∀ s, c s = g (f s))
    (hnr : ¬ Recoverable f q) : ¬ Recoverable c q := by
  obtain ⟨g, hg⟩ := hfac
  rintro ⟨r, hr⟩
  apply hnr
  refine ⟨r ∘ g, fun s => ?_⟩
  show r (g (f s)) = q s
  rw [← hr s, hg s]

/-- The impossibility direction for foreign toolchains, stated exactly:
    any artifact computed from a foreign program's behavior alone — which
    is all a foreign artifact ever determines — admits no recovery of the
    qualified quotient. Provenance for foreign software cannot be recovered
    from the artifact; it can only be re-derived approximately, or sensed
    at the boundary while the execution happens. This is the formal reason
    the qualification design senses foreign executions at the kernel
    boundary instead of reading their artifacts. -/
theorem foreign_no_recovery {c : Hypergraph Node → Artifact Node}
    (hfac : ∃ g : (Node → Prop) → Artifact Node,
      ∀ s, c s = g (forget s)) :
    ¬ Recoverable c (qual (A := Node)) :=
  no_recovery_of_factor hfac forget_no_recovery

/-- Certification without reconstruction: the qualification of a program
    is a function of its carried artifact alone, so a certificate over the
    quotient is checked against the artifact, never re-derived from the
    source. (Restated from Preservation.carry_recoverable as the
    implication it carries.) -/
theorem certification_from_artifact :
    Recoverable (carry (A := A)) (qual (A := A)) :=
  carry_recoverable

/-- Test selection and incremental revalidation run over premise cones.
    The cone either runs over is read from the carried artifact exactly —
    this is the compiler-level corollary. The exactness of cone-scoped
    revalidation itself (revalidating the cone of a change yields the
    verdict of revalidating everything) is
    HypergraphIncremental.incremental_exact in clpi/software-optimality,
    cited there as its stronger home and not re-proven here. -/
theorem cone_from_artifact (g : Hypergraph A) (b : A) :
    coneOf (carry g) b = cone g b :=
  cone_exact g b

end CompilersLoseInfo
