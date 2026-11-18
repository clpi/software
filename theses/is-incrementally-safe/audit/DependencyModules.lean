import SoftwareIsIncrementallySafe

open SoftwareIsComposable
open SoftwareIsIncrementallySafe

namespace AuditDependencyModules

theorem cone_sound {calls : List (Nat × Nat)} {seeds : List Nat} {s : Nat}
    (h : s ∈ coneExecOf calls seeds) : InClosure calls seeds s :=
  coneExec_sound h

theorem cone_complete {calls : List (Nat × Nat)} {seeds : List Nat} {s : Nat}
    (h : InClosure calls seeds s) : s ∈ coneExecOf calls seeds :=
  coneExec_complete h

theorem cone_affected {calls : List (Nat × Nat)} {seeds : List Nat} {s : Nat} :
    s ∈ coneExecOf calls seeds ↔
      HypergraphIncremental.Affected (hyper [] calls) (hyper seeds calls) s :=
  coneExec_iff_affected

theorem closureHyp_is_inClosure (calls : List (Nat × Nat)) (seeds inspected : List Nat) :
    ClosureHyp calls seeds inspected ↔ ∀ s, InClosure calls seeds s → s ∈ inspected :=
  Iff.rfl

theorem coneGood_is_affected {σ C ι ε : Type} (S : OrderedIncrement.Spec σ ι ε)
    (deps : σ → σ → Prop) (sem : (σ → C) → σ → OrderedIncrement.Beh ι ε)
    (I : σ → C) (changed : σ → Bool) (new : σ → C) :
    OrderedIncrement.ConeGood S deps sem I changed new ↔
      ∀ s, HypergraphIncremental.Affected (OrderedIncrement.depGraph deps fun _ => False)
          (OrderedIncrement.depGraph deps fun t => changed t = true) s →
        OrderedIncrement.Good S s (sem (OrderedIncrement.update I changed new) s) :=
  Iff.rfl

theorem same_profile_pareto :
    SoftwareIsQuantifiable.Pareto.profileOf (outputPoint leakBit) =
      SoftwareIsQuantifiable.Pareto.profileOf (outputPoint noiseBit) :=
  same_profile

theorem outputPoint_faithful (f g : Bool → Bool → Prop) :
    outputPoint f = outputPoint g ↔ (fun o => ∃ s, f s o) = (fun o => ∃ s, g s o) :=
  outputPoint_eq_iff f g

end AuditDependencyModules

#print axioms AuditDependencyModules.cone_sound
#print axioms AuditDependencyModules.cone_complete
#print axioms AuditDependencyModules.cone_affected
#print axioms AuditDependencyModules.closureHyp_is_inClosure
#print axioms AuditDependencyModules.coneGood_is_affected
#print axioms AuditDependencyModules.same_profile_pareto
#print axioms AuditDependencyModules.outputPoint_faithful
