import Lean
import IncrementalCert

open Lean

elab "print_exported_axioms" : command => do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.map₁.toList ++ env.constants.map₂.toList do
    if let .thmInfo _ := ci then
      if (`IncrementalCert).isPrefixOf n then
        names := names.push n
  let sorted := names.qsort fun a b => a.toString < b.toString
  for n in sorted do
    let axs ← collectAxioms n
    if axs.isEmpty then
      IO.println s!"'{n}' does not depend on any axioms"
    else
      let parts := axs.toList.map toString
      IO.println s!"'{n}' depends on axioms: [{String.intercalate ", " parts}]"

print_exported_axioms
