import Lake
open Lake DSL

package «software-is-incrementally-safe» where
  moreLeanArgs := #["-DwarningAsError=true"]

require «software-is-quantifiable» from "../is-quantifiable"

require «software-optimality» from "../optimality"

require «software-is-composable» from "../is-composable"

@[default_target]
lean_lib «SoftwareIsIncrementallySafe»

@[default_target]
lean_lib «AuditDependencyModules» where
  srcDir := "audit"
  roots := #[`DependencyModules, `RenameReorderAxioms, `FamilyAxioms, `OrderedIncrementAxioms,
    `SubmittedTraceSys]

@[default_target]
lean_lib «NatReprExample» where
  srcDir := "examples"
  roots := #[`NatReprInjective]

@[default_target]
lean_lib «Family»
