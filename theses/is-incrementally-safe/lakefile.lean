import Lake
open Lake DSL

package «software-is-incrementally-safe» where
  moreLeanArgs := #["-DwarningAsError=true"]

require «software-is-quantifiable» from git
  "https://github.com/clpi/software-is-quantifiable.git" @ "f370992611d8c722e4897e67dbb8eaecf3d872ed"

require «software-optimality» from git
  "https://github.com/clpi/software-optimality.git" @ "16a6c690cf4ec4dedda34328e165da995d7592ae"

require «software-is-composable» from git
  "https://github.com/clpi/software-is-composable.git" @ "dce6564be7366ae3389e710b53a4623f497290b7"

@[default_target]
lean_lib «SoftwareIsIncrementallySafe»

@[default_target]
lean_lib «AuditDependencyModules» where
  srcDir := "audit"
  roots := #[`DependencyModules]
