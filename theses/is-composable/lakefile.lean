import Lake
open Lake DSL

package «software-is-composable» where
  moreLeanArgs := #["-DwarningAsError=true"]

require «software-is-quantifiable» from git
  "https://github.com/clpi/software-is-quantifiable" @ "f370992611d8c722e4897e67dbb8eaecf3d872ed"

require «software-optimality» from git
  "https://github.com/clpi/software-optimality" @ "16a6c690cf4ec4dedda34328e165da995d7592ae"

@[default_target]
lean_lib «SoftwareIsComposable»

lean_exe harness where
  root := `Main
