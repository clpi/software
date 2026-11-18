import Lake
open Lake DSL

package «software-is-composable» where
  moreLeanArgs := #["-DwarningAsError=true"]

require «software-is-quantifiable» from git
  "https://github.com/clpi/software-is-quantifiable" @ "430340295c52a015772022b2b663d01120a3a747"

require «software-optimality» from git
  "https://github.com/clpi/software-optimality" @ "97a5d7f3e68de47cd9eb26221b83e713121673fd"

@[default_target]
lean_lib «SoftwareIsComposable»

lean_exe harness where
  root := `Main
