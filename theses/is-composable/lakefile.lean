import Lake
open Lake DSL

package «software-is-composable» where
  moreLeanArgs := #["-DwarningAsError=true"]

require «software-is-quantifiable» from git
  "https://github.com/clpi/software-is-quantifiable" @ "430340295c52a015772022b2b663d01120a3a747"

require «software-optimality» from git
  "https://github.com/clpi/software-optimality" @ "b52c3170a6e108345bd5ada44ca7355dae55b395"

@[default_target]
lean_lib «SoftwareIsComposable»

lean_exe harness where
  root := `Main
