import Lake
open Lake DSL

package «software-is-composable» where
  moreLeanArgs := #["-DwarningAsError=true"]

require «software-is-quantifiable» from git
  "https://github.com/clpi/software-is-quantifiable" @ "37917a4195efb1d0423a422ee954d767a9be1cd3"

lean_lib Qualification

lean_lib ExecutableClosure

lean_lib FiniteFrontier

lean_lib FiniteQualification

lean_lib HypergraphIncremental

@[default_target]
lean_lib «SoftwareIsComposable»

lean_exe harness where
  root := `Main
