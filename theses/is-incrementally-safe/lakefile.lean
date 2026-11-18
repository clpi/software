import Lake
open Lake DSL

package «software-is-incrementally-safe» where
  moreLeanArgs := #["-DwarningAsError=true"]

require «software-is-quantifiable» from git
  "https://github.com/clpi/software-is-quantifiable.git" @ "430340295c52a015772022b2b663d01120a3a747"

require «software-optimality» from git
  "https://github.com/clpi/software-optimality.git" @ "b52c3170a6e108345bd5ada44ca7355dae55b395"

require «software-is-composable» from git
  "https://github.com/clpi/software-is-composable.git" @ "033c12c01299a9b28983bee410c230641adc7d1e"

@[default_target]
lean_lib «SoftwareIsIncrementallySafe»

lean_lib Counterexamples where
  srcDir := "audit"
