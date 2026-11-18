import Lake
open Lake DSL

package «software-doesnt-have-to-regress» where
  leanOptions := #[⟨`warningAsError, true⟩]

require «software-is-composable» from git
  "https://github.com/clpi/software-is-composable" @ "033c12c01299a9b28983bee410c230641adc7d1e"

require «software-is-quantifiable» from git
  "https://github.com/clpi/software-is-quantifiable" @ "a21c7c56fa028f32014dd795b35b14f688e8fdf1"

@[default_target]
lean_lib SoftwareDoesntRegress

@[default_target]
lean_exe gate where
  root := `GateExe
