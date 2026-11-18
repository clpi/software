import Lake
open Lake DSL

package «software-doesnt-have-to-regress» where
  leanOptions := #[⟨`warningAsError, true⟩]

require «software-is-composable» from "vendor/software-is-composable"

require «software-is-quantifiable» from git
  "https://github.com/clpi/software-is-quantifiable" @ "9f5ca06c0d5d92904f8509af676ab09ea5e0d79c"

@[default_target]
lean_lib SoftwareDoesntRegress

@[default_target]
lean_exe gate where
  root := `GateExe
