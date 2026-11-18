import Lake
open Lake DSL

package «software-doesnt-need-review» where
  version := v!"0.1.0"
  leanOptions := #[⟨`warningAsError, true⟩]

require «software-is-composable» from git
  "https://github.com/clpi/software-is-composable" @ "033c12c01299a9b28983bee410c230641adc7d1e"

@[default_target]
lean_lib SoftwareDoesntNeedReview where
