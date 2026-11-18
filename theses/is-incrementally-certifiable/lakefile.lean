import Lake
open Lake DSL

package «software-is-incrementally-certifiable» where
  moreLeanArgs := #["-DwarningAsError=true"]

require «software-is-composable» from git
  "https://github.com/clpi/software-is-composable" @ "033c12c01299a9b28983bee410c230641adc7d1e"

lean_lib Audit where
  roots := #[`Audit.Refusals]

@[default_target]
lean_lib IncrementalCert where
  roots := #[`IncrementalCert]
