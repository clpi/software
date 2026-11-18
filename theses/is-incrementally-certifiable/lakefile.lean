import Lake
open Lake DSL

package «software-is-incrementally-certifiable» where
  moreLeanArgs := #["-DwarningAsError=true"]

require «software-is-composable» from git
  "https://github.com/clpi/software-is-composable" @ "033c12c0"

lean_lib Audit where
  roots := #[`Audit.Refusals]

@[default_target]
lean_lib IncrementalCert where
  roots := #[`IncrementalCert]
