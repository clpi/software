import Lake
open Lake DSL

package «software-is-incrementally-certifiable» where
  moreLeanArgs := #["-DwarningAsError=true"]

require «software-is-composable» from git
  "https://github.com/clpi/software-is-composable" @ "033c12c01299a9b28983bee410c230641adc7d1e"

require «software-is-quantifiable» from git
  "https://github.com/clpi/software-is-quantifiable" @ "430340295c52a015772022b2b663d01120a3a747"

lean_lib Audit where
  roots := #[`Audit.Refusals]

lean_lib Evidence where
  roots := #[`Audit.Counterexamples]

@[default_target]
lean_lib IncrementalCert where
  roots := #[`IncrementalCert]
