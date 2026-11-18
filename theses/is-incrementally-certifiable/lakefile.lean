import Lake
open Lake DSL

package «software-is-incrementally-certifiable» where
  moreLeanArgs := #["-DwarningAsError=true"]

require «software-is-composable» from git
  "https://github.com/clpi/software-is-composable" @ "476059c25b93679919238ae4293c6b0b4befe486"

require «software-optimality» from git
  "https://github.com/clpi/software-optimality" @ "b52c3170a6e108345bd5ada44ca7355dae55b395"

lean_lib Audit where
  roots := #[`Audit.Refusals]

lean_lib Evidence where
  roots := #[`Audit.Counterexamples]

@[default_target]
lean_lib IncrementalCert where
  roots := #[`IncrementalCert]
