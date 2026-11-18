import Lake
open Lake DSL

package «software-is-composable» where
  moreLeanArgs := #["-DwarningAsError=true"]

require «software-is-quantifiable» from git
  "https://github.com/clpi/software-is-quantifiable" @ "d88acbdc3ba78fff994067d2c73bcc01622b3f61"

require «software-optimality» from git
  "https://github.com/clpi/software-optimality" @ "ec1eadda0a29d1b254a98feb5ad24911a095c454"

@[default_target]
lean_lib «SoftwareIsComposable»

lean_exe harness where
  root := `Main
