import Lake
open Lake DSL

package «software-core» where
  moreLeanArgs := #["-DwarningAsError=true"]

@[default_target]
lean_lib SoftwareCore
