import Lake
open Lake DSL

package «software-is-composable» where
  moreLeanArgs := #["-DwarningAsError=true"]

@[default_target]
lean_lib SoftwareIsComposable
