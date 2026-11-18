import Lake
open Lake DSL

package «software-is-incrementally-certifiable» where
  moreLeanArgs := #["-DwarningAsError=true"]

@[default_target]
lean_lib Audit where
  roots := #[`Audit.Counterexamples]
