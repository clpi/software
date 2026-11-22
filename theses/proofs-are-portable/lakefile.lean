import Lake
open Lake DSL

package «software-proofs-are-portable» where
  moreLeanArgs := #["-DwarningAsError=true"]

@[default_target]
lean_lib Twin where
  roots := #[`Twin, `Axioms]
