import Lake
open Lake DSL

package «software-doesnt-need-review» where
  version := v!"0.1.0"
  leanOptions := #[⟨`warningAsError, true⟩]

@[default_target]
lean_lib SoftwareDoesntNeedReview where
