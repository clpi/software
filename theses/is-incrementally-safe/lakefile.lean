import Lake
open Lake DSL

package «software-is-incrementally-safe» where
  version := v!"0.1.0"

lean_lib SoftwareIsComposable where

lean_lib SoftwareIsIncrementallyCertifiable where

@[default_target]
lean_lib «SoftwareIsIncrementallySafe» where

@[default_target]
lean_lib Counterexamples where
  srcDir := "audit"
