import Lake
open Lake DSL

package «software-frontier-is-solvable» where
  moreLeanArgs := #["-DwarningAsError=true"]

require «software-is-quantifiable» from "../is-quantifiable"

require «software-optimality» from "../optimality"

@[default_target]
lean_lib SoftwareFrontier where
  roots := #[
    `Red,
    `Hyper,
    `Fuzz,
    `Solve,
    `Instances,
    `Frontier,
    `Search,
    `Candidate,
    `Pipeline,
    `Worklist,
    `Canon,
    `Bridge,
    `Tests,
    `LinkHypergraph,
    `LinkPareto,
    `examples.ReplicaPlacement
  ]
