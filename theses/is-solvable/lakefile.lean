import Lake
open Lake DSL

package «software-is-solvable» where
  version := v!"0.2.0"
  moreLeanArgs := #["-DwarningAsError=true"]

-- The closure core (Qualification, ExecutableClosure, HypergraphIncremental,
-- ClosureStrength) is imported from software-optimality at this pin, not copied.
require «software-optimality» from git
  "https://github.com/clpi/software-optimality" @ "979c872ad70a70422292a9694b1aacdf365587c1"

@[default_target]
lean_lib SoftwareIsSolvable where
  roots := #[`Hyperlattice, `WitnessExecutable, `WitnessTests, `Pareto]
