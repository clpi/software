# Finite mediation coverage

This is a query projection for the witness hypergraph, not a second
program semantics or a sensor inventory. Its input is a finite indexed
snapshot: vertices name effects or observations, directed arcs name
authorized evidence flow (if the endpoint is observed, the source effect
is observed), and readiness is the conjunction of deployed, healthy and
faithful. A computational dependency alone is not an observation arc.

`Observed x` means a directed path from x to a sensor whose three
readiness flags are set, including a zero-edge path at a ready sensor.
`Closure` fires a rule only after **all** listed premises are derived.
For each applicable rule, the local certificate names either a ready
sensor at the head, or a mediation arc from that head to one of the full
premise list. A nullary rule has no premise and needs the direct case.
Seed-placement records supply actual seed-to-sensor paths. Induction over
the derivation then proves `closure_observed`. It takes no completeness
premise of the form “every derived effect is observed.”

The boundary is deliberate. Seed paths, rule projections, actual wiring
and its interpretation, sensor placement, health and fidelity are
independently checkable or external premises. `external_lift` composes
local wiring and sensor facts; it cannot certify physical truth from
flags. `target_coverage` separately assumes that intended targets are
represented in the supplied closure. Neither lemma asserts that an
arbitrary deployment or its effect inventory is complete.

`observed_append` preserves an observation under additive valid arcs
and sensor entries in a fixed snapshot. A later sensor failure or a
withdrawal is not such an append to the active view. Keep the old evidence
historically without pretending the old sensor remains healthy now.

## Traversal and controls

`reverse_exact` checks the relational specification of the traversal:
mark all ready nodes, then move backward along incoming arcs. The Python
control supplies an executable indexed queue, not a verified extraction
of the Lean relation. Mark on enqueue so every vertex is dequeued at most
once and each incoming arc is scanned at most once. On indexed adjacency
and one ready bit per vertex, construction of reverse adjacency and
multi-source traversal take O(V+E) time and space. If readiness is
supplied as an unprojected sensor list, folding it adds O(S). Looking up
an explicit query list adds O(Q); independent full traversals can cost
O(Q(V+E)). No closure, physical validation, or runtime measurement is
included in this bound.

`python3 proof/mediation-replay.py` compared the reverse result with an
independent forward fixed-point oracle on all 4,096 directed three-node
edge/ready combinations (12,288 individual target comparisons) and all
eight readiness flag combinations. These are correctness controls, not a
benchmark. The Lean controls cover two-step composition, missing wiring,
false health, deployment and faithfulness flags, nullary rules, and a
target not represented by the closure.
