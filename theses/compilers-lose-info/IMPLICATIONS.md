# Implications

Each implication is stated at exactly its evidence level. A proven
corollary is a theorem of this repository (or of its cited stronger home)
about the model. A proposal is a claim about Idol's implementation, stated
with the condition that would close it; nothing here asserts an
implementation fact this repository did not check.

## Proven corollaries

**Incremental revalidation, at the compiler level.** Revalidation after a
change runs over the premise cone of the change. The cone is read from the
carried artifact exactly — `cone_from_artifact` (Implications.lean), from
`cone_exact` (Preservation.lean). The exactness of cone-scoped revalidation
itself — revalidating the cone yields the verdict of revalidating
everything — is `incremental_exact` in clpi/software-optimality
(HypergraphIncremental, pin 78b7b99b26ca241ac7a8964f2a4848489978c727), its
stronger home, cited and not re-proven. What the thesis adds is that the
compiler does not stand between the revalidation and its cone: with a
forgetting compiler the cone is precisely what was lost, and by
`foreign_no_recovery` no function of the artifact restores it, so a
conventional incremental builder's cone is always a re-derivation from
source, never a read from the artifact.

**Certification without reconstruction.** The qualified quotient of a
program is a function of its carried artifact (`certification_from_artifact`,
from `carry_recoverable`). A certificate over the quotient — the
qualification colorings, the fold over witnesses, a release certificate
between two pins — is therefore checked against the artifact alone. Under a
forgetting compiler the same certificate must be recomputed from source on
every check, because the artifact does not determine the quotient.

**Test selection as premise cones.** Selecting the tests a change can
affect is computing premise cones. Same corollary, same citation split as
incremental revalidation: the cone is exact from the carried artifact here;
from a conventional artifact the selection is a re-derivation, and its
exactness is bounded by the re-derivation's fidelity, not by the artifact.

**The impossibility direction for foreign toolchains.** Any artifact
computed from a program's behavior alone admits no recovery of the
qualified quotient (`foreign_no_recovery`, from the general
`no_recovery_of_factor` and the concrete `forget_no_recovery`). This is
the formal reason the qualification design treats foreign executions the
way it does: provenance for foreign software is not recovered from its
artifacts — it is sensed at the kernel boundary while the execution
happens (the boundary-sensing design of the decidability spec, §18), or
re-derived approximately afterward at cost. It also bounds what any
post-hoc tooling on conventional artifacts can ever certify: tools in the
factoring class inherit the loss, whatever their artifact format.

## Proposals, with closing conditions

**Witnesses are definitional, not recovered.** In the qualification
design, a witness is a derivation record — a component of the one graph,
emitted by the derivation itself. The model-level content is proven here:
what a witness attests (the quotient data) is carried, not reconstructed.
As a claim about Idol's build, it closes when a named Idol build's emitted
artifact is shown at a pin to carry the derivation records its
qualification surfaces read, with those surfaces reading them from the
artifact rather than re-running derivations.

**Debug and profile information are projections, not side channels.** A
debugger's provenance view and a profiler's attribution are functions of
the carried topology and behavior — projections of the one graph. This is
a design statement about Idol's tooling, not a theorem. It closes when
Idol's debug and profile outputs are produced as projections of the
carried graph in the implementation, with a check at a pin comparing them
against independently computed projections.

**The foundation claim, at its real strength.** Over hypergraphs under
the information order, merge is the join — proven here
(`hypergraph_join`, Basic.lean). The general claim — the states of
arbitrary software under the information order form a join-semilattice
with merge as the join — remains an open spec point in the monotonicity
program's living spec, where no provision yet proves the semilattice law
for the general order. It is carried in this repository only as the
labeled premise shape `JoinSemilatticePremise`; no theorem here depends
on the general form. It closes at its home, by naming the general order
or deriving it, not here.

## What does not follow

The thesis is about information, not cost: it does not show carrying is
cheap, that a carried artifact is small, or that any particular build
already emits one. It does not show a conventional artifact is useless —
it determines the behavior exactly; the loss is measured against the
qualified quotient and is exactly the topology. And it does not discharge
the coverage premise of clpi/software-is-quantifiable: that executions are
mediated by sensing is assumed there and untouched here.
