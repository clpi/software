# The thesis, stated precisely

State of this document: the statement of the thesis is settled intent (Chris,
directive of 2026-11-18). Its formalization here is proposed until the Lean
proof in this repository is checked at a named pin; the record of what is
verified, and at which pin, lives in the README's evidence table.

## The objects

A **program** is a derivation structure: a directed hypergraph over a type of
nodes, in the exact form the family already uses — a root predicate and a
family of hyperedges, each hyperedge a premise list concluding in one node
(`Hypergraph` in clpi/software-optimality, module HypergraphIncremental, read
at pin 78b7b99b26ca241ac7a8964f2a4848489978c727). A node **derives** when it is
a root or some hyperedge's premises all derive — the least fixed point of the
positive Horn rules, `Derives` in the same repo's Qualification module, the
same closure clpi/software-is-quantifiable colors and folds over (read at pin
a21c7c56fa028f32014dd795b35b14f688e8fdf1).

From a program, two relations are read off:

- its **behavior**: which nodes derive;
- its **topology**: the reachability relation — one node reaches another when
  it occurs in a premise list on a chain of hyperedges concluding at the
  other. The premise cone of a node is the set of nodes reaching it. This is
  the dependency view the family already derives from the hypergraph for
  invalidation scoping; firing a hyperedge still requires all of its
  premises, never the projected edges alone.

The **qualified quotient** of a program is the pair (behavior, topology).
Two programs agree on the qualified quotient when both components are equal.
This is the quotient the qualification machinery itself induces: equivalence
of terms under the derivation machinery, observed through everything the
machinery can derive about a program — what derives, and what depends on
what. The fold and the coloring of clpi/software-is-quantifiable are
functions of exactly this data.

A **compiler** is a map from programs to artifacts. A **recovery map** for a
compiler is a function from artifacts back to qualified quotients that
returns, for every program, that program's own quotient.

## The three claims

**Loss.** A compiler loses information when two programs that disagree on
the qualified quotient share an artifact. Where a compiler loses
information, no recovery map exists for it: a recovery map would have to
return two different quotients for one artifact. The conventional compiler
is the instance that matters: its artifact determines the program's behavior
and forgets the topology. The proof exhibits two concrete programs with
identical behavior and different premise cones — in one, the output node is
a root; in the other, it derives through a premise — sharing one artifact
under the forgetting map. Every tool that works from a conventional artifact
alone (a debugger reconstructing provenance, a profiler attributing cost, an
incremental builder or a test selector recomputing what a change touches) is
therefore re-deriving, approximately and at cost, data the compiler had and
discarded; exact provenance is not among what can be re-derived, because no
function of the artifact returns it.

**Preservation.** Idol's compilation is the derivation-carrying projection:
the artifact carries the behavior and the topology as its own components —
compilation is a derivation inside the one graph, not a map out of it. For
this compiler a recovery map exists and is a retraction on the quotient: the
quotient is a function of the artifact alone. Premise cones read from the
artifact are the source's premise cones, exactly. Joins commute at the level
of the topology: the topology of a merged program is the transitive closure
of the union of the two topologies — merging first and compiling second
yields the same topology as compiling first and joining second. (The
behavior of a merge is the closure of the merged graph and can exceed both
parts' behaviors; it is always read off the carried graph of the actual
merged program, never synthesized from the parts' behaviors. The statement
here is exact about which component commutes.)

**Completeness.** The two halves meet. The carried artifact determines the
source up to exactly the qualified quotient, in both directions: two
programs have the same carried artifact if and only if they agree on the
qualified quotient. The information the conventional map loses is exactly
the derivation structure, and carrying exactly that is sufficient — nothing
else about the source is needed to recover everything the qualification
machinery can derive, and nothing the machinery can derive is missing.

## Premises, named

The proof in this repository rests on the family's proven results as cited
premises, each at its home pin, and re-proves none of them:

- The closure semantics (`Derives` as least fixed point of positive Horn
  rules) and the hypergraph form: clpi/software-optimality, Qualification
  and HypergraphIncremental, pin 78b7b99b26ca241ac7a8964f2a4848489978c727.
- Exactness of premise-cone-scoped revalidation over the hypergraph
  (`incremental_exact`, with `incrementalFrontier_exact`): same repo, same
  pin. The compiler-level corollary proven here is only that the cone the
  revalidation runs over is available, exactly, from the carried artifact.
- Finiteness of the qualified space, the witness fold, and the coloring
  under its one side condition: clpi/software-is-quantifiable, pin
  a21c7c56fa028f32014dd795b35b14f688e8fdf1. Coverage — that sensing mediates
  every execution — remains a named premise there, and nothing here
  discharges it.

One foundation claim is **not** available as proven anywhere yet, and this
repository does not smuggle it in: that the states of arbitrary software,
under the information order, form a join-semilattice with merge as the join
(the monotonicity program's foundation claim; its living spec carries the
open point that no provision yet proves the semilattice law). What the proof
here needs is only the model-level fact, and that fact is proven in this
repository: over hypergraphs under the pointwise inclusion order, merge
(rule union) is the least upper bound. The general claim over all software
states enters the implications as a labeled premise with that home, never as
a theorem of this repo.

## What this document is not

It does not claim a conventional artifact determines nothing: it determines
the behavior, and the loss is measured exactly against the qualified
quotient. It does not claim carrying is free, or that any particular Idol
build already emits carried artifacts; which implications are proven
corollaries and which are proposals about the implementation, with their
closing conditions, is the implications document's job, kept separate from
the proof.
