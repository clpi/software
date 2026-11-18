# software-compilers-lose-info

A conventional compiler is a map from a program's derivation structure to an
artifact that forgets it. That forgetting is provable information loss: two
programs that differ in derivable properties — different premise cones,
different provenance — compile to the same artifact, and no function of the
artifact recovers what was dropped. Idol's compilation is the negation: a
derivation inside the one semantic graph, whose artifact carries the
derivation structure, so the topology is preserved end to end and nothing is
ever reconstructed because nothing was lost.

This repository carries the full proof of that thesis, in three parts, and
its implications. The thesis is stated precisely in THESIS.md before any
proof, in the family's existing vocabulary (the hypergraph and closure of
clpi/software-optimality; the fold and coloring of
clpi/software-is-quantifiable). The proof is Lean 4.19.0, no Mathlib, under
the family check gate: zero sorries, zero custom axioms, the escape scan,
warnings as errors, every Lean file covered.

## Evidence state

Four states, never blurred: settled intent, proposed, implemented,
verified.

| Part | State |
|---|---|
| Thesis statement (THESIS.md) | settled intent as a claim; formalization verified |
| Loss: the forgetting compiler is non-injective on the qualified quotient, with a concrete distinguishing pair, and admits no recovery map | verified — Loss.lean, gate green |
| Preservation: the derivation-carrying compiler admits recovery of the qualified quotient from the artifact; premise cones exact from the artifact; joins commute at the topology | verified — Preservation.lean, gate green |
| Completeness: carried artifact equal if and only if qualified quotients agree | verified — Completeness.lean, gate green |
| Implications (IMPLICATIONS.md) | written — four proven corollaries (cone-exact revalidation and test selection at the compiler level, certification without reconstruction, the foreign-toolchain impossibility), the rest labeled proposals with closing conditions |

Premises the proof rests on are named in THESIS.md with their home pins —
the family's proven results are cited, never re-proven, and the one
foundation claim that is still an open spec point in the monotonicity
program (software states under the information order forming a
join-semilattice with merge as the join) enters only as a labeled premise;
its model-level instance over hypergraphs is proven here.
