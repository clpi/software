# Persistence is minimal: the specification

## The claim

Settled intent, in the author's terms (directive of
2026-11-19): construct an analysis methodology that
proves — rigorously, incrementally, certifiably, and
machine-checkably — redundant computation, and
Pareto-optimal compression of persistent data to its
minimum representation, across many empirically
falsifiable and validatable means, including functional
representation and semi-persistence across the hypergraph.

Four states are kept distinct throughout this document:
settled intent, proposed semantics, implemented behavior,
verified behavior. The claim above is settled intent. The
Lean development in `proof/` is implemented behavior; what
the family gate checks at the landed pin is verified
behavior. Nothing below upgrades a claim's state on the
strength of prose.

## The executable method

Each step names the artifact it produces and the measure
it carries. Steps 2, 3, 6, 7, and 9 are the steps whose
correctness the Lean development proves; the remaining
steps are campaign discipline around them.

1. **Record the persistent state.** Fix the stored facts
   (a list of parts) and the recorded hyperedges (premise
   list, conclusion). Measure carried: the fact count and
   the edge count of the state.
2. **Test redundancy by certificate.** For a computation
   whose conclusion is claimed already derivable, produce
   a certificate: the recorded edges used, in order,
   naming only the premise cone. Run the checker
   `checkCert`; it re-runs the certificate (`runCert`),
   confirming every edge is recorded, every premise is in
   the accumulated store at its step, and the target lands
   in the final store. Measure carried: the certificate
   length, and the checker verdict. Soundness: `certsound`.
3. **Eliminate what is redundant.** Drop each computation
   whose conclusion is certified derivable; adjoin nothing.
   Measure carried: the count of computations eliminated,
   against the guarantee of `elim` that the derivable set
   is unchanged in both directions.
4. **Fix the qualification contract.** Name the finite
   choice alphabet and the axis list. The candidate space
   is `reps` over the alphabet at the datum's length.
   Measure carried: the candidate count, the computed
   power of `finite` — alphabet size raised to datum
   length.
5. **Price every candidate.** For each candidate
   representation and each axis, compute `cost` as the sum
   over zipped (part, code) pairs. Measure carried: the
   per-axis cost vector of every candidate. Segment
   pricing composes by `costadd`.
6. **Check minimality independently of production.** The
   checker `minimalB` confirms a claimed minimum is a
   candidate and that no candidate dominates it, through
   the boolean domination check `domB`. Measure carried:
   the count of candidates checked and the domination
   verdicts. Soundness: `mincheck`, on the bridge
   `dombridge`.
7. **Produce minima by the fold.** Where no minimum is yet
   claimed, run the choice procedure `choose`: a fold
   keeping an undominated candidate. Measure carried: the
   fold length, equal to the candidate count. Its output
   is minimum by construction: `choosemin`; existence in
   any nonempty candidate list: `existsmin`.
8. **Compose by segments, holding interactions fixed.**
   Price and minimize segment by segment only with the
   remaining segments held as a recorded interaction at
   fixed cost: domination of a segment lifts to the whole
   (`domlift`), and a minimum of the whole has minimum
   parts (`wholemin`). Measure carried: the per-segment
   costs and the interaction segment's cost. The converse
   direction is not available: the cross-part tradeoff
   control (`controlfour`) proves part minima need not
   compose, so any cross-segment tradeoff must be recorded
   as an interaction term to be visible to the check.
9. **Carry versions semi-persistently.** A version is
   readable exactly while every part of it is derivable
   (`Readable`). Before dropping any stored fact or edge,
   re-check the readability of every live version against
   the reduced state. Measure carried: the per-version
   readability verdicts, and the total version cost
   `vcost`, which splits per version by `vcostcons`.
   Keeping a shared premise as a recorded interaction is
   the positive move: `kept`.
10. **Grow incrementally, never re-qualify from scratch.**
    Additions to the store or the edge list — and only
    additions — preserve every checked certificate
    (`certmono`, on `runmono`) and every readable version
    (`readmono`). Measure carried: the count of
    certificates re-validated after each addition, which
    the theorems say is all of them, and the count of
    additions after which any certificate failed, which
    the theorems say is zero.

## Theorem inventory, at honest strength

All theorems below are proven outright in the Lean
development — full proofs, no premises inside the model,
printed axioms a subset of {propext, Quot.sound} as the
gate log shows; several depend on no axioms at all. The
two premises that remain are campaign-level, outside the
Lean development, named after the inventory.

Derivability (`proof/Core.lean`):

- `stepclose` — a recorded edge whose premises are all
  derivable has a derivable conclusion. Proven outright.
- `monof` — derivability is monotone in the store.
  Proven outright.
- `monoe` — derivability is monotone in the recorded
  edges. Proven outright.
- `elim` — adjoining an already derivable fact to the
  store changes the derivable set not at all, in both
  directions. Proven outright.

Certificates (`proof/Core.lean`):

- `runsound` — a successful certificate run leaves only
  derivable facts in its final store. Proven outright.
- `runmono` — a successful run stays successful under a
  larger store, and its final store only grows. Proven
  outright.
- `certsound` — a certificate the checker accepts
  witnesses a genuine derivation of the target. Proven
  outright.
- `certmono` — a checked certificate stays checked as the
  recorded edges and the store grow. Proven outright.
- `certcomp` — certificate composition at the run level:
  a successful first run composes with a second run from
  its final store. Proven outright.
- `certcompcheck` — the same composition at the checker
  level. Proven outright.

Representations and minima (`proof/Core.lean`):

- `finite` — the candidate count is the alphabet size
  raised to the length, a computed power. Proven outright,
  on the counting lemmas `sumconst` and `sumconstf`.
- `costadd` — cost is additive over append of data and
  representations, under segment length agreement. Proven
  outright; depends on no axioms at all.
- `dombridge` — the boolean domination check decides the
  domination proposition, in both directions. Proven
  outright.
- `mincheck` — the minimality checker is sound. Proven
  outright.
- `domirr` — domination is irreflexive. Proven outright.
- `nodom` — domination is transitive, with strict-axis
  propagation. Proven outright.
- `choosecore` — the fold invariant of the choice
  procedure. Proven outright.
- `choosemin` — the choice procedure's output is a
  minimum. Proven outright.
- `existsmin` — every nonempty candidate list carries a
  minimum. Proven outright.
- `domlift` — domination of a part lifts to the whole
  with the other segments fixed. Proven outright.
- `wholemin` — a minimum of the whole has minimum parts.
  Proven outright.

Semi-persistence (`proof/Core.lean`):

- `readmono` — readability is monotone in the store.
  Proven outright.
- `vcostcons` — total version cost splits at the head.
  Proven outright.
- `kept` — with the shared premise stored, the version
  deriving through the recorded edge stays readable.
  Proven outright.

Controls (`proof/Controls.lean`), each a proved negation
standing in the tree:

- `controlone` — axis relativity: a representation
  minimum on a restricted axis list is dominated on the
  full list.
- `controltwo` — an edge whose premise is outside the
  closure does not make its conclusion derivable (through
  the general `noderiv`).
- `controlthree` — naive per-version compression that
  drops the shared premise loses a still-readable
  version; keeping the premise restores it.
- `controlfour` — a cross-part tradeoff dominates the
  append of part minima in the composed datum.

Named premises, campaign-level, outside the Lean
development:

- **Edge faithfulness.** An edge recorded in the
  persistent list is faithful to a real derivation: the
  system actually produced the conclusion from those
  premises. The Lean development proves everything from
  the recorded list; it cannot prove the list honest.
- **Cost fidelity.** A campaign's cost assignment — its
  axes — tracks real costs: real bytes, real time, real
  retrieval effort of materialized versus functional
  representations. The Lean development proves optimality
  relative to the axes named; which axes track reality is
  the campaign's evidence.

## Falsification protocols

Every load-bearing claim not proven outright is paired
with the run that could refute it: the concrete run, the
corpus, and the refuting observation.

- **Edge faithfulness (premise).** Run: take a real
  persistent corpus — the restart records files named in
  the program record — replay each recorded edge against
  the execution log it claims to summarize, and check the
  conclusion was in fact produced from the premises.
  Refuting observation: one recorded edge whose premises
  held in the store at its recorded time and whose
  conclusion was never produced, or was produced from
  other premises. One such edge falsifies the premise for
  that corpus and voids every redundancy verdict resting
  on it.
- **Cost fidelity (premise).** Run: on the same corpus,
  for a sample of parts, measure the real cost of the
  materialized representation (bytes stored, retrieval
  time) and of the functional representation (derivation
  replay time, premise storage share), and compare the
  ordering against the campaign's axis costs. Refuting
  observation: one part whose axis ordering of the two
  representations is strictly opposite to the measured
  ordering on a load-bearing axis. That falsifies the
  axis, not the theorems: minima are then re-qualified
  under a corrected axis.
- **Candidate completeness (proposed semantics).** The
  claim that a real campaign's representations are
  exhausted by `reps` over its contract alphabet. Run:
  enumerate `reps ch n` for the corpus's datum lengths
  and check every representation in actual use appears.
  Refuting observation: one in-use representation absent
  from the enumeration — the alphabet was incomplete, and
  minimality verdicts over the smaller space do not
  transfer.
- **End-to-end methodology (proposed).** The claim that
  the ten steps above, run on a real corpus, eliminate
  exactly the redundant computations and reach a minimum
  representation of the whole corpus. This is the
  application section's work and stands open. Run: the
  application lane's pipeline over the restart records
  corpus, with every verdict produced by the checkers of
  this development. Refuting observation: one computation
  the pipeline eliminates whose conclusion a later step
  needs and cannot derive, or one representation the
  pipeline certifies minimum that a exhibited candidate
  dominates on the campaign's own axes.

## Synthesis

open

## Application

open
