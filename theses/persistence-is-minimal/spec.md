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
  representation of the whole corpus. The measurement
  form of this application is reported in the
  Application section; the form stated here stands open.
  Run: the application pipeline over the restart records
  corpus, with every verdict produced by the checkers of
  this development. Refuting observation: one computation
  the pipeline eliminates whose conclusion a later step
  needs and cannot derive, or one representation the
  pipeline certifies minimum that a exhibited candidate
  dominates on the campaign's own axes.

## Synthesis

The synthesis is assembled in `proof/Synthesis.lean`
(namespace `Synthesis`), proved under the same gate at
the same pin as the rest of this development. Its joined
theorem states the composed method for an arbitrary
system: given a record whose axis check passes, a datum
with a nonempty finite candidate space, recorded edges
and a store, versions, a nonempty workload list, and
admission of the record's segments, it concludes — in
order — freedom of the record on every checked axis;
sound redundancy elimination with the derivable set
unchanged; existence of a minimum representation;
frontier completeness over the candidate space;
independent checkability of the minimality verdict;
readability of every version under any growth of the
store; baseline-free measurement; incremental accounting
equal to full accounting, for measurement and for
re-checking alike; derived bounds on the workload list
attained by its members; admission of the composed
record; safety from the safety checker's acceptance;
quotient recovery by carrying representations; and the
candidate count as a computed power.

Every imported result enters in exactly one of three
forms.

Mirrored and discharged — the statement is the source's
verbatim, over definitions identical to the source's,
and the proof is this development's own:

- The losses core, from software-losses-are-compositional
  at d1159dc1e183061323afff362bca6234e34f7766: the
  mirrored definitions (derive, project, gap, free, the
  loss contract, grid, space, check, allcheck) and the
  theorems additive, projected, split, gapfree, composed,
  wholefree, compound, localizes, spacefinite, sound,
  allsound — the source's twelve core theorems. Its
  three controls stand in the source repo.
- The profiling baseline, from
  software-profiling-is-synthesizable at
  a53c4bf5aa83e8677ecb66571d61ed4c11e2d88d: the derived
  and measured forms mirrored (pderived, pmeasured), the
  baseline theorem proved by computation (profbaseline).
  The source's finiteness of configuration spaces is the
  same grid count as spacefinite. Its solved content —
  a least-cost member of any nonempty finite list — is
  proved here as leastcost, in this development's
  vocabulary.
- The traceability node content, from
  software-is-more-traceable-than-you-think at
  8f6a128069d0e68e97c4a69d78689c84350b0d2f: the source's
  fold is a two-sorted graph fold; its node projection
  is mirrored as the flat map of a contribution function
  (tfold), and fold membership (tmem) and retraction
  commutation (tretract) are proved.

Restated hypotheses — the source's vocabulary is not
mirrored; the result is an explicit hypothesis of the
joined theorem, with the source's own statement standing
at its pin:

- Frontier completeness (h_frontier), from
  software-optimality at
  95df5fb7e922e7316b0ebe90b7847fd45a208d88: the frontier
  completeness result of its general Pareto development
  (integer-valued there; natural-number form here).
- Bounds soundness and attainment (h_bsound,
  h_battained), from the same development: every
  collected value lies inside the derived bounds, and
  the bounds are attained by members.
- Incremental equals full (h_incr): one form, two
  sources — the incremental accounting theorem of
  software-profiling-is-synthesizable and the hypergraph
  incremental exactness of software-optimality.
- Re-check equals full check (h_recheck) and safety
  checker soundness (h_ssound), from
  software-is-incrementally-safe at
  97e55d28edc0d33f3466de3a3e4061e010c3b4d5: its
  recheck-from-scratch equivalence and its
  submitter-proof checker soundness.
- Admission composition (h_adm), from
  software-is-composable at
  7b1746467a410e9e5ae309f2a86bc4cd37700989: module
  admission composes under its interaction-closed side
  condition, which the joined theorem takes as an
  explicit input. The source's counterexample beside the
  theorem is the standing witness that the condition
  cannot be dropped — the same discipline as this
  development's controlfour.
- Carrying recovers the quotient (h_carry), from
  software-compilers-lose-info at
  69358971221d66e6304b64ff68a2e111d15231b3: its
  preservation result, by computation in the source.
  Its companion no-recovery result is the hypothesis of
  the lemma onlycarrying: an artifact map identifying
  two quotient-distinct programs admits no recovery —
  which is why the joined method claims recovery only
  for derivation-carrying representations, whose
  soundness is this development's certificate theorem.

Named premises — carried in the joined theorem's
antecedent, uninterpreted, each labeled a premise by its
own source. The conjuncts' proofs do not use them; they
bind where the method may be applied to a real system:

- Coverage, from software-is-quantifiable at
  d88acbdc3ba78fff994067d2c73bcc01622b3f61: the
  deployment-side obligations its interface results
  name.
- SpecAuthority, from software-is-incrementally-safe:
  the specification the checker enforces is the intended
  one.
- The general join-semilattice claim, from
  software-compilers-lose-info: proved there only for
  the hypergraph instance.
- Witness faithfulness, from
  software-profiling-is-synthesizable: facts enter the
  accounting only as certified witness states.
- Record fidelity, from
  software-losses-are-compositional: recordings are
  faithful, and a loss cell changes only on a
  same-contract re-measurement.

Correspondences — no hypothesis taken, recorded so the
accounting is complete:

- software-is-a-closed-loop at
  f2c3b6d643bba02e90fb16381d20c9b891210e65 contributes
  no hypothesis: its eleven theorems are instances (a
  batch tuning loop; a settlement ledger) whose general
  forms are the siblings' theorems already imported, and
  its role in this synthesis is the census and placement
  layer itself. Its head stands one enumeration commit
  past the pin recorded inside its own tree,
  ec47f7e42ad4f1438befdb7ab63af634d9e2fcaa.
- The closed loop's census ledger carries three lines
  stale against the repos' own heads: its
  incrementally-safe row predates that repo's final
  sweep, its traceability row predates that repo's
  in-repo thesis proof, and its optimality row predates
  the general Pareto discharge. Each repo's own state
  governs; the ledger lines stand as provenance only.
- software-compilers-lose-info cites the optimality and
  quantifiable developments at older pins than the ones
  used here. This synthesis imports at current heads and
  does not upgrade the source's citations.

Gaps the synthesis does not close, named:

- software-is-incrementally-safe has no recorded gate
  run at its head; its two restated results enter on its
  claims table and stated proof scripts, not on a gate
  log.
- The profiling development's visibility vector is
  proposed and open there, and re-solving as costs vary
  over time is open there; the joined method inherits
  both as open.
- The optimality development's stated not-proved list
  (instrumentation fidelity, hash binding, authorization,
  and the rest of its trust section) bounds every
  conjunct's reading as a claim about a real system.
- The tradeoff control bounds the composition
  conjuncts: minima are per qualification contract, and
  a cross-part tradeoff is visible to the method only
  when recorded as an interaction. The joined statement
  holds interactions fixed for exactly this reason.

## Application

One bounded application of the method, run as
measurement: the restart records corpus — the two JSON
lines files the fleet's restart recorder appends to
(cycles and policies). Measured 2026-11-19; the corpus
is append-only and growing, so the figures are the
measurement at that time, not a property of the files
forever.

Current representation: 3,516,608 bytes over 11,473
lines (cycles 3,027,709 bytes over 9,970 lines; policies
488,899 bytes over 1,503 lines). Both files are schema
uniform (17 keys in every cycles record, 11 in every
policies record), with zero parse failures and zero
exact-duplicate lines: the redundancy is value-level,
not line-level. Constant-valued keys: four in policies,
carrying 30,060 value bytes; none in cycles.
Low-cardinality keys (at most twenty distinct values):
eight in cycles carrying 409,207 value bytes; nine in
policies carrying 90,979 value bytes.

The alternative representation the method's steps 4 to
6 produce for this corpus — a dictionary and columnar
encoding: one dictionary per low-cardinality or constant
key, columns of dictionary indices or inline values,
from which the current records are exactly
reconstructible — measures 1,425,683 bytes total
(cycles 1,341,308, ratio 0.443011; policies 84,375,
ratio 0.172582; total ratio 0.405414), a saving of
2,090,925 bytes against the current representation on
the stored-size axis. A reference compressor over the
same files measures 280,522 bytes (ratio 0.079771),
recorded as context, not as a candidate: it is not a
representation in the method's sense, since nothing in
it is a derivation from recorded parts.

Verdict, at the method's own honesty standard: on the
stored-size axis, the current representation is NOT
minimum — the exhibited encoding is a witness candidate
strictly under it, in the sense of step 6's domination
check read on that one axis. The full Pareto verdict
over the qualification contract is UNMEASURED: the
blocking step is that no access-cost contract for this
store has been fixed — no named access, re-derivation,
and update axes with measured costs — so the remaining
axes cannot be priced and minimality cannot be checked.
The qualitative expectations stand as labeled statements
in the program record, not as measurements: dictionary
decoding adds an indirection per value on access;
appends stay cheap in both representations; single-value
updates are local in the current representation and
dictionary-mediated in the alternative.

No claim flips on this application: one corpus, one axis
measured, the rest named as the blocking step. The
end-to-end form — every verdict produced by this
development's checkers over the corpus — is the
falsification protocol's run above, and stands open.
