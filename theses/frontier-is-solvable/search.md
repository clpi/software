# The frontier technique

This document is the specification of the structural bounded technique for
solving and searching the search-space frontier optimally. It extends the
schedule development in the README with the general search layer proved in
the search module. Every claim carries one of four states, never blurred:

- **settled intent** — what the technique is required to mean.
- **proposed** — stated exactly, not yet proved; a closing route is named.
- **implemented** — present in the code at this pin.
- **verified** — proved in Lean at this pin under the family gate
  (the check script: no proof escapes, warnings as errors, Lean 4.19.0).

Theorem names below are the single-word names of the search module and of
the earlier qualification-frontier module it builds on.

## 1. The space

**Settled intent.** The possible states of a system form a join-semilattice
of terms up to equivalence. The hypergraph is the source of truth; any
dependency graph or incidence view is derived from it, never the other way
round. The space is equality-saturated on the possible side: closing a set
of states under the transition steps adds every reachable state, and the
closure is the least such closed set.

**Implemented and verified.** Possible states are carried as lists, and the
equivalence is membership equality: two lists name the same space when they
have the same members. The join of two spaces is list append. The join laws
hold as membership statements: a state is in a join exactly when it is in a
part; join commutes, associates, and is idempotent under this equivalence.
Saturation is the predicate that a state belongs to every closed list
containing the seed list. It contains the seed, it is closed under one
transition step, it is the least closed extension (anything it names is in
every closed extension), and it is monotone in the seed. The hypergraph
round trip and the extensionality of derived views are proved in the
hypergraph module and the earlier frontier module respectively: a view
that agrees on membership and on dominance gives the same frontier.

**Citation.** The general hyperlattice vocabulary has its home in the
bidirectional repository at pin b14fc92b: its core model carries states
up to equivalence as a join-semilattice (the hyperlattice), recorded
steps and their derivability closure, and bounds over candidate lists
with incremental tightening, under the family gate. This module proves
the finite-list instance of those facts directly and uses none of that
repository's theorems as proof steps; where the technique is stated for
the general hyperlattice rather than for finite lists, that pin is the
citation, per family discipline.

## 2. Two filters, never conflated

**Settled intent.** Two distinct filters act over the possible space. The
observed filter keeps what an environment setting makes visible. The
qualified filter keeps what is both intended and observed. Neither filter
is the other, and no result may trade one for the other.

**Implemented and verified.** Observation is the dial mask of the
hypergraph module: raising the dial never drops a visible incidence, and
every visible incidence is an incidence of the complete graph.
Qualification is the four-color painting: a state qualifies exactly when
its color is the intended color, which requires it to be both wanted and
seen. The search module proves that every qualified state is seen and
wanted. On the demo hypergraph at dial zero the qualified list is exactly
the first two states; the third state is wanted but unseen (a gap) and is
proved not qualified. An unseen state fed to dominance is blocked by the
three-valued gate, as the schedule module's gap result shows.

## 3. The frontier

**Settled intent.** The frontier is the nondominated set of the qualified
space under the contract axes: a qualified state is on the frontier
exactly when no qualified state dominates it. Membership is maintained
incrementally: when states join, when a state is inserted, and when a
state is retracted, the new frontier is determined by the old one and the
change, never by an unstated recomputation.

**Implemented and verified.** The evaluator filters the candidate list by
the qualification predicate, then keeps exactly the members no other live
member dominates. Its exactness theorem states that membership in the
output is the frontier predicate over the qualified candidates. Insertion
is exact: the frontier after inserting one state is the old frontier
filtered by the inserted state, plus the inserted state when nothing old
dominates it. Retraction is exact: a retracted frontier is the old
frontier minus the removed states, plus exactly the candidates whose
every former dominator was removed. Joining is exact under a per-state
qualification: the frontier of a join is the frontier predicate over the
joined membership, so part frontiers compound through the joined filter.
The replica placement example is the standing warning that filtering a
former frontier is not this update: offline fallbacks that were dominated
before the change are on the new frontier and are lost by filtering.

## 4. Bounds

**Settled intent.** Each axis carries a lower and an upper bound over a
space: the greatest lower bound and the least upper bound of the readings.
When spaces join, the bounds of the join are computed from the bounds of
the parts and compound: the bound of a join is at least as tight as the
bound of each part. The exact side condition is that qualification is a
per-state predicate applied over the joined space (section 3); a
qualification that looks at the whole list does not compound, and the
control below proves the condition cannot be dropped.

**Implemented and verified.** The bound of a join is the minimum of the
lower bounds of the parts, and dually the maximum of the upper bounds.
Any lower bound of a join is a lower bound of each part, and the greatest
lower bound of a join is at most the greatest lower bound of each part:
bounds tighten monotonically under joins, with no side condition beyond
the bounds existing. A greatest lower bound exists on every nonempty
finite list, for every axis. A bound computed on a part alone is in
general not a bound on the join; the control in section 9 proves this on
a named instance. The general hyperlattice form of these bounds — bounds
over candidate lists with incremental tightening — is the core model of
the bidirectional repository at pin b14fc92b, cited in section 1; the
statements here are its finite-list instance, proved here.

## 5. Boundedness

**Settled intent.** The qualified search space is finite, and this is
derived from what a qualification is, never assumed as a hypothesis. A
qualification names its software, its criteria, and the behavior intended
under them; its runs and venues are lists by construction.

**Citation, not re-proof.** The finiteness thesis has its home in the
quantifiable repository at pin d88acbdc (the merge of its sixth pull
request). Claim one of its table records the thesis as proved there: an
explicit finite list enumerates every schedule and every valid ordering
of a qualification, and its finiteness module notes that finiteness falls
out of the definitions, with no finiteness hypothesis anywhere in that
repository. This repository cites that result and does not re-prove it.

**Implemented and verified here.** In this repository a search space is a
finite list of candidates by construction of the space type, and the
exhaustive solver's output is a sublist of it. The search bound is a
computed quantity of the qualification, stated exactly: the number of
dominance comparisons of the exhaustive search over a candidate list is
bounded by the square of the list's length, one comparison per ordered
pair of candidates. The square of a join is computed from the parts: the
length of a join is the sum of the lengths. The output length bound —
the frontier has at most as many members as the candidate list — is
proved at this pin as part of the optimality statement below.

## 6. Speculative search

**Settled intent.** Search may run under hypothesized qualifications or
hypothesized states. A speculative result is valid exactly on its premise
cone: the set of hypotheses it depends on. Discharging a hypothesis (it
turns out true) or refuting one (it turns out false) updates the results
incrementally, never by re-running the search from scratch.

**Implemented and verified.** A speculation is an eligibility predicate
extended by a list of hypothesized states. The cone theorem: every member
of a speculative frontier is either a member of the real frontier or is
itself one of the hypotheses — so a result with no hypothesis in its cone
is premise-free and stands unconditionally. Discharge: when every
hypothesis is in fact eligible, the speculative frontier is the real
frontier, by extensionality of the eligibility view; the update is the
identity on membership. Refutation of a single hypothesis: every other
speculative frontier member is a real frontier member, by the insertion
exactness theorem; removal of a set of hypotheses is governed by the
retraction exactness theorem. Both updates are stated as frontier
characterizations, so applying them needs no recomputation.

**Proposed.** Speculation over hypothesized states with hypothesized
readings (a candidate that does not yet exist, with a reading that is not
yet measured), and nested premise cones (a hypothesis that itself rests
on hypotheses). Closing route: model a hypothesized state as an insertion
into the candidate list together with an extension of the readings
function, and reuse insertion exactness; model nesting by iterating the
speculative eligibility construction and composing the cone theorems.

## 7. Weightings

**Settled intent.** A weighting is a tuned confidence weighting over the
search space: it orders the search, and it never bounds it. Under a
weighting the qualified search remains incrementally solvable (sections
3 and 6). Weightings are reweightable and rewritable on the fly. A
weighting is adopted on its metric empirical outcome, never on its
intent alone, and it stays reconstructable and solvable later. Where a
weighting is not mapped to a rigid semantic intent, the mechanism is
constructively self-clarifying: the weighting's own effect on the
frontier is itself a constructed, inspectable object.

**The mechanism (implemented).** A weighting is data: a total function
from states to natural-number confidence weights, together with the
candidate list. The weighted order is insertion of each candidate into
the ordered list of the rest at its weight rank (lighter first; ties
keep list order). The search is the evaluator of section 3 run over the
weighted order. The weighting governs exactly two things: the order in
which candidates are examined, and the order in which speculative
hypotheses (section 6) are explored. It governs nothing else.

**The rule (settled intent, with proved enforcement where stated).**

1. Never an upper bound. No weighting may exclude a qualified state
   from the returned frontier, prune a candidate, or tighten a bound.
   A change that alters frontier membership is not a reweighting; it is
   a change of qualification, governed by sections 2 and 3.
2. Reweightable on the fly. Replacing the weight function at any point
   changes only the examination order of what remains. Results already
   returned stand.
3. Adopted on metric empirical outcome. A weighting replaces the
   incumbent when a stated metric, measured on a named instance set,
   improves: for example the counted comparisons of the counted
   evaluator proposed in section 8, or time to an accepted certificate.
   The adoption record names the metric, the instance set, and both
   weightings. This rule is campaign discipline, not a theorem.
4. Reconstructable. A past search is reproduced exactly from its
   recorded weight function and candidate list; both are data, and the
   order construction is a function of them.
5. Self-clarifying. The effect of a weighting is a constructed object:
   the trace, the pair of the induced order and the frontier computed
   under it. Two weightings are compared by comparing their traces.

**Verified in Lean at this pin.** Insertion preserves membership, so
the weighted order has exactly the candidates as members. Frontier
membership depends only on candidate membership, never on order: for
any two lists with the same members, the evaluator's membership
coincides. Therefore, under every weighting, the returned set is the
complete nondominated qualified set (the full statement: membership
under a weighting is the frontier predicate itself), and changing the
weighting mid-search leaves the final frontier membership unchanged —
reweighting is exact, with no recomputation of what the frontier is.
The trace is sound: its frontier component is the true frontier. On a
named two-state instance the weighting provably changes the returned
list (the order flips) while the frontier predicate is unchanged: order
is all a weighting moves.

**Proposed, with closing routes.** A proved characterization of the
moved set — the states whose rank changes between two weightings — and
of its relation to speculative cone exploration order. Route: define
rank from the trace order, prove the moved set is exactly the symmetric
difference of the two rank orders, and order cone exploration by rank.
The counted-comparison metric of rule 3 rides on the counted evaluator
proposed in section 8.

## 8. The optimality statement

**Settled intent.** Optimal means three things together: the returned
frontier is the complete nondominated set of the qualified space; the
search returns no state outside the qualified closure; and the cost of
the search is bounded by the stated function of the qualification
(section 5).

**Verified in Lean at this pin.**

1. Completeness and soundness of the returned set: a state is in the
   evaluator's output exactly when it is a qualified candidate and no
   qualified candidate dominates it.
2. Nothing outside: every returned state is a member of the candidate
   list, and the output is no longer than the candidate list.
3. Bounds compound exactly under joins, tighten monotonically, and exist
   on every nonempty finite list (section 4).
4. Updates are exact: insertion, retraction, and joins under a per-state
   qualification (section 3).
5. Speculative results are valid exactly on their premise cone, and
   discharge and refutation update them without recomputation
   (section 6).
6. For finite schedule spaces, the imported gate results: every output
   point is free of dominance in both the contract sense and the
   canonical profile sense, every undominated point is emitted together
   with its reading vector, a dominated point is answered with a named
   dominator, and the certificate checker accepts exactly this frontier.

**Proposed, with closing routes.**

7. The operational comparison count of the shipped evaluator is the
   square bound of section 5. Route: a counted evaluator, proved to
   return the same frontier as the exhaustive evaluator with a counter
   bounded by the square of the candidate length.
8. A pruning search that skips pairs the bounds already decide, returning
   the same frontier faster. Route: soundness of pruning from the
   tightening theorems plus a named dominator witness for every pruned
   point, in the shape of the schedule module's named-dominator result.
9. Speculative search over hypothesized states and nested cones
   (section 6). Route: insertion plus readings extension, as stated.

**Not claimed.** No polynomial bound: multi-objective scheduling with
precedence is NP-hard in general, and the exhaustive search is
exponential in the feasible set, as the README limits state. Nothing is
claimed about systems that have not been cut down to a finite space,
about readings that were not supplied, or about candidates outside the
space.

## 9. Standing controls

Each control is a proved negation or a proved inequality over a concrete
instance, in the repository's existing control style. A control that
starts passing is a defect in the technique, not in the control.

1. Dropping the qualified filter makes the frontier wrong. On the named
   three-state instance (the trade-off instance of the test module, with
   the third state dominating both axes), the unfiltered frontier is the
   single dominating state, while the frontier under the qualification
   that excludes it is the two trade-off states. The two are proved
   unequal, and the unfiltered winner is exactly the state the filter
   excludes.
2. A qualification that is not a per-state filter breaks compounding.
   Under a whole-list capacity qualification (only the first two states
   of a list qualify), qualifying each part before joining and then
   taking the frontier gives a different answer from qualifying the
   joined list: proved unequal on the same three-state instance. This is
   the side condition of sections 3 and 4, shown necessary.
3. A part bound is not a join bound. The value that bounds the first
   state alone on the second axis is proved not to be a lower bound of
   the two-state join, because the joined state reads below it.
4. Scoring an unknown as intended changes the frontier (the red module's
   shift result), and a dominated schedule offered as the frontier fails
   the certificate (its rejection result). Both predate this layer and
   remain in force.
5. Filtering former winners is not recomputation (the replica placement
   example): after the hub outage, the correct frontier contains
   fallbacks that filtering the old frontier provably loses.

## 10. The bet

**Status: a bet, recorded as a bet.** The following claim is not a
premise of anything in this repository, is not used as a hypothesis in
any proof here, and is not implied by the theorems above. It is the
campaign's search-space bet, stated exactly so that evidence can settle
it.

**Statement.** For every qualification in the campaign corpus, the
qualification-constructed candidate set and the contract extraction
process that produces it are: deterministic (the same qualification
yields the same candidate set and the same contracts, at the same pin);
bounded (by the computed bound of section 5, evaluated on that
qualification); solvable (the exhaustive search of section 3 terminates
on the set with the exact frontier, and its certificate is accepted);
and incrementally solvable along tuned confidence weightings (the
updates of sections 3 and 6 and the reweightings of section 7 keep every
result exact, with no recomputation from scratch).

**What settles it for.** A corpus instance, at a named pin, where all
four properties are checked: extraction run twice with identical output;
the candidate count at or under the computed bound; the certificate
accepted; and an insertion, a retraction, and a reweighting each
agreeing with full recomputation on that instance. Accumulating such
rows across the corpus is evidence for the bet, at the strength of the
corpus's coverage — never a proof of the universal statement.

**What settles it against.** A single corpus instance, at a named pin,
failing any one property: two extractions of one qualification
disagreeing; a candidate count above the computed bound; a rejected
certificate on a set the extraction produced; or an incremental update
or reweighting whose result differs from recomputation. One such row
refutes the bet as stated, and the refutation is recorded, not
repaired silently: the bet is then restated at the strength the
evidence supports.

**Where evidence accumulates.** The campaign census: the bidirectional
repository's census at its pins, the theses synthesis that joins the
family, and one behavioral hypergraph per library in the library
repository, each row dated, pinned, and labeled campaign evidence. This
repository's contribution to the corpus is its instance modules and
examples, whose outputs the gate reproduces exactly.

## 11. The candidate space

This section is the specification of the candidate space: the
structurally searchable space of candidates drawn from the graph of
behavior. It is proved in the candidate module, which cites the
search and frontier modules and re-proves none of their results.
Theorem names below are the single-word names of the candidate
module, together with the names it cites.

**Named premise, with its falsification route.** The graph in this
section is the singular hypergraph of the ruling given by Chris on
2026-11-19 at 15:43 Pacific: the total equivalence graph of
equivalent terms, symbol-bound at minimum resolution, bound only by
the finite resolved upper bound at resolution time via the only
lattice; resolution levels reconciled on the same graph; growth
append-only; colorings and qualifications constructed from it, with
overlapping qualifications appended or colored in the same edges.
The list constructions used in the proofs (candidate lists with
premise and conclusion readings, incidence counting) are a finite
instance of that graph, never the graph itself, and no statement
here presents them as it. Falsification route: a parallel program
is re-founding the redundant-compute theory on this model; if its
disposition, recorded at
`~/workspace/research/redundant-compute-coloring-2026-11-19.md`
when it lands, rejects or revises the ruling, every statement in
this section that rests on the premise is re-examined against the
disposition. At the time of writing that record has not landed, so
the premise stands at the strength of the ruling itself. The
finiteness used below is derived from what a qualification is
(section 5), never assumed.

**Settled intent.** The space is drawn from the append-only graph
of possible, observed, qualified, disqualified, and otherwise
colored behavior. A candidate enters by append and never by
rewriting what the graph already carries. Qualification and
disqualification are colorings of the candidate in the standing
sense of section 2: the observed filter and the qualified filter
are distinct, and no result trades one for the other. A candidate's
standing is its measure vector under a weighting epoch (section
11.3). The solved set of the space is the nondominated qualified
set under the epoch's measures, maintained with the exactness of
sections 3 and 6 as the graph appends.

### 11.1 The candidate record

**Implemented.** A candidate record is data with four parts. The
entry carries the candidate's own term, the list of terms it is
composed from (its parts), and the list of premise terms it builds
on (its links). The score carries the six improvement readings of
section 11.2. The two filter inputs, seen and wanted, carry the
observed side and the intended side separately. The record's
coloring is the four-color painting of the hypergraph module
applied to exactly those two inputs, and its qualification is the
boolean that both inputs hold.

**Verified.** A record whose qualification holds has the intended
color (`record.intended`). The projection from a list of records
to a space is a definition: identifiers are the record terms, the
reading of an identifier is the reading of its record's score, the
qualification of an identifier is the qualification of its record,
and an identifier with no record reads zero and does not qualify
(`project`). The solved set of the projected space is the solved
set of the records by the definition of the solved set below.

### 11.2 The measures

Each measure is a computable function or relation over the record
and the space, stated with its direction. No measure is a prose
judgment.

- **Net-newness** (`fresh`). What the candidate adds that the
  carried list does not already carry: one for its own term when
  that term is new, plus one for each part that is not carried.
  Direction: higher is more new. Evidence: the count itself,
  computed from the record and the carried list. Verified at its
  boundary: a carried term with no parts reads zero, and a new
  term with no parts reads one (`fresh.done`, `fresh.one`).
- **Impact** (`reach`). How many entries of the space are composed
  from this candidate's term. Direction: higher reaches more of
  the space. Evidence: the count itself, computed from the space.
  Verified at its boundary: the empty space reaches zero
  (`reach.nil`).
- **Novelty of composition** (`blend`). Zero when the term is
  already carried; otherwise the count of its parts that are
  carried, so a recombination of carried parts into a new term
  reads high and a composition of wholly new parts reads low.
  Direction: higher is a more novel recombination of what exists.
  Evidence: the count itself. Verified at its boundary: a
  candidate with no parts reads zero either way (`blend.done`).
- **Gap-solving** (`solves`). The count of gaps of the space that
  the candidate closes, under the closing relation of section
  11.4. Direction: higher closes more gaps. Evidence: the count
  itself, computed from the gap list and the closing relation.
- **The improvement axes** (the score). Six readings, each a
  natural number, higher is better on every axis, each with its
  evidence requirement. Better (`gain`): the stated quality
  reading of the candidate's behavior, evidenced by a checked
  comparison against the incumbent it would replace. Faster
  (`speed`): the stated time reading, evidenced by a timed run at
  a named pin on a named venue. Less redundant (`lean`): the
  stated count of duplicated behavior the candidate removes,
  evidenced by the graph count before and after. More powerful
  (`power`): the stated count of behaviors the candidate makes
  derivable that were not derivable before, evidenced by the
  derivability closure count. More expressive (`width`): the
  stated count of distinct forms the candidate can state,
  evidenced by enumeration of the forms. More ergonomic (`ease`):
  the stated character count of the shortest form that invokes
  the candidate, evidenced by the counted canonical form. A
  reading with no evidence of its stated kind is not a reading;
  it is absent, and absence is handled by the three-valued
  discipline of the schedule layer, never by scoring an unknown
  as intended (section 9, control 4).

**Verified.** The score reading turns a score into a cost by
negation on the six axes and zero off them, so the existing
dominance vocabulary applies unchanged. Equal scores are never a
strict win (`score.tie`, by the frontier module's ties result).
Dominance on the six axes is exactly the pareto form: no worse on
every axis and strictly better on one (`score.exact`, by the
frontier module's pareto exactness).

### 11.3 Epochs and the solved set

**Implemented.** A space is a finite list of candidate
identifiers, a reading function, and the qualification coloring
as a boolean predicate. An epoch is data: the active axis list
and a total confidence weighting, in the sense of section 7. The
solved set under an epoch is the evaluator of the frontier module
run over the weighted order of the candidate list, qualified by
the coloring and dominated under the epoch's axes.

**Verified.**

1. Exactness. The solved set under a weighting epoch is exactly
   the nondominated qualified set of candidates under that
   epoch's measures (`exact`). The proof is a thin join: it is
   the search module's `full` statement, which itself joins its
   `weighted` statement to the frontier module's evaluator
   exactness. Nothing is re-proved.
2. Weightings never bound. Membership in the solved set depends
   on the epoch's axes and never on its weighting: two epochs
   with the same axes solve the same set (`same`, by the search
   module's reweighting statement). A weighting change is exact
   and moves order only, as section 7 already established.
3. Epochs are appended records. The solved set at an epoch index
   is a function of that index's record alone (`replay`: two
   epoch lists agreeing at an index solve the same set there).
   Appending a new epoch never changes an earlier index's solved
   set (`keep`, by induction on the epoch list). Every earlier
   epoch's solved set therefore stays exactly reproducible from
   its epoch record.

### 11.4 Gaps as objects of the space

**Settled intent.** A gap is a first-class structural object in
the same space, never a prose note. It is itself constructive and
solvable across the same parametric dimensions as a candidate,
and it carries its own measure vector.

**Implemented.** A gap record carries an axis list, a target
reading on those axes (its mark), its own term, and the epoch
index at which it entered. Its measure vector is four computable
counts: its size, the axis count (`gsize`); its reach, the count
of candidates that close it, the dual of impact (`greach`); its
open width, the count of its axes on which every candidate still
reads above the mark (`gopen`); and its age, the count of epoch
records since it entered (`gage`). A
candidate closes a gap when it dominates the gap's target
reading on the gap's axes, under the reading that sends the
gap's term to its target and every other term to the space's
reading (`closes`). Gap-solving for a candidate is the count of
gaps it closes (`solves`, section 11.2).

**Verified.** Closing is decidable within the space's finite
bound: the scan of the candidate list returns a closing
candidate exactly when one is in the list (`hit`: a returned
candidate is a member and closes the gap; `miss`: when the scan
returns nothing, no member closes the gap), and the existence of
a closing candidate in the list is a decidable proposition
(`solvable`, a decision procedure, not a theorem). The list of
closing candidates is no longer than the candidate list
(`bound`).

**Premise, with closing route.** The exact comparison count of
the closing scan — one closing test per candidate, each test
costing one comparison per gap axis — is stated as a premise,
not a theorem: no counted form of the scan is proved here.
Closing route: a counted scan in the shape of the counted
evaluator proposed in section 8, item 7, proved to return the
same result as the scan with its counter bounded by the product
of the candidate count and the gap axis count. Until that lands,
any claim needing the count itself is unmeasured; the
decidability and the length bound above do not need it.

### 11.5 Updates as the graph appends

**Settled intent.** The space is semi-persistent: appends update
it incrementally, and the updated solved set equals a from-scratch
solve of the updated space. This is the incremental-covers-full
property of the standing measurement discipline, stated for the
candidate space.

**Verified.**

1. From-scratch form. The solved set of the grown space, computed
   through the epoch's weighted order, has exactly the members of
   a from-scratch solve of the grown candidate list (`fresh.solve`,
   by the search module's `weighted` statement applied to the
   grown list).
2. Incremental form, qualified append. When the appended
   candidate is qualified, the new frontier predicate is the old
   frontier filtered by the appended candidate, plus the appended
   candidate when nothing old dominates it (`grow`, and its
   solved-set form `step`). The proof transports list append to
   eligibility insertion by view extensionality and then applies
   the frontier module's insertion exactness; the side condition
   is exactly that the appended candidate is qualified.
3. Incremental form, disqualified append. When the appended
   candidate is disqualified, the solved set is unchanged
   (`grow.dead`, by view extensionality): a disqualification
   coloring is an update with an exact, empty effect on the
   solved set, proved rather than assumed.
4. Join. The solved predicate of a joined space is the frontier
   predicate over the joined membership (`join`, by the search
   module's join frontier statement through the epoch weighting).
5. Retraction. Removing an eligibility set exposes exactly the
   candidates whose every former dominator was removed (`drop`,
   the frontier module's retraction exactness stated for the
   candidate space). A coloring change that disqualifies a set
   of candidates updates by this rule and by rule 3, never by
   an unstated recomputation.

### 11.6 Standing controls for this layer

Two new controls, each a proved statement over the named demo
space (two candidates trading the two axes, a third reading zero
on both), in the style of section 9.

1. A change of epoch axes preserves the solved set: refuted
   (`epoch.shift`). Under the first axis alone the solved set is
   the first candidate; under the second axis alone it is the
   second. An epoch change that moves the axes is a change of
   measures, not a reweighting, and section 11.3 rule 2 is the
   exact boundary of what a reweighting preserves.
2. Appending a candidate never removes a solved member: refuted
   (`loss`). The third demo candidate dominates both axes, and
   appending it removes the first candidate from the solved set
   under the two-axis epoch. Semi-persistence is exactness of
   the update, never monotonicity of membership; any consumer
   that assumes solved members only accumulate is wrong by this
   control.

The controls of sections 9 remain in force for this layer: in
particular the weighting of section 7 provably moves the returned
list's order while membership stands (the search module's order
control), and filtering a former solved set is not an update
(section 9, control 5).

### 11.7 What is not claimed

No counted bound is claimed for the closing scan (section 11.4,
premise). No statement is made about candidates or gaps outside
the finite list, about readings that were not supplied, or about
the general hypergraph beyond the finite-list instance, beyond
the named premise that heads this section. The moved-set
characterization proposed in section 7 remains proposed there
and is not claimed here. The search-space bet of section 10 is
unchanged: the candidate space is the structure the bet is about,
and this layer adds no corpus evidence for or against it.
