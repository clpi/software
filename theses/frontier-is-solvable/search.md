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
