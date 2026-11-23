# Lane a report: the historical witness hypergraph

Built from the frozen snapshot only. The builder is `build.py`; it reads
the snapshot directory named on its command line and writes
`hypergraph.json`. Nothing in the build reads the live store.

## Snapshot pins consumed

- `witnesses.json` — sha256 673ab30b1bea3bc98cd42ea68b1e1b58d3194891bb021b3f7b8949c7085e2c7e (2509 witness records, 8482 join records)
- `steps.json` — sha256 57dabacc753fa4a394fad29f43c66b54bbc96ec0021d97283c7bbd35ee597075 (15 steps)
- `accounting.json` — sha256 775764911237e96dddc2353b686c34513b3fe14d2af824573b167c364637efd8 (1526 entries)
- The accounting hash carried by `accounting.json` and by the last step
  is the same value: 5fca02f38a694a3c58d7b7cc6d78fce7ee8489a36c39cf796e4004ac2febd5a4.

## Canonical form and content addresses

One canonical encoding is used everywhere: a value is written as JSON
with keys sorted, no spaces after separators, and text unescaped except
where JSON requires it. A content address is the sha256 of that writing,
in hex. A node address is taken over its kind and its defining fields
only. A link address is taken over its kind, its premise set, its
conclusion, and its own fields. Time is never part of an address:
arrival is not identity.

The serialization is one JSON object with two keys, `nodes` and
`edges`, each a list sorted by address, written with the same canonical
encoding plus a final newline. Byte equality across runs is therefore
meaningful.

## Nodes

Every node carries its kind, its defining fields, its address as `id`,
and a `time` list (see the time section). Counts by kind:

| kind | count | defining fields |
|---|---|---|
| project | 9 | the project name |
| fact | 180 | project plus fact name |
| state | 8555 | project plus pin, after the pin rewriting below |
| witness | 2509 | the full witness record minus its batch: source, project, pin as recorded, the rewritten pin as `state`, fact, value, grade, host, contract, digests, range, note |
| batch | 15 | batch name, step index, and the step record's two hashes under their recorded names |
| venue | 10 | the host text, verbatim |
| procedure | 16 | the procedure text (an envelope part; see boundary links) |
| class | 719 | project, fact, the sorted member pins, the class label (the member pins joined by commas, exactly as the accounting prints it), and the sorted addresses of its accounting entries |
| join | 8467 | project, scope, the endpoint pair, and the recorded kind |

Total nodes: 20480.

Witness identity follows section 17.2 of the governing spec: source
locator plus project plus pin plus fact name. One identity with two
values is two witnesses. The filed feed holds 2508 identities over 2509
records: exactly one identity carries two values, and it yields two
witness nodes. No two records share identity and value while differing
in any other field, and no witness arrives in more than one batch, so
taking the whole record minus batch as the node's fields is unambiguous
on this store; that was checked by execution, not assumed.

Pin rewriting (the section 17.2 amendment) is implemented: within one
project, a pin that uniquely prefixes exactly one longest form is
rewritten to that form, and an ambiguous short form is left as
recorded. On this snapshot it fires zero times: no pin in any project
prefixes another, so every state stands as recorded. The four shortened
forms the amendment speaks of are not present in the frozen snapshot.

States by project: idol 8331, drift-sentinel 89, idol-wsp 40,
idol-lib 37, idol-sites 28, idiom 14, idol-wide 10, idol-model 4,
semi-persistent-fork 2. States attested only by join records are
included; a state is a symbol of the store whether or not a witness
stands at it.

## Links (hyperedges)

Each link is a full premise set to one conclusion. Counts by kind:

| kind | count | premises | conclusion |
|---|---|---|---|
| derivation | 719 | the class's member witness nodes | the class node |
| join | 8467 | the two endpoint state nodes | the join node |
| boundary | 170 | the envelope parts: procedure node, state node, and venue node where a venue is recorded | the witness node |

Total links: 9356. No link or node points at a missing address; that
was checked over the whole file.

Derivation links: one per class formed under section 17.4. Components
are computed over every state of the project, so connectivity flows
through states carrying no witness for the fact; the members of a class
are the component states that do carry a witness for the fact. A
transition record (kind `transition clean`, fact field the word `all`)
joins its endpoints for every fact; a gate record (kind
`gate proof-equal`) joins its endpoints for its named fact alone.
This reading was tested against the alternative that class members are
whole components: the whole-component reading reproduces the
accounting's class labels for 5 of 180 fact groups; the reading used
here reproduces them for 180 of 180. Every one of the 719 computed
classes carries at least one accounting entry, and the class nodes
between them carry the addresses of all 1526 accounting entries, each
exactly once (a class carries between 1 and 66 entries: plain, joined,
split, contested, and dependence entries all ride on their class node
this way).

Join links: the 8482 recorded join edges fold to 8467 distinct
relations (8438 transition, 29 gate). Duplicates are exact repeats of a
relation in a later batch; no relation is recorded with two kinds, and
no pair is recorded in both directions. From the hypergraph alone,
with no snapshot, the classes were re-derived using only the join
links, the state nodes, and the witness nodes: the result is the same
719 classes, label for label. The recorded join relation is therefore
recoverable from the hypergraph in everything section 17.4 uses.

Boundary links: one per witness whose fact begins `execution:` — 170
witnesses (drift-sentinel 89, idol 73, semi-persistent-fork 8). Each is
marked envelope grain in its link fields, per section 18.6: the
envelope is the coarsest lawful grain. The procedure premise is the
witness's contract where one is recorded (159 of 170) and its fact
name otherwise (11). The venue premise is absent for exactly 2 of the
170, whose records name no host; those links have two premises, the
other 168 have three.

## The fold, proved by execution

The builder folds per-record contributions into content-addressed
sets; nothing in the output depends on feed order or feed multiplicity.
Four runs, all writing the same canonical serialization:

| run | feed | file sha256 |
|---|---|---|
| plain, first | snapshot as filed | a847fb5465f743700f90b34b423444fa8441660b6854c53cd8f62aea58829ea5 |
| plain, second | snapshot as filed | a847fb5465f743700f90b34b423444fa8441660b6854c53cd8f62aea58829ea5 |
| shuffled | witnesses and join records in a fixed shuffled order | a847fb5465f743700f90b34b423444fa8441660b6854c53cd8f62aea58829ea5 |
| duplicated | every witness and join record twice | a847fb5465f743700f90b34b423444fa8441660b6854c53cd8f62aea58829ea5 |

All four outputs are byte-identical. The output file is 10855823 bytes.

## Time: what this store actually carries, and what it does not

Carried on every witness node and every link: the batch the record
arrived in and that batch's step index (0 to 14) in the compounding
order of `steps.json`. Symbol nodes (project, fact, state, venue,
procedure, join, class) carry the batches whose records attest them;
batch nodes carry their own step. Every node and every link in the
file has a non-empty time list.

What the record affords, stated plainly:

- There is no timestamp field anywhere: not on witness records, not on
  join records, not on steps, not on accounting entries. No field of
  any record is a clock reading as such.
- The batch name is the main time text. 13 of the 15 step batch names
  carry a calendar date (day resolution, no finer). Two carry none:
  `extra facts input` (step 8) and `history graph projection` (step 9).
  For records in those batches, the step index is the only time the
  store affords, and that is all the hypergraph claims for them.
- The step index is the only store-wide ordering. Within a batch, no
  order among records is recorded; the fold treats a batch as a set,
  and feed order is not time.
- One project uses time as its state identity: all 89 drift-sentinel
  pins are minute-resolution time texts in the form
  `2026-11-09 19:32`. Those pins are carried verbatim as state symbols,
  and the accounting's class labels for that project are those same
  texts.
- The finest clock text in the store sits inside one witness's range
  field: a second-resolution interval in ISO form,
  `2026-11-17T13:26:53Z to 13:33:08Z`, as part of a wall-time range.
  Three range fields in total carry wall-time text. Ranges otherwise
  carry numeric spreads (56 records carry a range at all).
- Time text also rides inside prose fields, carried verbatim: 75
  witness notes carry a date, 313 witness sources carry a date, and 1
  contract carries a date. None of it is parsed into a separate time
  field; the hypergraph carries what is recorded, where it is
  recorded, and synthesizes nothing.
- Wall time for executions is mostly absent: of the 170 execution
  witnesses, only the few range texts above carry any duration. The
  store does not record when, within a day, a batch ran, nor how long
  any step took.

## Judgment calls, named as such

1. Join endpoints are stored as a sorted pair, so the recorded
   direction of a join record (which endpoint stood in its `from`
   field) is not carried. Section 17.4's relation is symmetric —
   an edge connects its endpoints — and direction carries no class
   information. Connectivity, kind, scope, project, and recording
   batches are all carried, and class re-derivation from the
   hypergraph alone is exact.
2. Accounting entries are not minted as nodes; the task's node list
   does not include them. A class node carries the content addresses
   of its entries, so every entry is reachable and checkable from the
   hypergraph, and the derivation link's conclusion is the class.
3. The envelope-grain mark is derived from the fact form (a fact
   beginning `execution:`), because the store's own records carry no
   grain field. The mark states the grain the spec assigns to such
   witnesses; it is not a field the records themselves assert.
4. The procedure premise falls back to the fact name where a witness
   records no contract, following the task's own rule (procedure from
   its contract or fact name). This fires 11 times.
5. Steps are represented by their batch name, index, and two hashes.
   A step's own witness list and changed list are not re-encoded as
   nodes or links: they are the fold's bookkeeping, and their content
   is recoverable from the witness nodes and their batch times.
6. Dependence entries (34, the per-venue difference signal of section
   17.6) get no link kind of their own. They are entries of a class,
   derived from that class's witnesses across venues, and their
   addresses ride on the class node with the other entries.

## What did not hold

Nothing in the task's premises failed. Two expectations worth naming:
the pin-rewriting amendment fires zero times on this snapshot (the
shortened forms it governs are absent), and the store carries no
timestamp field, so exact time at symbol grain is batch-plus-index
plus whatever time text the records themselves carry — no finer claim
is made anywhere in the file.
