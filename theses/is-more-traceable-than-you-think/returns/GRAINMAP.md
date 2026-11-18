# Grain map: provable returns over the lane a hypergraph

Lane b, independent check. The extractor is `extract.py` in this
directory; it is rerunnable and deterministic (two runs produced a
byte-identical `results.json`). Three code paths, kept separate:

- Extraction reads the hypergraph alone. For each entry address a
  class node carries, it offers the candidate premise sets the
  hypergraph itself contains: the full member set of the class's
  derivation link, the groups of that set by environment, and the
  groups by environment and value.
- The check loads the derivation record as oracle only. A candidate
  passes when (a) its witnesses, rendered as the record renders
  evidence — batch, source, pin, fact, joined by the record's
  separator, plus a source-digests element for each premise carrying
  digests — equal the recorded evidence as a set, and (b) the four
  parts re-derived from the candidate under section 17.3 of the
  governing spec equal the recorded parts.
- Refinement loads the step file only for entries the symbol grain
  left ambiguous or failing.

Snapshot pins, as supplied and re-verified by hash before the run:
the hypergraph at a847fb54 (first eight digits; full value in the
lane a report), the derivation record at 77576491, the step file at
57dabacc. Every verdict below is verified at this snapshot and at no
other.

## Totals

| measure | count |
|---|---|
| entries checked | 1526 |
| exact at symbol grain | 1522 |
| exact only at step grain | 4 |
| failing | 0 |

By kind: plain 1006 of 1006 exact at symbol grain; joined 180 of
180; split 190 of 190; dependence 34 of 34; contested 112 of 116 at
symbol grain and the remaining 4 at step grain.

## How the symbol grain separates

Of the 1526 uniquely determined premise sets:

- 1220 are the full member set of their class's derivation link
  (every plain entry whose class has one environment, every joined
  entry, every dependence entry, and the axis variants that ride on
  them).
- 268 are an environment-and-value group: one environment, one
  witnessed value — the contested separation, and split entries
  whose environment carries a single value.
- 38 are an environment group whose members carry more than one
  value: split entries where the separation the hypergraph offers
  is the environment alone.

Entries that differ only by axis share one premise set and one set
of derived parts; 861 distinct premise sets serve the 1526 entries,
at most 3 entries on one set. Sharing is not ambiguity: the premise
set is the same, so the return is the same.

The part rules as executed, all under section 17.3: workload is the
contract text where any premise carries one (distinct contracts
joined in sorted order), else a procedure line naming the premises'
batches in sorted order; a dependence entry takes the fixed line
naming the differing witnesses. Environment is the tier-one host
where a premise names one, else the tier-two record line naming its
batch; several environments print as the joined list in sorted
order. Uncertainty takes a recorded range first (a range counts
where it is a plain numeric span), else the witnessed spread of
minimum to maximum where the values are numeric, else agreement
over the witness count where non-numeric values agree, else it is
underivable with its reason, which is also the only underivable
part anywhere in the record (482 entries). Derived numbers print
in the record's own six-significant-digit general form; the six
largest byte counts in the store print in scientific notation in
the record, and the check reproduces that form rather than
correcting it.

## The one refinement site

One site, four entries, all in one class: project idol, fact
`execution: idol-prof battery`, class label the single pin
260b73efc47120f73d3025b2b4721f3d8f175cf3. The four entries are the
contested pair of values (26 passed, 27 passed) on two axes each:

- 244f94304cb19b5c8d3fa013815fdcf54fd0463d76bce3c5779a791d88aabd09
- 647104c2fbc501063a4a28c44bda89d8ae35a711c6b80e1d7152eb9acbc24b6c
- e33dc07eda865b26f196de641717984849870f6b06a1f093413385eec0049851
- eed8a98206e6fedb8cd340660ba24468e29fe76f57dc2ad17150b80c606c986c

What symbol grain could not separate: this class holds the store's
one repeated-observation pair — two witness nodes with a single
identity under section 17.2 (same batch, source, pin and fact),
differing in value, note and range. Both singleton premise sets
render to the same one-element evidence set, and both re-derive
the same four parts for each entry, so no unique premise set is
determined at symbol grain. The rendered evidence is the collision
point; the nodes themselves are distinct.

What step grain added: the changed list of step 13, batch
`universal execution backfill 2026-11-17` — the step that added all
four entries — names each entry by a rendering that ends in its
value. That naming binds each entry to the witness node carrying
that value, and the bound candidate passes both checks. Named
plainly: the step file's own witness list names the shared
identity only once, so the binding comes from the changed list's
value naming, not from any finer witness identity in the step
file.

Characterization: the step-grain region is not a project region
and not a fact-kind region. It is one structural feature — a
repeated witness identity inside one class, where the two
witnesses share batch, environment and every rendered field, and
the entries over them are told apart only by value. It occurs
once in this snapshot, over 2 of 2509 witness nodes.

## Failing entries

None. All 1526 entries are exact at one of the two grains; no
entry was rounded up and none was dropped from the count.
