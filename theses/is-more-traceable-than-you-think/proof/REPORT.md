# Traceability — platform independence of the witness hypergraph fold

Lane C deliverable for the repository named in the brief as
software-is-more-traceable-than-you-think. Lean 4.19.0, no
Mathlib, no external packages. Toolchain pin in `lean-toolchain`:
`leanprover/lean4:v4.19.0`.

## Re-run, cold

    LEAN=/path/to/lean ./check.sh        # writes CHECK.log, exit 0
    LEAN=/path/to/lean python3 platform-audit.py   # writes PLATFORM-AUDIT.log

No state outside this tree is used. The gate compiles every
`.lean` file found recursively in the tree, importers after the
modules they import.

## The model

- A derivation is a premise characteristic function over nodes
  together with a head node, so a hyperedge carries its full
  premise set.
- A hypergraph is a pair of characteristic functions: which
  nodes are present, which derivations are present.
- The fold of an event stream (a list) is the pointwise join,
  on both faces, of the contributions of the stream's events.
- A timed event is an underlying event together with a time
  component from an arbitrary time type. The timed fold is
  defined through the underlying events' contributions only;
  the time components are carried and never read.

What the model takes as given is exactly one thing: the
contribution assignment, an arbitrary function from events to
hypergraphs. That arbitrariness is the independence. Every
theorem is quantified over arbitrary node, event and time
types and over every such assignment, so the theorems hold
for every way events can be sensed and lifted into the
representation, and no hypothesis names a particular
environment, language, program or mechanism. No decidable
equality is assumed anywhere: the construction does not need
it, because contributions arrive as whole hypergraphs and
presence is an existential over the stream. That is stronger
than the brief's sketch, which allowed decidable equality
where needed; it turned out to be needed nowhere.

## Theorems, in plain words

Main module `Traceability.lean` (theorem names in the family
style of the template repositories):

1. `fold_nodes` and `fold_edges` — provable returns. A node,
   respectively a derivation, is present in the folded
   hypergraph if and only if at least one event in the stream
   contributes it. The premise set of every witnessed
   conclusion is read off the hypergraph exactly as recorded:
   nothing added, nothing lost.
2. `returns_head` — a derivation that a named event of the
   stream contributes is present in the folded hypergraph.
   An earlier form also assumed the derivation's head is a
   witnessed node of the fold; that hypothesis was never read
   by its proof term, and it is removed. The Controls module
   pins both directions of the head's independence on concrete
   data: `separation` (a witnessed head with no contribution
   does not return) and `unwitnessed` (a contribution returns
   with no witnessed head).
3. `fold_ext` — order and duplication independence. Two
   streams with the same membership have equal folds; the
   fold is a function of the set of events alone.
   Corollaries: `fold_perm` (reordering changes nothing) and
   `fold_append_self` (presenting every event twice changes
   nothing). Supporting laws: `join_assoc`, `join_comm`,
   `join_idem`, the two empty-join identities, `fold_append`
   (the fold splits over appends), `graph_ext`,
   `bool_eq_of_agree`.
4. `foldtimed_ext` — time independence, membership form. Two
   timed streams whose underlying events have the same
   membership have equal folds, whatever their time
   components are. `foldtimed_retime`, with its lemma
   `map_event` — time independence, reassignment form:
   reassigning every time component of a stream, keeping the
   underlying events in place, leaves the folded hypergraph
   unchanged.
5. `retract_nodes` and `retract_edges` — retraction
   exactness, membership form. After filtering a stream to a
   surviving subcollection, a node, respectively a
   derivation, is present in the filtered fold if and only if
   some surviving event of the original stream contributes
   it. `retract_eq` — retraction exactness, recomputation
   form: folding the filtered stream yields exactly the
   hypergraph of any stream presenting exactly the survivors.
   Observables after retraction equal recomputation from the
   survivors.

Nothing was weakened. Every statement from the brief is
proved at the stated strength.

## Adversarial controls

Module `Controls.lean`, checked by the same gate, kept as
regression fixtures. Each control defines a weakened variant
of the construction and proves, on concrete data checked by
the kernel, that the corresponding claim fails for it.

1. Counting fold — attacks duplication independence (part of
   theorem group 1 in the brief's numbering: order and time
   independence). Weakening: the join adds per-node counts
   instead of taking the union, dropping idempotence.
   Failure exhibited: `count_once` and `count_twice` compute
   the counting fold of a single presentation as 1 and of the
   doubled presentation as 2 at the same node, and
   `count_claim_fails` proves the negation of the claim that
   doubling a stream changes nothing.
2. First fold — attacks order independence. Weakening: the
   fold keeps only the first event's contribution, reading
   arrival order. Failure exhibited: the streams written
   [0, 1] and [1, 0] present the same set (`swap_same_set`),
   and `first_claim_fails` proves the negation of the claim
   that same-membership streams fold equally, by evaluating
   both folds at node 0.
3. Coarse grain — attacks provable returns. Weakening:
   presence is read at head grain, so two derivations that
   share a head are merged and the premise set is not read
   off. The two concrete derivations share head 1 and differ
   in premises (`prem_differ`). Failure exhibited:
   `grain_absent` proves the second derivation is exactly
   absent from the folded hypergraph, `grain_coarse_present`
   proves it reads as present at head grain, and
   `grain_claim_fails` proves the negation of the claim that
   head-grain presence gives exact presence. The premise set
   read off at the coarse grain is wrong for that derivation.
4. Residue fold — attacks retraction exactness. Weakening:
   the retracted fold's node face keeps the nodes of the
   full, unretracted fold joined in, so retracted events
   leave residue. Failure exhibited:
   `residue_survivor_absent` proves node 0 is absent from the
   survivors' fold, `residue_present` proves it is present in
   the residue fold, and `residue_claim_fails` proves the two
   folds are unequal, the negation of the exactness claim for
   the variant.

## Axiom audit

Every main and control theorem carries a `#print axioms`
line, printed into `CHECK.log`. The gate itself enforces the
subset, not just prints it: it extracts every printed axiom
and fails unless each lies in {propext, Classical.choice,
Quot.sound}. Result on the final sources: gate exit 0, the
subset check passed, and the printed set is exactly
{propext, Quot.sound} — Classical.choice is allowed but not
used, and no other axiom appears. Three control theorems
depend on no axioms at all.

## Platform audit, mechanical

`platform-audit.py` enumerates every definition and theorem
in both modules (48 statements), asks the Lean kernel checker
to print each statement's type with all parameters and
hypotheses, and scans that printed list against a fixed word
list. Output in `PLATFORM-AUDIT.log`; the scan is rerunnable
and exits nonzero on any hit.

- Word list, 52 words: linux, windows, macos, darwin,
  freebsd, openbsd, unix, posix, kernel, syscalls and its
  singular, operating, idol, zig, python, rust, java,
  javascript, typescript, haskell, ocaml, golang, swift,
  kotlin, scala, perl, ruby, lua, cpu, gpu, x86, arm64,
  socket and its plural, thread and its plural, process and
  its plural, pid, driver and its plural, hardware, bytecode,
  compiler, interpreter, shell, disk, heap, pointer, binary,
  executable, machine.
- Hits over the 48 printed statements: 0. Audit result: PASS.
- Parameters and hypotheses, as printed: the main theorems
  quantify over node, event and time types, one contribution
  assignment, streams, a survival test and membership
  hypotheses — nothing else.
- Literal source search, for completeness: the same word
  list searched over both source files gives zero hits,
  except the word "kernel" in three comments, each meaning
  the Lean proof kernel that checks the proofs, not an
  operating-system kernel; that word is in the list and the
  printed-statement scan, which is the audit of record, has
  zero hits for it.

## Gate

`check.sh` covers every `.lean` file in the tree recursively
with no skipped subfolders. The escape scan covers the
tokens: sorry, admit, axiom, native_decide, implemented_by,
extern, unsafe, opaque, partial. Compilation uses warnings
as errors. Final run: exit 0, output in `CHECK.log`.

## Relation to the sibling repositories

- The Fold module of software-is-quantifiable already proves
  the fold of a plain accounting: the accounting as the
  characteristic function of the recorded witness set, its
  join pointwise, with its own extensionality and permutation
  theorems. That result is about a single characteristic
  function over witness identities. This module does not
  re-prove it. What this adds is the level the accounting
  sits on: hypergraphs (two characteristic functions, nodes
  and full-premise derivations), an arbitrary contribution
  assignment in place of the single-witness accounting,
  timed streams with time independence, the exact read-off
  of derivations, and retraction exactness — all quantified
  over arbitrary environments.
- The HypergraphIncremental module of software-optimality
  already proves that incremental recomputation over a
  derivation hypergraph equals full recomputation of the new
  snapshot, with its affected-region and frontier results.
  This module does not redo it. What this adds is the
  witness-stream level below it: the folded historical
  witness hypergraph as a function of the boundary-event
  set, provenance read off it exactly, retraction as
  recomputation from the survivors, and independence of the
  fold from order, duplication and time, for every
  contribution assignment.

## Files

- `Traceability.lean` — the proof module.
- `Controls.lean` — the adversarial controls.
- `check.sh` — the gate; `CHECK.log` — its output, exit 0.
- `platform-audit.py` — the mechanical audit;
  `PLATFORM-AUDIT.log` — its output, PASS, 0 hits.
- `lean-toolchain` — the toolchain pin.
