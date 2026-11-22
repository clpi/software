# Verification

The authoritative command is `./check.sh`, run with the exact `lean-toolchain`
version. It discovers every Lean file and writes
`.lake/all-files-gate/receipt.json`. The receipt binds all proof sources and
gate inputs by SHA-256, records the dependency commits and Lean binary hash,
and distinguishes a clean committed run from a dirty development run.

The independent mathematical counterexample review is in
`independent-interaction-review.md`. It compiled all 24 controls individually
with warnings as errors and confirmed that each uses no axioms. Its final
source hashes are:

```
c531fa1f7749cbc7616c73c8b4ee79b5a8e2727f6f05a12582faa841e6809b06  SoftwareIsComposable/Interaction.lean
f83d4fc80cb3126d36d65b3f7b3813054da9787cbb0817290fb897e816cd768b  Audit/InteractionControls.lean
```

The legacy source is an exact namespace-only relocation. Replacing its opening
and closing `SoftwareIsComposable.Legacy` namespace with `SoftwareIsComposable`
recovers original Git blob `251c0824e8bc48a82bc69a640cbd54d7aff86f63`, SHA-256
`faf5b73b4348471db420b367b87f9f7cca3bc23e03287cb30d5e2b2137952a83`, from
incrementally-safe `de1b30716e2b758141d5940056f37cd678464032`.

An immutable commit is not considered independently checked until a second
reviewer has exported that commit into a fresh checkout, rebuilt the pinned
dependencies, run the entire gate, and compared the source/input hashes.
The resulting execution receipt is recorded here after that source freeze.
The historical root `CHECK.log` remains explicitly historical.

Concurrent main `7a408c7b752df6f47b9cf60ddbd89d4001b5e22a` was integrated before
the final source freeze. Its two added proof modules were independently read.
The independent checker added eight further standing controls in
`Audit/OneShotBoundary.lean`, SHA-256
`9f97d1b63befb3932824715693912868f502d256c95bccd1a8db72af114f07e8`, to distinguish
nullary and nonrecursive finite evaluation from seeded recursive closure.
They compile with warnings as errors and no custom axioms; five use standard
`propext` / `Quot.sound`, while three need no axioms. Thus the combined 32
independent controls are kernel checked; the original 24 are individually
axiom-free.

No hosted CI result is asserted by this document. The check runs and receipts
are local kernel executions with the pinned Lean toolchain. The executable
CSV harness is exercised for its existing contract; it is not an interaction
safety checker.
