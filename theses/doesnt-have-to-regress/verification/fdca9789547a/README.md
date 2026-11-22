# Exact-pin verification: incremental dynamic non-regression

Source commit: `fdca9789547ad62536ab71d7689d99dc7754a116`
Source tree: `9508544f033bb3ac3fc5d077e10ae9532c0662c5`

The default branch was fast-forwarded to that exact source commit after both complete gate runs passed. This evidence-only descendant adds verification records; it is not a replacement source pin.

## Independent and publisher checks

Both complete receipts agree byte for byte (SHA-256 `cf95873cec50bfc4b79158c399c0fdd67cdbd06c25e00df32a97600dc820d832`):

- 27 Lean files compiled with warnings as errors.
- 916 proposition-valued declarations audited, including generated logical declarations. The source contains 385 explicitly named theorems, up from 203 at the previous landed pin.
- Zero custom proof axioms and zero authored source proof escapes.
- Standard foundations are separately allowed: propext, Classical.choice and Quot.sound.
- 2,025 compiler-generated nonlogical unsafe runtime declarations separately inventoried; these are not custom proof axioms or authored escapes.
- All existing gate controls pass, plus 44 dynamic executable cases.

The independent agent fetched all 70 source blobs at the immutable remote commit, verified every Git blob, size, mode and all 11 tree objects, reconstructed the original commit object, and rebuilt from source-only pinned dependency checkouts with no copied compiled outputs. It repeated the source/dependency hash checks after the gate and confirmed a clean exact HEAD. It also independently challenged the multiple-executable audit partition with four additional controls.

Read [independent-summary-fdca978.json](independent-summary-fdca978.json), [independent-receipt-fdca978.json](independent-receipt-fdca978.json), [independent-source-fdca978.json](independent-source-fdca978.json), and [independent-partition-fdca978.json](independent-partition-fdca978.json). The full independent logs are in [independent-full-logs-fdca978.txt.gz](independent-full-logs-fdca978.txt.gz). Publisher records are [publisher-receipt.json](publisher-receipt.json), [publisher-gate.log](publisher-gate.log), and [publisher-logs.json.gz](publisher-logs.json.gz).

The runtime cases cover cold/warm/cost-only proof work, negative-evidence reuse, dynamic archive reconsideration, promises, actual recorded inverses, refusal of regressing rollback, exact replay, conflicting event IDs, complete context reobservation, and malformed or incomplete model inputs. See the source's `Dynamic/REVIEW.md` and `DYNAMIC.md` for claims, counterexamples and application premises.

## Hosted CI status remains open

[hosted-ci-status.json](hosted-ci-status.json) records a final-pin hosted Actions job that failed before any runner was assigned or any step executed. Earlier candidate execution also failed before runner assignment on two attempts; the job log endpoint returned 404. The available evidence does not identify the underlying cause. No hosted CI pass is claimed.

The workflow explicitly requires `FAMILY_READ_TOKEN` with read access to the private composable prerequisite. Runner availability, that credential, required branch checks and actual deployment correspondence remain operational prerequisites. The verified local and independent gates are real completed checks; a workflow that never ran is not substituted for them.

## Recovery and evidence identity

A workspace reset occurred before the candidate source was initially published. The recovered staged source tree exactly matched its pre-reset Git tree. All final evidence above was regenerated after recovery at the final immutable pin. A subsequent clean build exposed missing Lake roots for two Audit modules; the final source fixes those declarations. Pre-reset working-tree receipts and failed intermediate candidates are not closure evidence.

[manifest.json](manifest.json) gives byte sizes and SHA-256 digests for the attached verification artifacts.
