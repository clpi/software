# Exact-commit verification

These receipts verify source commit `f07f8e7595eb70afe84a40403f54481dfc22f6cc`, tree `9108e2e6fd7ed5787b1253dbd124d16d8ca5cf26`. The default branch was advanced to that exact checked commit. This evidence commit adds records without changing the checked source pin.

The publisher and an independent checker both ran the source commit's unmodified `./check.sh`: 17 repository Lean files, 203 named theorems, 427 proposition-valued declarations, zero custom proof axioms or prohibited authored source escapes; all refusal controls passed. Standard Lean foundational axioms and 940 compiler-generated nonlogical runtime declarations are reported separately. The independent checker retrieved all 42 source blobs and both dependency trees from GitHub, verified hashes/modes, and rebuilt without copied compiled artifacts. Both worktrees were clean and both receipts' source and gate hashes match.

`receipt.json` is the independent gate receipt; `independent-summary.json` records the independent reconstruction. `complete-command-logs.txt.gz` contains all 49 command logs as a gzip-compressed UTF-8 transcript. `publisher-receipt.json` and `publisher-check.log` record the other exact-pin run. The model scope and explicit application premises remain those in the source commit's `AUDIT.md` and `Audit/REVIEW.md`.
