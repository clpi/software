# Cumulative incremental hypergraph computation and proof: a duet

## Voice One — Delivered result and exact revision boundary

This revision supplies an executable append-only dependency hypergraph spanning source recomputation, linked compilation, symbolic certificates, independent certificate checks, compiled execution, and actual Lean value proofs. New versions append history. Current-head transactions select active versions; prior tasks, artifacts, and proofs remain available for reuse. Complete ordered prerequisite lists make these multi-input hyperedges, including repeated argument positions.

The delivered compiler is a finite pure exact-integer reference pipeline with `const`, named `input`, `add`, `mul`, and `neg`. Python generates actual instruction blocks and execution records. Lean independently checks those blocks and recorded values. Production Idol/Duo integration and a source-level proof of the whole Python implementation remain separate obligations.

The baseline is [2d35b503aa74b2ac2397d9cc6af0c4049c609b4e](https://github.com/clpi/software-is-more-traceable-than-you-think/tree/2d35b503aa74b2ac2397d9cc6af0c4049c609b4e). It removed the dominated `returns_head` inherited from `8f6a128069d0e68e97c4a69d78689c84350b0d2f`. The [original duet](REPORT.md), its standing counterexamples, and its explicitly weaker unrestricted replacement remain in force. This extension does not restore a premise equivalent to the desired conclusion.

This report's claims attach to the commit containing it; the accompanying delivery identifies that immutable release pin. [SOURCE-SHA256.txt](SOURCE-SHA256.txt) binds proof sources, runtime, gates, and generated fixtures. [CHECK.log](CHECK.log) is the repository-wide theorem/axiom census. The [campaign receipt](receipts/incremental-campaign.json), [named tests](receipts/incremental-tests.log), and [gate transcript](receipts/incremental-gate.log) record fresh execution at these source hashes. A workspace restart interrupted integration; reconstructed sources received fresh checks rather than inheriting the earlier run's evidence.

## Voice One — One exact identity and one append-only history

The cache identity is `stage + exact payload + ordered prerequisite IDs + complete scope`. Scope includes contract/target, implementation fingerprints, checker and runtime identities, and environmental/effect declarations. Actual input values are explicit payloads of stages whose results depend on them. Mandatory implementation fingerprints are refreshed independently of caller-supplied labels. Hashes choose index buckets; exact canonical descriptor bytes determine equality.

Every task refers to earlier interned tasks. Publication requires every prerequisite result. A task that uses one child twice still receives two argument positions, while sharing that child's computation. The journal appends task definitions, successful results, and source/head transactions. Revert can reuse an older result while appending a new current-head transaction. Successful publication is unique per full key; failed attempts or computations lost before durable publication may repeat.

| Stage | Work and dependency boundary |
|---|---|
| Recompute | Interpret a source operation from all child values and captured inputs. |
| Compile | Emit a local stack block with ordered references to child artifacts. |
| Certificate | Record a local symbolic stack trace and parent certificate references. |
| Check | Independently verify the trace, source operation, emitted code, and every parent receipt. |
| Execute | Run the local code using all child execution values and its matching check. |
| Factor | Represent independent Cartesian choices through checked alternatives; no tuple enumeration. |

Source edits use reverse-dependency indices and overlay maps. A hot value edit visits its affected cone and skips topology validation when argument lists are unchanged. A test replaces active tables with dictionaries that reject whole-table iteration: the hot edit and delta export still succeed. Restart explicitly reconstructs indices by replay; its cost is reported separately.

## Voice One — Validity and reuse are derived from transitions

[Incremental.lean](Incremental.lean) defines the actual abstract transition. A hit retains the cache. A miss resolves all prerequisites, computes the local operation, and appends a row. An unresolved prerequisite refuses the transition.

`run_valid` derives `ValidLog` from execution starting at the empty log. `reuse_agrees_with_fresh` derives equality between a retained hit and fresh local evaluation of its immutable prerequisites. The caller never supplies warm/cold equality. `run_cold_exact` proves equality to a separate cold traversal with no cache-hit branch. `run_append` proves that partitioned requests agree with their concatenation.

Prefix preservation, unique-key, per-key work, and cumulative stage-count theorems account for retained history. `valid_backward`, `dependency_rank`, and `no_self_support` derive strict dependency ranks from accepted construction. `cumulative_contract` lifts a separately established local all-input invariant across the operational history. It does not assume that history already satisfies the conclusion.

Interned task IDs and completed-row indices differ when work finishes out of order. [Projection.lean](Projection.lean) formalizes their translation: `resolve_remap` preserves order, multiplicity, and values; `remapped_keys_reflect_equality` prevents aliasing; `complete_publishes_result` derives the result from original dependencies; and `projected_cold_exact` proves cold replay equality for successful publication histories. Controls complete later task IDs before a pending smaller ID.

[Provenance.lean](Provenance.lean) connects operational completion to the original fold and executable contributor search. The original `Derivation` uses a characteristic premise set. Its audit view therefore encodes distinct positional occurrences relative to the immutable task table, preserving original IDs and repeated positions without equating this set graph with the computation graph. No reachability equivalence between their encodings is claimed. Accepted publication derives membership and the recorded contribution; a conclusion-restating contribution premise is absent.

## Voice One — Real incremental compilation and reproof

[Pipeline.lean](Pipeline.lean) specifies source operations, actual instructions, stack execution, and linked-row checking. The checker verifies exact emitted code, arity, and prior-row bounds. `checked_program_correct` proves successful source and target evaluation with the same complete result list for every input environment. Equality cannot hide two failures.

```lean
theorem certify_extension {before after : List Row} {count : Nat}
    (prior : check 0 before = true) (length : before.length = count)
    (delta : check count after = true) :
    check 0 (before ++ after) = true
```

The driver proves `delta` by kernel computation over actual new compiler rows. It imports the predecessor's certificate and length theorem. It does not decide the whole historical prefix again. Since compiler correctness is universal over input values, changing only those values adds no compiler proof rows.

Actual values require their own proofs. [Evaluation.lean](Evaluation.lean) defines a linked captured-input tree with actual local code. Its exact statement is:

```lean
def Correct (tree : Tree) (result : Int) : Prop :=
  source tree = result ∧ target tree = some result
```

Each constructor consumes all parent correctness proofs, checks its own code, and proves its local arithmetic. Generated `value_N_correct` theorems reference earlier tree and proof constants. A value edit reuses unaffected value proofs and reproves its changed execution cone. It retains the universal compiler proof.

[The kernel driver](../incremental/lean.py) checks completion prefixes, original task IDs, projected indices, ordered parent proofs, scope, code, and observed-value associations. Accepted proof modules and receipt records are append-only. On restart it verifies source/toolchain identity, retained artifact hashes, delta counts, mappings, chains, and exact proof-source regeneration. These are integrity checks within a single-writer local trust boundary, not authentication of arbitrary external records.

The [committed receipt modules](../examples/incremental/receipts/) come from the actual depth-20 campaign. The example gate regenerates all five source modules byte for byte in a fresh directory. The repository gate independently compiles and audits the committed modules too.

## Voice One — Exponential sharing and combinatorial composition

[Sharing.diamond_compression](Sharing.lean) uses the same evaluator for a shared dependency DAG and full call-tree unfolding. Each layer consumes the previous value in two ordered positions. At depth `n`, both return the same value, while the specified invocation counts are `n+1` and `2^(n+1)-1`. At depth 20 that is 21 versus 2,097,151. The expanded-tree count is proved; the demo does not allocate or execute that tree. The result counts stage invocations, not total hashing, integer arithmetic, proof normalization, or I/O.

[Families.lean](Families.lean) models a component as actual checked compiler rows plus a valid output-row index. `every_selection_correct` proves successful equal source/target output tuples for every selection of independent alternatives. `binary_component_family_correct` reuses two checked component proofs across all selections at `n` coordinates, for every environment.

`assignment_count_exact` proves the product-of-factor-lengths law. `binary_compact_distinct` proves that `2n` references describe `2^n` distinct Boolean selectors. Distinct selectors need not produce distinct outputs for arbitrary components. [IndependentComponents.lean](../examples/incremental/IndependentComponents.lean) instantiates the semantic theorem with the constant-zero and constant-one blocks used by the runtime example.

The depth-20 factor example has 20 factor records, 40 alternative references, two checked component artifacts, and 1,048,576 represented tuples. It materializes zero tuples. Cross-coordinate constraints and side effects are outside the independent-product theorem.

## Voice One — Measured cumulative campaign

Every revision is compared with a separately executed fresh engine and fresh Lean session. The source graph has the 21-node diamond and a separate two-node branch. [The full receipt](receipts/incremental-campaign.json) includes values, timings, counters, kernel outputs, and restart costs.

| Revision | Recompute | Compile | Certificate | Check | Execute | New compiler rows proved | New values proved | New receipt modules |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| Initial cold run | 23 | 23 | 23 | 23 | 23 | 23 | 23 | 1 |
| Warm repeat | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| Input edit | 21 | 0 | 0 | 0 | 21 | 0 | 21 | 1 |
| Structural edit | 11 | 11 | 11 | 11 | 11 | 11 | 11 | 1 |
| Revert | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| Runtime/proof restart | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| Scope change | 23 | 23 | 23 | 23 | 23 | 23 | 23 | 1 |
| **Cumulative incremental** | **78** | **57** | **57** | **57** | **78** | **57** | **78** | **4** |
| **Seven actual cold rebuilds** | **161** | **161** | **161** | **161** | **161** | **161** | **161** | **7** |

The input edit changes the main value from 2,097,152 to 3,145,728. Changing a middle addition to negation yields −1,572,864. Revert restores 2,097,152. The independent branch stays −7. Scope change requalifies current artifacts while retaining old versions.

The main incremental campaign starts eight Lean processes: four fixed/bootstrap compilations once plus four receipt compilations. Restart reuses retained proofs with no new Lean process. Seven fresh cold sessions each compile four bootstrap modules and one receipt: 35 processes total. The recorded seven cold receipt processes exclude their 28 bootstrap compilations and must not be compared to eight as total-process counts.

## Voice Two — A1: Hash equality could substitute for component identity

Force every digest to collide while submitting different descriptors.

**Voice One — Answer, resolved:** Exact canonical bytes decide equality inside a bucket. The forced-collision control passes; the formal model uses exact key equality. Completion hashes bind journal bytes but do not define logical task equality.

## Voice Two — A2: An AND premise, argument order, or repeated position could disappear

Drop one prerequisite, reverse two inputs, or change `[x,x]` into `[x]`.

**Voice One — Answer, resolved:** Core resolution, runtime publication, symbolic checking, projected indices, and value proof constructors retain the complete ordered list. Lean controls prove missing-premise refusal and order/multiplicity behavior. A deliberately rehashed missing-premise artifact reaches Lean and fails its arity check.

## Voice Two — A3: Raw IDs could be confused with completion positions

Intern an unused early task, complete later tasks first, then complete the smaller ID.

**Voice One — Answer, resolved:** `Projection.resolve_remap` and `projected_cold_exact` establish the translation. Standing Lean/Python controls exercise exactly this order. The driver checks original task associations for each new suffix.

## Voice Two — A4: A callback could mutate a retained child's metadata

The first runtime copied child values but exposed nested task metadata by reference.

**Voice One — Answer, resolved:** Callback contexts now detach nested metadata and values. The regression that first exposed the bug passes. Deliberate privileged mutation of engine internals remains outside the pure-runner contract.

## Voice Two — A5: An old proof could be mislabeled current after a toolchain change

The first restart path restored active artifacts even when the requested scope had changed.

**Voice One — Answer, resolved:** Reopen and scope changes replan current artifacts. Mandatory actual implementation fingerprints survive label overrides. Pending historical tasks cannot execute under another scope; the driver rejects current observations with a different artifact scope. Historical results remain available as historical records.

## Voice Two — A6: Source/target equality could be two failures

An equality theorem alone would be weak if both evaluators returned no result.

**Voice One — Answer, resolved:** `checked_program_correct` derives a successful result and exact result-list length from checked arity and backward bounds. Component checking additionally validates the output index.

## Voice Two — A7: Matching fabricated observations could masquerade as value proofs

The first kernel bridge proved compiler correspondence but did not mention actual output numbers. Both Python observations could be changed to 999 together.

**Voice One — Answer, resolved:** Actual values now have separate linked `Evaluation.Correct` proofs. A simple forged observation fails association checking. A stronger attack changes the execution value and both observations, then recomputes its completion chain: it reaches Lean and fails the local arithmetic proof. `correct_unique_value` forbids two different accepted values for one captured tree. This attack changed the implementation and proof, not merely their description.

## Voice Two — A8: Rehashed metadata could invent a longer proven prefix

The first restore path accepted receipt counts after checking hashes. Changing the end count to 999 and rehashing could misstate the theorem's extent.

**Voice One — Answer, resolved:** Restore now verifies counts, consecutive IDs, unique task associations, both completion chains, parent mappings, axiom metadata, and exact regenerated proof source. Rehashed count inflation, changed imported objects, changed fixed proof source, and divergent prefixes are rejected. Coherent hostile replacement of all local trust material is not authenticated by this design.

## Voice Two — A9: Correct captures need not describe one global environment

Capture input `x` as 1 in one child and 2 in another. Both can be locally correct and their sum can be 3, although no single environment agrees with both leaves.

**Voice One — Answer, standing limitation `GLOBAL_INPUT_AGREEMENT`:** [EvaluationControls.lean](EvaluationControls.lean) proves this counterexample and proves no global environment agrees. The unconditional statement is explicitly named **WEAKER-CAPTURED-TRACE**: source and actual code agree successfully for the recorded captured-input tree. `Evaluation.agrees_correct` gives the stronger environmental statement only with the separate `Agrees` obligation. The source manager's binding behavior is tested; external capture truth and global agreement are not silently inferred.

## Voice Two — A10: Distinct exponential outputs still require distinct output work

Sharing cannot make materialization of every distinct tuple linear in the number of factors. Separate component qualifications do not establish arbitrary interactions either.

**Voice One — Answer, resolved by exact scope and a standing control:** The distinct-output test materializes distinct tasks and counts each. The exponential sharing theorem compares repeated unfolding with shared evaluation. The family theorem describes independent choices and universal correctness without enumeration. It claims neither free output materialization nor correctness of unmodeled cross-component interactions.

## Voice Two — A11: Successful row counts could hide real work

Hashing, serialization, integer bit complexity, Lean imports, normalization, retries, or crashes can consume work without adding a retained result.

**Voice One — Answer, named open obligation `TOTAL_COST`:** Successful publications, attempts/failures, dependency visits, source-management visits, proof modules, restart replay, and elapsed time are reported separately. The formal cost model counts evaluator invocations. No constant-time lookup, global linear wall-time, universally optimal invalidation, or exactly-once execution across crashes is proved.

## Voice Two — A12: A model theorem could be advertised as verification of all Python or production software

The generic engine accepts arbitrary callbacks. The reference language is finite. The repository also contains a separate frozen witness-data builder.

**Voice One — Answer, named boundaries `GENERIC_RUNNER_CONTRACT`, `PYTHON_REFINEMENT`, `SOURCE_FIDELITY`, `LOCAL_TRUST_AND_CRASHES`, and `PRODUCTION_INTEGRATION`:** Generic reuse requires fixed pure semantics and every semantic dependency in the key. Projection proves the abstract representation relation; actual generated artifacts and values are kernel-checked; runtime behavior is tested against fresh cold execution. No complete Python-refinement or sensing theorem is asserted. Local storage, one writer, and the Lean installation remain trusted. The original frozen `hypergraph/build.py` and `returns` pipeline are not converted here. Globally ambiguous short-pin normalization needs versioned views before an incremental conversion can preserve its meaning.

## Voice One — Proves at this revision

1. The original contribution-premise defect remains removed, with the exact weaker general theorem and original counterexamples visible.
2. Operational construction derives all-premise validity, stable history, exact local reuse, canonical cold replay equality, and cumulative batch composition.
3. Complete exact keys prevent incompatible reuse; the model retains at most one successful publication per key.
4. Backward ranks prevent self-supporting cycles, and completion-order projection preserves original complete dependencies and computed values.
5. Checked actual linked code successfully preserves exact-integer source semantics for every environment.
6. Each emitted actual-value proof establishes its captured source value and successful execution of the real local code, using all parent proofs.
7. New compiler/value data is proved through extensions and references to previous theorem constants; the campaign exercises edits, revert, scope changes, and runtime/proof restart.
8. The shared-diamond model proves equal values with `n+1` versus `2^(n+1)-1` stage invocations.
9. Independent checked components compose for every selection; binary factors represent `2^n` distinct selectors with `2n` references.
10. Every repository Lean file, including controls and generated fixtures, is freshly compiled with warnings as errors and audited against exactly `{propext, Quot.sound}`.

## Voice One — Cannot say at this revision

- That arbitrary witnesses are complete, truthful, or causally sufficient; or that any witnessed head under any lifting must have a derivation.
- That contradictory captures describe one global environment. The standing counterexample defeats that claim; **WEAKER-CAPTURED-TRACE** is the unconditional result.
- That every Python operation, callback, persisted value, parser, or source/export association is formally refined by Lean.
- That independent components establish arbitrary interacting/effectful compositions, cyclic fixed-point semantics, or linear materialization of exponentially many distinct outputs.
- That row counts prove constant-time lookup, linear proof normalization, total linear runtime, or universal exponential wall-time speedup.
- That a new scope label proves an arbitrary new contract. Concrete semantics remains the specified exact-integer operation set.
- That the journal is authenticated, multi-writer, distributed, or crash-atomic across every file and receipt append. Truncated history is refused; unfinished work can repeat.
- That restart and kernel import read no old metadata. Those costs are explicit even when old source and proof terms are reused.
- That the frozen witness builder, arbitrary software, or production Idol/Duo has been converted to this reference pipeline.

## Voice One — Reproduction

```sh
export LEAN=/absolute/path/to/lean
sh proof/check.sh
sh examples/check.sh
sh examples/range-ledger/check.sh
sh examples/incremental/check.sh
python3 proof/platform-audit.py
```

Lean 4.19.0 is pinned. `examples/check.sh` runs both nested example gates. The incremental gate requires all 38 named Python tests with no skips, executes the depth-20 Lean campaign plus seven actual cold comparisons, verifies exact counts, and regenerates all five retained proof modules. `INCREMENTAL_RECEIPTS_DIR` redirects measured receipts when rechecking a published pin. Full transcripts are retained under [receipts](receipts/).

The original wrong-middle-bridge mutation must still fail. New semantic attacks deliberately rehash modified streams where necessary, so wrong code, missing premises, and fabricated values reach Lean rather than stopping at checksum verification. The supplementary platform-word scan is lexical evidence, not a theorem about physical executions.
