# rwlog Performance Investigations

This document is a backlog of architecture-level performance investigations for `rwlog`.
The intent is to find order-of-magnitude improvements, not micro-optimizations.

## Guardrails

- Preserve current language semantics.
- Treat every idea as a hypothesis until measured.
- Prefer changes that improve asymptotic behavior, pruning power, or work avoidance.
- Require benchmarks on representative workloads before and after each experiment.

## Investigation Backlog

Each item is an investigation area, not a guaranteed improvement.

### Search/Scheduling Architecture

1. Replace strict left-biased stepping with adaptive branch scheduling guided by historical yield rate per branch.
2. Prioritize branches with lower estimated normalization cost before expensive branches.
3. Add a scheduler mode tuned for first-answer latency vs throughput and compare both modes.
4. Use dynamic branch throttling for branches that repeatedly produce duplicates.
5. Introduce beam-style bounded frontier for exploratory workloads and evaluate semantics-preserving variants.
6. Investigate stratified fairness where recursive producers receive budget quotas rather than strict alternation.
7. Add cooperative work-stealing across independent branches for multicore execution.
8. Replace queue discipline with pluggable schedulers (`FIFO`, `LIFO`, cost-priority, round-robin-by-call-key).
9. Cache branch failure signatures to fast-reject repeated dead paths.
10. Predict likely-empty conjunction branches early from shape constraints and schedule them first.

### Work Graph Representation

1. Replace tree-style `Rel` cloning with a DAG representation using structural hashing to share repeated subexpressions.
2. ~~Introduce immutable arena-backed nodes for `Rel`/`Node` to reduce `Arc` churn.~~ **Partially addressed — ~19% + ~2.6% improvement.** See [docs/perf_investigations/box_emit_node_shrink.md](docs/perf_investigations/box_emit_node_shrink.md) and [docs/perf_investigations/box_nodestep_emit_shrink.md](docs/perf_investigations/box_nodestep_emit_shrink.md). Boxing NF in Node::Emit shrank Node from ~136B to ~24B, eliminating most memcpy (11.58% → 0.56%) and drop overhead. Follow-up: boxing NF in NodeStep::Emit shrank NodeStep from ~152B to ~40B, reducing sret copy costs. Arena-backed nodes may yield further improvement but Node/NodeStep sizing is now addressed.
    - **Sub-investigation: Box NF in DiagonalStepResult/FixStepResult — DISCARDED (3.5-5% regression).** See [docs/perf_investigations/box_step_result_nf.md](docs/perf_investigations/box_step_result_nf.md). Tried boxing NF in step_in_place return values (~128B → ~16B). Failed because the compiler already optimizes sret efficiently for these simpler functions, and Box::new inside the callee is worse than in the caller. The NodeStep boxing pattern doesn't generalize.
3. Store normalized fragments once and reference by ID in execution nodes.
4. Replace recursive descent rewrites with iterative worklist rewrites to reduce stack pressure. **Partially addressed** — see [docs/perf_investigations/step_node_inline_control.md](docs/perf_investigations/step_node_inline_control.md). Outlining cold paths (step_or, ComposeWork/MeetWork::step_in_place) reduced step_node stack pressure by ~11%. step_node still has a 2792-byte frame (absorbing FixWork::step_in_place), but the hot path now benefits from cross-function optimization.
    - **Sub-investigation: iterative Node Drop — DISCARDED (1.3% regression).** See [docs/perf_investigations/node_drop_iterative.md](docs/perf_investigations/node_drop_iterative.md). Custom `Drop` for `Node<C>` using `ManuallyDrop`+`NodeParts` mirror enum. Compiled and passed tests but regressed due to `into_parts()` overhead on every pattern match and `mem::replace` in Drop. The 5.65% drop overhead in profiles includes deallocation costs that iterative drop cannot avoid.
    - **Sub-investigation: flatten Or spine — DISCARDED (0.8-1.6% regression).** See [docs/perf_investigations/flatten_or_spine.md](docs/perf_investigations/flatten_or_spine.md). Replaced binary `Or(Box<Node>, Box<Node>)` with flat `Vec<Node>` or `VecDeque<Node>` to eliminate recursive drop. Vec regressed due to O(n) remove(0); VecDeque regressed due to ring buffer overhead. The recursive drop is well-optimized by the compiler for the actual Or depths in practice.
    - **Sub-investigation: engine tight loop — DISCARDED (no improvement).** See [docs/perf_investigations/engine_loop_inlining.md](docs/perf_investigations/engine_loop_inlining.md). Manually inlined step_node into Engine::next() to keep Node on stack instead of round-tripping through self.root. U=39/100 — the compiler already performs this optimization at release levels.
5. Explore compact bytecode-style execution plans compiled from `Rel` before evaluation.
6. Add canonicalized subplan cache keyed by normalized plan shape.
7. Evaluate rope/chunk-based sequence storage vs current factor representation for long `Seq`.
8. Investigate specialized node types for common plan idioms (`rule ; call`, `call ; rule`, `A & B` with atoms). **Partially investigated — DISCARDED (12% regression).** See [docs/perf_investigations/split_work_node_variants.md](docs/perf_investigations/split_work_node_variants.md). Splitting Node::Work into Node::FixWork/ComposeWork/MeetWork to eliminate Work discriminant cache miss regressed due to re-boxing overhead — WorkStep returns Box<Work> which must be destructured and re-boxed into the specialized Node variant on every step transition.
9. Reduce Work<C> enum size by boxing PipeWork internally (624B→~288B). **Investigated** — see [docs/perf_investigations/allocation_overhead_analysis.md](docs/perf_investigations/allocation_overhead_analysis.md). 440K Box<Work> allocations waste 94% per FixWork boxing due to PipeWork sizing the enum.
10. ~~Add object pool / free list for Box<Work> and Box<Node> to eliminate 880K malloc/free cycles per query.~~ **Superseded** — see [docs/perf_investigations/diagonal_join_take_self_overhead.md](docs/perf_investigations/diagonal_join_take_self_overhead.md). In-place stepping for ComposeWork/MeetWork eliminated 88% of allocations (751K→88K), making pooling unnecessary.
11. ~~In-place stepping for FixWork to eliminate clone+alloc+free per step.~~ **Implemented — ~20% improvement.** See [docs/perf_investigations/fixwork_inplace_stepping.md](docs/perf_investigations/fixwork_inplace_stepping.md). FixWork steps in-place via `step_in_place`, reusing the existing Box<Work>. Reduced Box<Work> allocations by 49.3% (439K→223K). `recursive_even_backward_first64` from ~60ms to ~49ms. Inlining Work into Node was also tried but regressed 25% due to stack traffic.

### Matching and Unification-Equivalent Core (Matching-Only Semantics)

1. Replace generic term matching with opcode-specialized match programs compiled per pattern shape.
2. Introduce constructor-indexed dispatch tables to avoid repeated top-symbol checks. **Partially investigated — top-constructor prefilter DISCARDED then RE-INVESTIGATED.** See [docs/perf_investigations/compiled_match_prefilter.md](docs/perf_investigations/compiled_match_prefilter.md). Original top-level constructor mismatch check showed no improvement on even64 (U=43/100) due to small constructor vocabulary.
    - **Sub-investigation: root functor precheck with lock-free access — ~3.2% improvement on treecalc_synth_flip.** See [docs/perf_investigations/nf_functor_sig.md](docs/perf_investigations/nf_functor_sig.md). Re-investigated with synth_flip as primary workload (99.14% compose failure rate, diverse tree calculus constructors). Uses `get_unlocked()` for zero-overhead term access instead of `read_lock()`. Checks first build/match pattern root functor only. Also showed slight improvement on even64 (U=80). Full compiled match programs remain uninvestigated.
    - **Sub-investigation: multi-position precheck — DISCARDED (no improvement).** See [docs/perf_investigations/multi_pos_precheck.md](docs/perf_investigations/multi_pos_precheck.md). Extended root functor precheck to all pattern positions. U=56/100 on synth_flip — most NFs are arity-1, so multi-position adds nothing over single-position.
3. Precompute variable occurrence maps for each pattern to speed repeated-variable constraints.
4. Explore union-find-like equivalence structures for intra-side variable equalities during matching.
5. Add fast-paths for linear patterns (no repeated variables) separate from nonlinear patterns. **Partially investigated** — ground-term occurs check skip DISCARDED. See [docs/perf_investigations/skip_occurs_ground.md](docs/perf_investigations/skip_occurs_ground.md). Adding `is_ground()` early-return to `occurs_locked` showed U=42/100 on synth_flip — the walk already exits quickly for ground terms. Linearity-based elimination of occurs check entirely remains uninvestigated.
    - **Sub-investigation: remove occurs check from offset-aware matcher — ~3.9% improvement on treecalc_synth_flip.** See [docs/perf_investigations/remove_shifted_occurs.md](docs/perf_investigations/remove_shifted_occurs.md). Proved that occurs check in `match_terms_combined_shifted` always returns false because: (1) initial substitution is empty, (2) left/right variable namespaces are completely disjoint (left < offset, right >= offset), so no cyclic bindings are possible. Removed both `occurs_unlocked` calls and the now-dead function. U=100/100 (complete separation), neutral on secondary.
6. Pre-normalize variable IDs to dense ranges earlier to reduce substitution map size.
7. Evaluate hash-consed matched-subterm memoization for repeated pattern applications.
8. Cache match failures by `(pattern_id, subject_top_shape)` to skip impossible attempts.
9. Investigate SIMD-friendly structural comparison for small fixed-arity constructor trees.
10. Add matching cost model and schedule cheaper matches first in heterogeneous fusion.

### NF/Kernel Normalization Pipeline

1. Introduce a staged normalization pipeline with explicit cost-based reorder of commuting rewrites.
2. Memoize `compose_nf` results by normalized NF fingerprints.
3. Memoize `meet_nf` results by canonical pair fingerprints (order-normalized).
4. Separate cheap syntactic impossibility checks before expensive matching in compose/meet.
5. ~~Add canonical hash keys for `NF` to enable dedup and cache hits across branches.~~ **Implemented — ~10% improvement.** See [docs/perf_investigations/cached_nf_hash.md](docs/perf_investigations/cached_nf_hash.md). Added `cached_hash: u64` field to NF, pre-computed at construction. Hash impl returns cached value (one u64 write). PartialEq compares hash first as fast rejection. Eliminates repeated full-NF hashing in all FxHashSet operations.
6. Rework normalization to produce and consume compact intermediate IR rather than rebuilding full `NF`s.
7. ~~Identify hot paths where repeated factor/collect cycles can be eliminated.~~ **Partially addressed — ~8.8% improvement on program_synth_flip.** See [docs/perf_investigations/rwt_max_var_o1_computation.md](docs/perf_investigations/rwt_max_var_o1_computation.md). Replaced `max_var_index_terms` tree walks (5.68% of runtime) in compose_nf/meet_nf with O(1) computation from DropFresh metadata. Full factor/collect cycle elimination remains uninvestigated.
    - **Sub-investigation: eliminate redundant variable traversals in factor_tensor — ~4.2% improvement.** See [docs/perf_investigations/lazy_collect_tensor.md](docs/perf_investigations/lazy_collect_tensor.md). Reordered factor_tensor to run renumber_vars_list first (reusing lhs_vars for constraint renaming), collected RHS vars once instead of twice, replaced HashSet/HashMap with u64 bitsets, skipped constraint renaming for empty constraints. 12.5% improvement on treecalc secondary.
    - **Sub-investigation: virtual shift_vars — ~4% improvement on program_synth_flip.** See [docs/perf_investigations/virtual_shift_vars.md](docs/perf_investigations/virtual_shift_vars.md). Eliminated physical term tree rewriting for variable renaming-apart by combining shift+subst into a single pass (`apply_subst_shifted`). Avoids creating intermediate shifted terms that were immediately consumed by matching/substitution.
    - **Sub-investigation: offset-aware matching — ~2.2% improvement on treecalc_synth_flip.** See [docs/perf_investigations/offset_aware_match.md](docs/perf_investigations/offset_aware_match.md). Extended virtual shifting further: instead of shifting right-side terms before matching (full tree walk even with empty subst), the matcher handles variable offsets internally. For the 99%+ of compose attempts that fail, no shifting ever occurs. U=100/100 (complete separation).
    - **Sub-investigation: cache collect_tensor — DISCARDED (no improvement).** See [docs/perf_investigations/cache_collect_tensor.md](docs/perf_investigations/cache_collect_tensor.md). Cached RHS renaming result in NfInner. U=47/100 — eager construction cost for short-lived NFs offset savings; small term trees make per-call collect_tensor very cheap.
    - **Sub-investigation: ground-bit skipping in collect_vars/apply_var_renaming — ~1.5% improvement on recursive_even_backward_first64.** See [docs/perf_investigations/collect_vars_ground_bit.md](docs/perf_investigations/collect_vars_ground_bit.md). Added `is_ground()` bit-test to skip ground subtrees in `collect_vars_helper` and `apply_var_renaming`. Previously rejected on program_synth_flip due to codegen regression, but confirmed beneficial on the tabling-heavy workload (U=97/100).
    - **Sub-investigation: fused factor_tensor with substitution — ~27.8% improvement on treecalc_synth_flip.** See [docs/perf_investigations/fused_factor_compose.md](docs/perf_investigations/fused_factor_compose.md). Eliminated intermediate term creation in compose_nf by fusing apply_subst into factor_tensor. Instead of creating substituted intermediate terms (interned in HashMap) then collecting vars and renumbering, the fused `factor_tensor_with_subst` resolves variables through substitutions during its own traversal passes, producing final terms directly. Also handles constraint-derived subst_opt in the same pass. U=100/100 (complete separation), also improved secondary ~4.5%. The meet_nf path still uses the unfused pipeline.
    - **Sub-investigation: defer b-side collect_tensor — DISCARDED (no significant improvement).** See [docs/perf_investigations/defer_collect_rhs.md](docs/perf_investigations/defer_collect_rhs.md). Deferred `collect_tensor(b)` until after matching succeeds (99.14% of composes fail). Two approaches: (a) simple deferral to success path, (b) fusing DropFresh renaming into factor_tensor_with_subst via shifted_vars. Approach (b) regressed; approach (a) was borderline (U=73 then U=60 on retry). Root functor precheck already filters most incompatible pairs before collect_tensor runs, and collect_tensor is lightweight for typical small NFs.
8. Build a fusion planner that batches multiple adjacent kernel operations in one pass.
9. Add identity/annihilator propagation earlier to shrink plans before deep normalization.
10. Specialize unary-arity common cases to bypass general multi-arity machinery.

### DropFresh and Variable Routing

1. Replace generic `SmallVec` map representation with packed bitset/packed arrays for frequent small arities.
2. Precompute composition tables for common `DropFresh` patterns.
3. Introduce a canonical `DropFresh` interner to share identical routings.
4. ~~Add fast-path for identity and near-identity routings through tagged variants.~~ **Investigated — negligible ROI.** See [docs/perf_investigations/dropfresh_identity_fast_path.md](docs/perf_investigations/dropfresh_identity_fast_path.md). DropFresh is 100% identity for the critical workload (even64), but the kernel is only ~3-5% of runtime at the ~32ms baseline. Fast-paths implemented but produce no measurable improvement. Further kernel-level optimizations cannot meaningfully help tabling-heavy workloads.
5. Fuse adjacent `DropFresh` chains without materializing intermediate mappings.
6. Evaluate transposed/internal cache-friendly layouts for routing maps in composition-heavy workloads.

### Term Representation and Memory Layout

1. Move to arena indices with cache-aware contiguous child storage for `TermStore`. **Partially addressed** — see [docs/perf_investigations/memcpy_struct_size_reduction.md](docs/perf_investigations/memcpy_struct_size_reduction.md). Thin ChrState (`Option<Box<ChrStateData>>`) reduced NF from 224B→112B, NodeStep from 456B→240B, Node from 232B→128B. Memcpy dropped from 21% to <0.5% of execution. Arena indices for TermStore remain uninvestigated.
    - **Sub-investigation: Arc-wrap NF inner fields — significant improvement (U=95/100).** See [docs/perf_investigations/nf_arc_wrap.md](docs/perf_investigations/nf_arc_wrap.md). Wrapped NF fields in `Arc<NfInner<C>>` for O(1) cloning. Also eliminated double-Arc in DiagonalJoin seen lists (`Vec<Arc<NF<C>>>` → `Vec<NF<C>>`). Added `Arc::ptr_eq` fast path in PartialEq. Remaining double-Arc in fix.rs and rel.rs could be further optimized.
2. ~~Add global hash-consing for immutable ground subterms.~~ **Partially addressed** — ground-term tracking implemented via TermId bit encoding. See [docs/perf_investigations/ground_bit_subtree_skipping.md](docs/perf_investigations/ground_bit_subtree_skipping.md). Ground flag in bit 31 of TermId enables O(1) subtree skipping in apply_subst/apply_subst_shifted. ~9% improvement on program_synth_flip with zero tabling regression. Full ground-subterm deduplication (interning) remains uninvestigated.
3. Add optional per-query temporary arena to avoid long-lived heap churn for transient terms.
4. Use compact tagged integer encoding for tiny terms/vars to reduce pointer chasing.
5. Evaluate SoA layout for term fields to improve traversal throughput.
6. Introduce generation-based GC/reclamation for dead transient terms between query epochs.
7. Add copy-on-write term slabs shared across branches.
8. ~~Investigate lock-free symbol/term interning paths for parallel evaluators.~~ **Partially investigated — intern cache DISCARDED twice.** See [docs/perf_investigations/term_intern_cache.md](docs/perf_investigations/term_intern_cache.md). Direct-mapped cache showed U=50 on even64 (Round 13) and U=15 on synth_flip (Round 19, actively slower). Existing var_cache and all_same optimizations already handle the common cases; remaining HashMap overhead is irreducible hashconsing cost. Lock-free interning for parallelism remains uninvestigated.
9. ~~Evaluate alternative allocators for allocation-heavy workloads.~~ **Implemented — ~1.3% primary / ~21.5% secondary improvement.** See [docs/perf_investigations/mimalloc_global_allocator.md](docs/perf_investigations/mimalloc_global_allocator.md). Replaced glibc malloc with mimalloc as global allocator. Massive secondary improvement on treecalc_first16 (allocation-dominated workload). Set per-binary rather than in lib.rs due to profiling binaries with custom counting allocators.

### Constraint/CHR Engine Integration

1. ~~Add CHR predicate indexing by head functor/arity and argument shape.~~ **Implemented — ~27% improvement on CHR-heavy workloads.** See [docs/perf_investigations/chr_trigger_indexing.md](docs/perf_investigations/chr_trigger_indexing.md). First-argument functor indexing on the trigger table + RVarEnv reuse. Eliminated 69% of match_head calls (28.7M/41.8M) and 99.99% of RVarEnv heap allocations. `program_synth_flip` from ~7.3s to ~5.5s.
2. ~~Compile CHR rules into indexed decision structures rather than linear scans.~~ **Partially addressed** — see [docs/perf_investigations/chr_trigger_indexing.md](docs/perf_investigations/chr_trigger_indexing.md). First-argument indexing covers the most common case. Full decision-tree compilation for multi-argument or variable-first-arg patterns remains uninvestigated.
3. ~~Add incremental constraint store deltas to avoid full rechecks after each introduce.~~ **Partially addressed** — ownership-based clone elimination (`normalize_owned`/`combine_owned`) removed 98.8% of wasted ChrState clones. See [docs/perf_investigations/chr_normalize_clone_elimination.md](docs/perf_investigations/chr_normalize_clone_elimination.md). `program_synth_flip` from ~5.5s to ~4.9s (~10% improvement).
    - **Sub-investigation: incremental CHR normalization — ~1.4% improvement.** See [docs/perf_investigations/incremental_chr.md](docs/perf_investigations/incremental_chr.md). Added fixpoint watermark to skip re-processing stable constraints. Preserves watermark through compose pipeline when constraint args are ground (unchanged by subst). Also removed redundant rebuild_indexes call in solve_to_fixpoint. Modest improvement because many normalize calls involve fresh constraints and fixpoint loop was already efficient at skipping dead constraints.
    - **Sub-investigation: skip redundant match_head in apply_rule — ~10.4% improvement.** See [docs/perf_investigations/chr_skip_rematch.md](docs/perf_investigations/chr_skip_rematch.md). Removed redundant `env.reset()` and `match_head` re-matching in `apply_rule_by_id_reuse` — the RVarEnv already has correct bindings from `find_match_by_ids_reuse`. Pure code deletion (net -10 lines). U=92/100 on synth_flip, neutral on even64.
    - **Sub-investigation: hoist read_lock out of match_head — DISCARDED (no improvement).** See [docs/perf_investigations/chr_lock_hoist.md](docs/perf_investigations/chr_lock_hoist.md). Hoisted `terms.read_lock()` acquisition from per-call in `match_head` into `SearchCtx` (acquired once per search). U=52/100 — parking_lot's uncontended read lock is ~10ns, negligible compared to actual pattern matching work. Would matter more under multi-threaded contention.
    - **Sub-investigation: fuse CHR constraint remap + apply_subst — ~1.7% improvement.** See [docs/perf_investigations/fuse_chr_constraint_ops.md](docs/perf_investigations/fuse_chr_constraint_ops.md). Fused `remap_constraint_vars` + `apply_subst` for b-side constraint into single operation (one ChrStateData clone instead of two). Also fixed self.clone() + Arc::make_mut double-clone pattern in apply_subst and remap_vars. U=75/100.
    - **Sub-investigation: CHR duplicate-argument precheck — DISCARDED (no improvement).** See [docs/perf_investigations/chr_duparg_precheck.md](docs/perf_investigations/chr_duparg_precheck.md). Added precheck in normalize_owned to skip fixpoint when no rule can fire based on per-predicate arg indexes. U=34/100, -1.05% — precheck duplicated work already handled by IndexedTriggers dispatch. Only single-head rules exist in treecalc_synth_flip.
4. Introduce join-order optimization for multi-head CHR rules based on selectivity estimates.
5. Cache guard evaluation results for repeated `(rule, bindings)` pairs.
6. Add contradiction-first scheduling to fail branches earlier.
7. ~~Explore persistent constraint store snapshots to reduce clone costs across branches.~~ **Superseded** — ChrState clone overhead was eliminated by thin ChrState (`Option<Box<ChrStateData>>`) and ownership-based clone elimination (`normalize_owned`/`combine_owned`). See [docs/perf_investigations/memcpy_struct_size_reduction.md](docs/perf_investigations/memcpy_struct_size_reduction.md) and [docs/perf_investigations/chr_normalize_clone_elimination.md](docs/perf_investigations/chr_normalize_clone_elimination.md). Empty ChrState clone is now O(1), and non-empty ChrState clones are avoided entirely on the normalize/combine hot path.
    - **Sub-investigation: Option<Arc> for ChrState.program — DISCARDED (3.3% regression).** See [docs/perf_investigations/chrstate_option_arc.md](docs/perf_investigations/chrstate_option_arc.md). Changed `program: Arc<ChrProgram<T>>` to `Option<Arc<ChrProgram<T>>>` to skip atomic clone for empty programs. Improved secondary benchmark 4% but regressed primary 3.3% due to Option indirection overhead on all program accesses.
8. Intern and hash canonical residual-constraint states to deduplicate equivalent outputs.

### Tabling/Recursion Strategy

1. Replace coarse call-key table entries with stratified keys that separate shape and constraint components.
2. Add subsumption tabling: reuse answers from more-general calls when safe.
3. Add answer-trie indexes per call key for faster duplicate detection and replay.
4. Introduce semi-naive fixpoint updates to avoid reprocessing stable answers.
5. Evaluate strongly connected component scheduling for mutual recursion groups.
6. Add incremental invalidation model for environments where definitions change.
7. Investigate bounded early materialization of likely-hot recursive calls.
8. Add producer prioritization by estimated marginal new answers.
9. Compare eager replay vs batched replay strategies for consumer wakeups.
10. Explore differential dataflow-style recursive maintenance for monotone fragments.

### Conjunction/Meet Execution

1. Replace naive fair diagonal join with selectivity-aware join ordering.
2. Add cardinality/selectivity estimators for `AndGroup` components.
3. Introduce adaptive join algorithms (`nested-loop`, hash-join-like, indexed join) by workload.
4. Pre-filter candidate pairs using cheap shape signatures before full `meet_nf`.
5. Cache failed meet pairs to avoid repeated impossible intersections.
6. Rework `AndGroup` to pipeline partial meets instead of materializing large intermediate frontiers.
7. Use async producer/consumer channels for parallel branch production and controlled backpressure.
8. ~~Add branch-specific dedup filters to cut cross-product blow-up.~~ **Partially addressed — ~5% improvement.** See [docs/perf_investigations/arc_diagonal_join.md](docs/perf_investigations/arc_diagonal_join.md). Arc<NF<C>> wrapping in DiagonalJoin seen vectors and dedup sets eliminates deep NF clones on every emit. Dedup set insertion is now O(1) Arc clone instead of deep clone. Combined with earlier Arc wrapping in Table answers (see [docs/perf_investigations/arc_nf_answers.md](docs/perf_investigations/arc_nf_answers.md)).
    - **Sub-investigation: Arc-wrap pending NFs — ~7.6% improvement.** See [docs/perf_investigations/arc_pending_nf.md](docs/perf_investigations/arc_pending_nf.md). Extended Arc wrapping to DiagonalJoin pending VecDeque and pending_set FxHashSet. Eliminates deep NF clone per push_pending call. Combined with cached_nf_hash for ~7.8% combined improvement.

### Disjunction/Or Execution

1. Internally flatten nested `Or` structures once and schedule from a branch pool. **Investigated** — see [docs/perf_investigations/or_tree_and_per_step_cost.md](docs/perf_investigations/or_tree_and_per_step_cost.md). Or tree overhead is negligible for the heaviest workload (max 1 sibling). Or flattening would help wide-disjunction cases but those are already <1ms. The real bottleneck is ChrState clone/hash allocation (45% of execution).
2. Add duplicate-answer suppression close to branch emission rather than global late-stage.
3. Share normalized prefix work among sibling `Or` branches where legal.
4. Add branch pruning based on static incompatibility with downstream constraints.
5. Batch branch stepping to amortize scheduler overhead.

### Parsing/Compilation Layer

1. Add a compile phase from parsed `Rel` to optimized execution plan cached per definition.
2. Introduce plan-level static analyses: arity flow, variable liveness, potential determinism.
3. Add detection and specialization for deterministic relations.
4. Inline small relation calls into caller plans when profitable.
5. Add whole-program relation call graph analysis for cycle grouping and specialization.
6. Precompute top-symbol indexes for each rule head during parsing.
7. Compile frequently used queries into reusable prepared plans.

### Deduplication and Canonicalization

0. ~~Replace SipHash with FxHash for NF dedup HashSets.~~ **Implemented — ~5% improvement.** See [docs/perf_investigations/fxhash_nf_dedup.md](docs/perf_investigations/fxhash_nf_dedup.md). Replaced `std::collections::HashSet` with `rustc_hash::FxHashSet` across all hot-path NF dedup sets (DiagonalJoin, Engine, Table, DedupQueue). SipHash was 4.17% of runtime; FxHash eliminated most of that overhead.
1. Define stable canonical fingerprints for answers to make dedup O(1) hashed in common cases.
2. Add per-branch dedup + global dedup layering to reduce central contention.
3. Investigate canonical alpha-renaming at emission boundary to improve duplicate collapse.
4. Add bounded LRU caches for recently emitted canonical answers in streaming queries.
5. Evaluate probabilistic prefilters (Bloom) before full dedup checks for high-volume streams.

### Parallelism

1. Parallelize independent `Or` branches with work-stealing thread pools.
2. Parallelize `AndGroup` producers and merge with deterministic stable ordering layer.
3. Split tabling producer evaluation and consumer replay onto separate executors.
4. Use lock-sharded tables and caches keyed by call key/hash buckets.
5. Investigate data-parallel match evaluation for batches of candidate terms.
6. Add NUMA-aware placement experiments for large memory-heavy workloads.

### Output/Rendering Path

1. Separate answer generation from rendering to measure pure engine throughput.
2. Add lazy formatting to avoid rendering answers that are dropped by upstream filters/tests.
3. Cache rendered symbol strings for repeated term structures in large result sets.

### Correctness-Preserving Pruning Analyses

1. Add static impossibility analysis for constructor conflicts before runtime.
2. Add variable-occurrence compatibility analysis to reject impossible compositions early.
3. Add monotonicity/determinism annotations inferred from rules for safer aggressive pruning.
4. Identify relation fragments where exhaustive normalization can be replaced by precompiled transfer functions.
5. Add bounded symbolic execution on plans to discover dead branches ahead of runtime.

### Experimental Alternate Architectures

1. Build a prototype Datalog-style semi-naive engine for a subset and compare recursion-heavy workloads.
2. Build a prototype e-graph-based normalization backend for compose/meet-heavy workloads.
3. Build a prototype incremental dataflow executor where each relation is a node and answers are streams.
4. Build a bytecode VM backend with explicit registers for vars/substitutions.
5. Build a GPU-accelerated matcher prototype for broad shallow term sets.

## Prioritization Candidates (High Expected ROI)

1. ~~Memoization and canonical hashing for `compose_nf`/`meet_nf`.~~ **Investigated — not worth pursuing.** See [docs/perf_investigations/compose_meet_memoization.md](docs/perf_investigations/compose_meet_memoization.md). Duplication is only 21%, always exactly 2x, caused by tabling fixpoint verification. The real target is fixpoint strategy (#3 below).
2. Selectivity-aware `AndGroup` join ordering and failed-pair caches.
3. Tabling improvements (answer tries + semi-naive updates + replay strategy). **Partially investigated** — see [docs/perf_investigations/fixpoint_verification_overhead.md](docs/perf_investigations/fixpoint_verification_overhead.md). Fixpoint verification overhead is low-ROI for current workloads (max ~3ms savings). Semi-naive requires 3+ iterations to help, which doesn't occur in the current corpus.
4. Compiled match programs with constructor-indexed dispatch.
5. Plan compilation/caching for parsed relation definitions and frequent queries.
6. Structural sharing/DAG representation for `Rel` and normalized plans.
7. ~~ChrState clone/hash/eq optimization.~~ **Superseded** — see [docs/perf_investigations/per_step_cost_decomposition.md](docs/perf_investigations/per_step_cost_decomposition.md). ChrState cloning is a symptom, not the root cause. 89.8% of ChrState clones originate from `FixWork::clone`, which deep-copies `CallKey<C>` (containing NFs) on every step. The real fix is Arc-wrapping CallKey in FixWork (~22% estimated reduction) rather than optimizing ChrState itself.
8. ~~FixWork clone-per-step elimination.~~ **Implemented — 20-25% improvement.** See [docs/perf_investigations/callkey_arc_wrapping.md](docs/perf_investigations/callkey_arc_wrapping.md). Arc-wrapping CallKey in FixWork reduced `recursive_even_backward_first64` from ~105ms to ~84ms.
9. ~~Mutex-to-FastLock for single-threaded tabling.~~ **Implemented — ~20% improvement.** See [docs/perf_investigations/fastlock_mutex_elimination.md](docs/perf_investigations/fastlock_mutex_elimination.md). Replaced `parking_lot::Mutex` with zero-cost `FastLock` in Table. 1.74M Mutex locks per 64 answers (8 per FixWork step, 99.1% of answer_at calls returning None). Reduced `recursive_even_backward_first64` from ~85ms to ~65-71ms. Remaining targets: FixWork::clone (~4%), malloc/free (~6%), dispatch (~8%), drop overhead (~5.5%).
10. ~~Allocation overhead reduction (Box<Work>/Box<Node> size + malloc/free elimination).~~ **Implemented — ~31% improvement.** See [docs/perf_investigations/diagonal_join_take_self_overhead.md](docs/perf_investigations/diagonal_join_take_self_overhead.md). In-place stepping for ComposeWork/MeetWork eliminated 663K alloc+free cycles (88% of total). Allocations: 751K→88K (-88%), bytes: 179MB→14MB (-92%). `recursive_even_backward_first64` from ~46ms to ~32ms. Cumulative 3.28× speedup from original ~105ms.
11. ~~FixWork in-place stepping.~~ **Implemented — ~20% improvement.** See [docs/perf_investigations/fixwork_inplace_stepping.md](docs/perf_investigations/fixwork_inplace_stepping.md). Eliminated 216K clone+alloc+free cycles per 64 answers. Cumulative 2.14× speedup on critical workload (105ms → 49ms across all optimizations).
12. ~~step_node inline control.~~ **Implemented — ~16% improvement.** See [docs/perf_investigations/step_node_inline_control.md](docs/perf_investigations/step_node_inline_control.md). Added `#[inline(never)]` to cold paths (step_or, ComposeWork/MeetWork::step_in_place), freeing compiler inlining budget for hot FixWork path. A/B tested: 30.1ms → 25.5ms with non-overlapping ranges. Cumulative 4.12× speedup (105ms → 25.5ms).
13. ~~Memcpy/struct size reduction (thin ChrState).~~ **Implemented — ~8% improvement.** See [docs/perf_investigations/memcpy_struct_size_reduction.md](docs/perf_investigations/memcpy_struct_size_reduction.md). Restructured ChrState from 128B to 16B via `Option<Box<ChrStateData>>`. Cascaded: NF 224→112B, NodeStep 456→240B, Node 232→128B. Memcpy dropped from 21% to <0.5%. step_node frame halved (2792→1384B). Boxing individual fields was tried first and REGRESSED 22% due to pointer chasing replacing L1-hot stack reloads. Cumulative ~4.6× speedup (105ms → 22.6ms).
14. ~~Eager compose pair processing.~~ **Reverted — caused catastrophic regression on CHR-heavy workloads.** See [docs/perf_investigations/eager_compose_pairs.md](docs/perf_investigations/eager_compose_pairs.md). Replaced cursor-based one-pair-per-step compose processing with eager batch processing. Improved `recursive_even_backward_first64` from ~13.9ms to ~7.0ms (~50%), but caused `treecalc_synth_flip` to regress from ~3s to >60s (hanging). Eager processing floods pending queue before CHR constraint propagation can prune search branches. Reverted to cursor-based approach.
    - **Sub-investigation: budgeted eager compose — DISCARDED (CHR regression at every budget).** See [docs/perf_investigations/compose_budget.md](docs/perf_investigations/compose_budget.md). Tested budgets from 16 down to 1. Even budget=1 causes synth_flip to hang. The regression is about execution ORDER not batch SIZE — the one-step delay between NF arrival and cursor processing is essential for CHR pruning. **Remaining opportunity: batch cursor processing within pre_step (preserves one-step delay).**
    - **Sub-investigation: compile-time eager compose for trivial constraints — ~3.7% improvement.** See [docs/perf_investigations/eager_unconstrained.md](docs/perf_investigations/eager_unconstrained.md). Added `const ALWAYS_EMPTY: bool` to `ConstraintOps`. When true (C=()), compose pairs eagerly in on_new_left/on_new_right. When false (C=ChrState), cursor-based as before. Monomorphized at compile time — zero-cost branching. Improvement is 3.7% vs hypothesized 64.6% because prior optimizations already reduced compose dispatch overhead.

## Suggested Experiment Template

1. Hypothesis: one sentence about expected speedup mechanism.
2. Scope: exact subsystem and files touched.
3. Workloads: benchmark IDs and why they are representative.
4. Metrics: first-answer latency, total time, allocations, peak RSS, steps, cache hit rates.
5. Result: absolute numbers and relative change.
6. Regression check: semantics test suite and existing property tests.
7. Decision: keep, iterate, or revert.
