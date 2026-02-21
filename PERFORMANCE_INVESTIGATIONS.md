# rwlog Performance Investigations

This document is a backlog of architecture-level performance investigations for `rwlog`.
The intent is to find order-of-magnitude improvements, not micro-optimizations.

## Guardrails

- Preserve current language semantics.
- Treat every idea as a hypothesis until measured.
- Prefer changes that improve asymptotic behavior, pruning power, or work avoidance.
- Require benchmarks on representative workloads before and after each experiment.

## Major Improvement Proposals

Architecture-level improvement proposals. Each targets a distinct subsystem and is paired with benchmark cases for before/after measurement.

### 1. AOT Plan Compilation to Bytecode / Register Machine

Add an ahead-of-time compiler from parsed `Rel` into a compact bytecode with explicit registers for current NF, substitution environments, call keys / table handles, and branch continuation state. Replace the current "fat enum tree" stepping model with an interpreter over compact instruction streams (or a "direct threaded" interpreter). Cache compiled plans per relation and per query shape.

This creates a single choke point where you can: fuse adjacent operations (`rule ; call`, `call ; rule`, repeated `;` chains), eliminate `Rel` cloning overhead structurally (bytecode is immutable, shared), specialize hot instructions (e.g., "match root functor then fast-fail" as a single op), and add profile-driven layout (instruction ordering, hot/cold splitting) without relying on LLVM PGO.

**Partially addressed — batch-advance single-Atom Calls ~81.6% total corpus improvement.** See [docs/perf_investigations/pipe_batch_advance.md](docs/perf_investigations/pipe_batch_advance.md). Inline resolution of Calls whose body is `Rel::Atom(nf)` bypasses FixWork/Table/ComposeWork/DiagonalJoin machinery entirely. `sequence_chain_len4096` from ~3.94s to ~87ms (45x). Full bytecode compilation remains uninvestigated but this demonstrates the payoff of eliminating per-step dispatch overhead.

**Key benchmark cases:** `sequence_chain_len4096` (~~plan interpretation overhead via O(n) `to_vec()` per step~~ now 87ms with batch-advance), `hot_call_site_256` (256 calls to a 32-rule dispatch relation; each call re-walks the Or spine — plan caching would compile the dispatch table once)

### 2. Whole-Program Determinism + Mode Inference

A compile-time analysis pass over relation definitions: infer determinism under an input/output mode (e.g., `@ground_input ; rel` deterministic even if `rel ; @output` is not), infer linearity/nonlinearity of rule heads, infer whether a call is "constructor-driven" vs "variable-driven".

Use that to: inline small deterministic callees into callers, pick specialized execution strategies (e.g., "single successor rule" vs "search tree"), bypass parts of tabling when provably unnecessary (deterministic + terminating fragment).

This changes evaluation from "everything is a search problem" to "search only where necessary," while preserving semantics.

**Key benchmark cases:** `inline_amplification_256` (256 distinct trivially-deterministic relations composed in sequence; stresses per-call Fix/Call + tabling overhead that inlining would eliminate), existing `recursive_add_*`

### 3. Compiled Matching: Decision Trees + Discrimination Trees

Replace generic term matching with compiled match programs: for each rule head (and for compose/meet pattern lists), compile a flat decision program with top functor checks, arity checks, selected deeper position checks, variable binding writes, repeated-variable equality checks, and early contradiction exits. Then add multi-rule indexing via discrimination tree / trie keyed by functor paths to dispatch directly to candidate rules.

This turns "O(rules) attempts with repeated generic matcher overhead" into "direct dispatch to a tiny candidate set with a straight-line matcher."

**Key benchmark cases:** `wide_match_512` (512 rules sharing top functor `pair`; root precheck passes for all, forcing depth-2 matching to reject — discrimination trees dispatch in O(1)), `nonlinear_match_64`

### 4. Terms as Closures: Explicit-Substitution + Explicit-Shift

Introduce a second term representation for transient evaluation: `T = Concrete TermId | Susp { base: TermId, subst: SubstId, shift: i32 }`. Update matching, factor/collect, and CHR argument evaluation to operate directly on `Susp` views (forcing only when needed for output interning / dedup).

This extends the already-successful "virtual shift / offset-aware matching" direction into the full substitution pipeline, eliminating repeated tree walks in `apply_subst`-dominated workloads.

**Key benchmark cases:** `deep_rewrite_depth64`, `deep_rewrite_depth256` (8-wide recursive `wide_inc` on depth-64/256 terms; each level applies 8-variable substitution on a 17-node build pattern — closures would defer these walks for ~13-16x improvement)

### 5. Adaptive Search Scheduling

Replace strict left-biased stepping with a scheduler that maintains per-branch statistics: estimated cost per step, yield rate (answers per step), duplicate rate (answers rejected by dedup), failure rate (steps producing no frontier progress). Offer two explicit modes: minimize time-to-first-answer, and maximize answers/sec under bounded memory.

For synthesis-style workloads, performance is dominated by how fast you reach a productive subspace; a scheduler change can shift effective complexity without touching kernel cost.

**Key benchmark cases:** `hetero_or_branches`, `failfast_conjunction`

### 6. True Multicore Execution

A parallel executor with: per-worker deques (Chase-Lev style), work-stealing for independent branches, sharded tables + sharded term interning (or per-worker transient stores + merge), deterministic merge layer for answer streams if required by tests.

Targets linear-to-sublinear wall time reduction on wide branching workloads.

**Key benchmark cases:** `heavy_or_16`, `parallel_and_32x32_overlap16`

### 7. Tabling Redesign: Answer Tries + Semi-Naive + SCC

Replace "flat sets of answers per call" with: an answer trie keyed by canonicalized NF (alpha-renamed + hashed), delta sets to propagate only new answers (semi-naive), and SCC-based scheduling for mutually recursive groups.

This changes recursion cost from "replay everything" to "replay only new," which is the standard asymptotic jump for recursive logic engines. Semi-naive requires 3+ fixpoint iterations to help, which the current corpus doesn't trigger — these new benchmarks provide that coverage.

**Partially implemented — semi-naive replay watermarks ~96.6% improvement on graph_reach_64.** See [docs/perf_investigations/tabling_semi_naive.md](docs/perf_investigations/tabling_semi_naive.md). Added replay watermark to tabling: consumers in subsequent fixpoint iterations only replay delta (new) answers. Compose attempts dropped from 5.38M to 131K (41x reduction). graph_reach_64 from ~190ms to ~6.4ms (30x speedup). Answer tries, SCC scheduling, and subsumption tabling remain uninvestigated.

**Key benchmark cases:** ~~`graph_reach_64`~~ (now 6.4ms with semi-naive), `left_rec_32` (unaffected — different recursion pattern)

### 8. Conjunction/Meet as Join Optimizer

Replace "one diagonal join strategy" with: runtime join-order selection based on selectivity estimates, multiple join algorithms (nested-loop for small×large, hash join keyed by shape/functor signatures, indexed join for large streams), and failed-pair caching keyed by stable fingerprints.

Converts worst-case cross products into something closer to database join complexity.

**Key benchmark cases:** `join_low_overlap_64x64`, `join_skewed_128x4`, `join_high_overlap_64x64`

### 9. Constraint-State Canonicalization + Global Interning

Push the commutative-hash normalize cache further by: making normalized `ChrState` structurally interned (hash-consed) so identical states across branches become pointer-identical, dedup at the state level rather than only at the "normalize result cache" level, and feeding canonical constraint-state IDs into call keys and answer fingerprints.

Turns an optimization (memoizing normalize results) into a representation invariant (canonical state identity), enabling pervasive work avoidance: cheaper equality/dedup, higher cache hit rates across the engine, and less memory churn.

**Key benchmark cases:** `constraint_perm_4`, `multi_head_chr_join`

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
    - **Sub-investigation: mid_normalized flag to skip redundant normalize_mid_atoms — ~6.3% total corpus improvement.** See [docs/perf_investigations/pipe_lazy_mid_normalize.md](docs/perf_investigations/pipe_lazy_mid_normalize.md). Added dirty flag to PipeWork that skips normalize_mid_atoms() when mid has no normalizable structure. Eliminates O(n²) to_vec() overhead for long deterministic chains (sequence_chain_len4096 was 83.8% of total time). U=96/100. sequence_chain_len4096 still dominates — remaining bottleneck is O(n) per-step compose/step overhead requiring plan compilation.
8. Investigate specialized node types for common plan idioms (`rule ; call`, `call ; rule`, `A & B` with atoms). **Partially investigated — DISCARDED (12% regression).** See [docs/perf_investigations/split_work_node_variants.md](docs/perf_investigations/split_work_node_variants.md). Splitting Node::Work into Node::FixWork/ComposeWork/MeetWork to eliminate Work discriminant cache miss regressed due to re-boxing overhead — WorkStep returns Box<Work> which must be destructured and re-boxed into the specialized Node variant on every step transition.
9. Reduce Work<C> enum size by boxing PipeWork internally (624B→~288B). **Investigated** — see [docs/perf_investigations/allocation_overhead_analysis.md](docs/perf_investigations/allocation_overhead_analysis.md). 440K Box<Work> allocations waste 94% per FixWork boxing due to PipeWork sizing the enum.
10. ~~Add object pool / free list for Box<Work> and Box<Node> to eliminate 880K malloc/free cycles per query.~~ **Superseded** — see [docs/perf_investigations/diagonal_join_take_self_overhead.md](docs/perf_investigations/diagonal_join_take_self_overhead.md). In-place stepping for ComposeWork/MeetWork eliminated 88% of allocations (751K→88K), making pooling unnecessary.
11. ~~In-place stepping for FixWork to eliminate clone+alloc+free per step.~~ **Implemented — ~20% improvement.** See [docs/perf_investigations/fixwork_inplace_stepping.md](docs/perf_investigations/fixwork_inplace_stepping.md). FixWork steps in-place via `step_in_place`, reusing the existing Box<Work>. Reduced Box<Work> allocations by 49.3% (439K→223K). `recursive_even_backward_first64` from ~60ms to ~49ms. Inlining Work into Node was also tried but regressed 25% due to stack traffic.

### Matching and Unification-Equivalent Core (Matching-Only Semantics)

1. Replace generic term matching with opcode-specialized match programs compiled per pattern shape.
2. ~~Introduce constructor-indexed dispatch tables to avoid repeated top-symbol checks.~~ **Partially implemented — top-constructor prefilter + DiagonalJoin functor indexing.** See [docs/perf_investigations/compiled_match_prefilter.md](docs/perf_investigations/compiled_match_prefilter.md). Original top-level constructor mismatch check showed no improvement on even64 (U=43/100) due to small constructor vocabulary.
    - **Sub-investigation: root functor precheck with lock-free access — ~3.2% improvement on treecalc_synth_flip.** See [docs/perf_investigations/nf_functor_sig.md](docs/perf_investigations/nf_functor_sig.md). Re-investigated with synth_flip as primary workload (99.14% compose failure rate, diverse tree calculus constructors). Uses `get_unlocked()` for zero-overhead term access instead of `read_lock()`. Checks first build/match pattern root functor only. Also showed slight improvement on even64 (U=80). Full compiled match programs remain uninvestigated.
    - **Sub-investigation: multi-position precheck — DISCARDED (no improvement).** See [docs/perf_investigations/multi_pos_precheck.md](docs/perf_investigations/multi_pos_precheck.md). Extended root functor precheck to all pattern positions. U=56/100 on synth_flip — most NFs are arity-1, so multi-position adds nothing over single-position.
    - **Sub-investigation: depth-2 compose precheck — DISCARDED (no improvement).** See [docs/perf_investigations/depth2_precheck.md](docs/perf_investigations/depth2_precheck.md). Extended root functor precheck to check first child's root functor. U=59/100, 0.25% — depth-2 checks add minimal value beyond existing root precheck. The compose precheck design space appears exhausted for this workload.
    - **Sub-investigation: DiagonalJoin root functor indexing — ~1.37% improvement.** See [docs/perf_investigations/indexed_diagonal_join.md](docs/perf_investigations/indexed_diagonal_join.md). Index NFs in ComposeStrategy by root functor of build/match patterns. Compose pairs are only generated between functor-compatible NFs, reducing attempts from ~324K to ~278K. U=90/100, neutral on secondary.
3. Precompute variable occurrence maps for each pattern to speed repeated-variable constraints.
4. Explore union-find-like equivalence structures for intra-side variable equalities during matching.
5. Add fast-paths for linear patterns (no repeated variables) separate from nonlinear patterns. **Partially investigated** — ground-term occurs check skip DISCARDED. See [docs/perf_investigations/skip_occurs_ground.md](docs/perf_investigations/skip_occurs_ground.md). Adding `is_ground()` early-return to `occurs_locked` showed U=42/100 on synth_flip — the walk already exits quickly for ground terms. Linearity-based elimination of occurs check entirely remains uninvestigated.
    - **Sub-investigation: remove occurs check from offset-aware matcher — ~3.9% improvement on treecalc_synth_flip.** See [docs/perf_investigations/remove_shifted_occurs.md](docs/perf_investigations/remove_shifted_occurs.md). Proved that occurs check in `match_terms_combined_shifted` always returns false because: (1) initial substitution is empty, (2) left/right variable namespaces are completely disjoint (left < offset, right >= offset), so no cyclic bindings are possible. Removed both `occurs_unlocked` calls and the now-dead function. U=100/100 (complete separation), neutral on secondary.
    - **Sub-investigation: eliminate occurs checks from compose-path matchers — DISCARDED (correctness failure).** See [docs/perf_investigations/eliminate_compose_occurs.md](docs/perf_investigations/eliminate_compose_occurs.md). Attempted to extend the offset-aware occurs check removal to `match_terms_combined_shifted_with_left_renaming` and `match_terms_combined`. Tests hang (lam_eq beta reduction creates infinite terms). Cross-namespace substitution cycles ARE possible through the combined substitution even with disjoint namespaces — the offset-aware matcher's proof does NOT generalize because these matchers have a non-monotone binding order.
6. Pre-normalize variable IDs to dense ranges earlier to reduce substitution map size.
7. Evaluate hash-consed matched-subterm memoization for repeated pattern applications. **Partially addressed — shift_term memoization ~35.5% improvement.** See [docs/perf_investigations/shift_memo.md](docs/perf_investigations/shift_memo.md). Thread-local cache for shift_term results keyed by packed (TermId, offset). Same compound terms shifted by same offset across 278K compose attempts. U=100/100 (complete separation), neutral on secondary.
    - **Sub-investigation: direct-mapped array cache for shift_term — DISCARDED (33.9% regression).** See [docs/perf_investigations/shift_array_cache.md](docs/perf_investigations/shift_array_cache.md). Replaced HashMap with fixed-size Vec direct-mapped cache. Hashbrown's SIMD-accelerated probing is far superior; packed key's poor low-bit distribution causes massive collisions with modulo indexing.
    - **Sub-investigation: thread-local memoization cache for apply_subst — DISCARDED (not significant).** See [docs/perf_investigations/apply_subst_memo.md](docs/perf_investigations/apply_subst_memo.md). Added SubstCache with (TermId, subst_fingerprint) keys. U=62/100, 0.28% — fingerprint computation + HashMap overhead per-call cancels out cache hit savings. apply_subst's existing fast paths (ground bit, inline vars) handle most calls cheaply; the cache only helps for complex non-ground terms which are a minority.
8. Cache match failures by `(pattern_id, subject_top_shape)` to skip impossible attempts.
9. ~~Investigate SIMD-friendly structural comparison for small fixed-arity constructor trees.~~ **Investigated — no improvement.** See [docs/perf_investigations/target_cpu_native.md](docs/perf_investigations/target_cpu_native.md). Building with `-Ctarget-cpu=native` enabled 14,721 AVX2 instructions but U=53/100 (no significant improvement). The workload is pointer-chasing bound (hash table probing, term tree walks), not SIMD-amenable. SwissTable's 16-byte probe groups don't benefit from 32-byte AVX2 registers.
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
    - **Sub-investigation: cache DropFresh rhs_map for inline-renaming compose — ~3.71% improvement.** See [docs/perf_investigations/cached_rhs_map.md](docs/perf_investigations/cached_rhs_map.md). Cached the DropFresh reverse mapping in NfInner and wrote an inline-renaming matcher that applies variable renaming during matching instead of pre-creating renamed terms. Eliminates per-compose `apply_var_renaming_list` tree walk for the a-side (324K calls). collect_tensor(b) deferred to success path only. U=100/100 (complete separation), neutral on secondary.
    - **Sub-investigation: defer shift_term to compose success path — DISCARDED (slight regression).** See [docs/perf_investigations/defer_shift_compose.md](docs/perf_investigations/defer_shift_compose.md). Attempted to defer shift_term() calls during compose matching to the success path. shift_term at 8.97% was hypothesized to be wasted on the 99.14% failing compose attempts. U=34/100, -1.11% — most failures exit before reaching Var-App bindings where shift_term is called. SmallVec bookkeeping overhead for deferred tracking negated savings.
    - **Sub-investigation: inline shift_term into apply_subst traversals — DISCARDED (-0.55%).** See [docs/perf_investigations/apply_subst_inline_shift.md](docs/perf_investigations/apply_subst_inline_shift.md). Attempted to defer variable shifting via ShiftMask bitmask, applying shifts on-the-fly during apply_subst/factor_tensor traversals. U=29/100 — offset-aware matching (Round 6) already eliminated most shift_term calls; deferred shifting overhead (bit ops, extra branches) exceeded residual savings.
    - **Sub-investigation: defer b-side collect_tensor — DISCARDED (no significant improvement).** See [docs/perf_investigations/defer_collect_rhs.md](docs/perf_investigations/defer_collect_rhs.md). Deferred `collect_tensor(b)` until after matching succeeds (99.14% of composes fail). Two approaches: (a) simple deferral to success path, (b) fusing DropFresh renaming into factor_tensor_with_subst via shifted_vars. Approach (b) regressed; approach (a) was borderline (U=73 then U=60 on retry). Root functor precheck already filters most incompatible pairs before collect_tensor runs, and collect_tensor is lightweight for typical small NFs.
    - **Sub-investigation: eliminate split_match_subst in compose_nf — ~16.1% improvement.** See [docs/perf_investigations/skip_split_subst.md](docs/perf_investigations/skip_split_subst.md). Returned raw combined substitution from matching instead of splitting into (left, right) halves. Consumers resolve bindings lazily through apply_subst's natural chain following. Eliminated 14.21% overhead from split_match_subst (walking all bindings, calling apply_subst on each, creating intermediate TermStore entries). U=100/100 (complete separation), neutral on secondary. meet_nf path still uses split_match_subst.
8. Build a fusion planner that batches multiple adjacent kernel operations in one pass.
9. Add identity/annihilator propagation earlier to shrink plans before deep normalization.
10. Specialize unary-arity common cases to bypass general multi-arity machinery. **Partially investigated — unary compose specialization DISCARDED.** See [docs/perf_investigations/unary_compose_specialize.md](docs/perf_investigations/unary_compose_specialize.md). Specialized compose_nf for arity-1 NFs (direct matching, SmallVec rhs_map, deferred b-side collect_tensor). U=65/100, 0.26% — match_term_lists_shifted already has arity-1 fast path, and allocation overhead is negligible with mimalloc.

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
4. ~~Use compact tagged integer encoding for tiny terms/vars to reduce pointer chasing.~~ **Implemented — ~0.66% improvement.** See [docs/perf_investigations/inline_var_termid.md](docs/perf_investigations/inline_var_termid.md). Encoded variables and nullary constants directly in TermId tag bits (2-bit tag + 30-bit payload), eliminating TermStore lookups for the two most common term kinds. Modest improvement because `get_unlocked()` was already very fast (direct Vec index, no locking).
5. Evaluate SoA layout for term fields to improve traversal throughput.
6. Introduce generation-based GC/reclamation for dead transient terms between query epochs.
7. Add copy-on-write term slabs shared across branches.
8. ~~Investigate lock-free symbol/term interning paths for parallel evaluators.~~ **Partially investigated — intern cache DISCARDED twice, single-shard DISCARDED.** See [docs/perf_investigations/term_intern_cache.md](docs/perf_investigations/term_intern_cache.md). Direct-mapped cache showed U=50 on even64 (Round 13) and U=15 on synth_flip (Round 19, actively slower). Existing var_cache and all_same optimizations already handle the common cases; remaining HashMap overhead is irreducible hashconsing cost. Lock-free interning for parallelism remains uninvestigated.
    - **Sub-investigation: eliminate double hashing via raw_entry — DISCARDED (1.5% regression).** See [docs/perf_investigations/single_shard_intern.md](docs/perf_investigations/single_shard_intern.md). Pre-computed FxHash once and used raw_entry API for both shard selection and HashMap lookup. U=35/100 — FxHash is so fast (~5-15ns) that double computation is negligible. raw_entry closure indirection cancels savings. The 9.3% interning cost is dominated by hash table probing and Term equality comparisons, not hash computation.
9. ~~Evaluate alternative allocators for allocation-heavy workloads.~~ **Implemented — ~1.3% primary / ~21.5% secondary improvement.** See [docs/perf_investigations/mimalloc_global_allocator.md](docs/perf_investigations/mimalloc_global_allocator.md). Replaced glibc malloc with mimalloc as global allocator. Massive secondary improvement on treecalc_first16 (allocation-dominated workload). Set per-binary rather than in lib.rs due to profiling binaries with custom counting allocators.

### Constraint/CHR Engine Integration

1. ~~Add CHR predicate indexing by head functor/arity and argument shape.~~ **Implemented — ~27% improvement on CHR-heavy workloads.** See [docs/perf_investigations/chr_trigger_indexing.md](docs/perf_investigations/chr_trigger_indexing.md). First-argument functor indexing on the trigger table + RVarEnv reuse. Eliminated 69% of match_head calls (28.7M/41.8M) and 99.99% of RVarEnv heap allocations. `program_synth_flip` from ~7.3s to ~5.5s.
2. ~~Compile CHR rules into indexed decision structures rather than linear scans.~~ **Partially addressed** — see [docs/perf_investigations/chr_trigger_indexing.md](docs/perf_investigations/chr_trigger_indexing.md). First-argument indexing covers the most common case. Full decision-tree compilation for multi-argument or variable-first-arg patterns remains uninvestigated.
    - **Sub-investigation: pre-flatten CHR head patterns — ~7.0% improvement.** See [docs/perf_investigations/flat_chr_match.md](docs/perf_investigations/flat_chr_match.md). Pre-flattened head argument patterns into contiguous `FlatMatchOp` arrays at program construction time, replacing the generic PatArena-based tree walk. Eliminated PatArena indirection, reduced stack entry size from 16 to 4 bytes, improved cache locality. U=100/100 (complete separation), neutral on secondary.
3. ~~Add incremental constraint store deltas to avoid full rechecks after each introduce.~~ **Partially addressed** — ownership-based clone elimination (`normalize_owned`/`combine_owned`) removed 98.8% of wasted ChrState clones. See [docs/perf_investigations/chr_normalize_clone_elimination.md](docs/perf_investigations/chr_normalize_clone_elimination.md). `program_synth_flip` from ~5.5s to ~4.9s (~10% improvement).
    - **Sub-investigation: incremental CHR normalization — ~1.4% improvement.** See [docs/perf_investigations/incremental_chr.md](docs/perf_investigations/incremental_chr.md). Added fixpoint watermark to skip re-processing stable constraints. Preserves watermark through compose pipeline when constraint args are ground (unchanged by subst). Also removed redundant rebuild_indexes call in solve_to_fixpoint. Modest improvement because many normalize calls involve fresh constraints and fixpoint loop was already efficient at skipping dead constraints.
    - **Sub-investigation: skip normalize_owned when at fixpoint — DISCARDED (no improvement).** See [docs/perf_investigations/skip_fixpoint_normalize.md](docs/perf_investigations/skip_fixpoint_normalize.md). Early return when `fixpoint_watermark >= next_cid`. U=64/100, 0.35% — Arc::make_mut is O(1) when refcount=1, empty-agenda solve_to_fixpoint returns immediately, so the "skipped" work was already nearly free.
    - **Sub-investigation: skip redundant match_head in apply_rule — ~10.4% improvement.** See [docs/perf_investigations/chr_skip_rematch.md](docs/perf_investigations/chr_skip_rematch.md). Removed redundant `env.reset()` and `match_head` re-matching in `apply_rule_by_id_reuse` — the RVarEnv already has correct bindings from `find_match_by_ids_reuse`. Pure code deletion (net -10 lines). U=92/100 on synth_flip, neutral on even64.
    - **Sub-investigation: hoist read_lock out of match_head — DISCARDED (no improvement).** See [docs/perf_investigations/chr_lock_hoist.md](docs/perf_investigations/chr_lock_hoist.md). Hoisted `terms.read_lock()` acquisition from per-call in `match_head` into `SearchCtx` (acquired once per search). U=52/100 — parking_lot's uncontended read lock is ~10ns, negligible compared to actual pattern matching work. Would matter more under multi-threaded contention.
    - **Sub-investigation: fuse CHR constraint remap + apply_subst — ~1.7% improvement.** See [docs/perf_investigations/fuse_chr_constraint_ops.md](docs/perf_investigations/fuse_chr_constraint_ops.md). Fused `remap_constraint_vars` + `apply_subst` for b-side constraint into single operation (one ChrStateData clone instead of two). Also fixed self.clone() + Arc::make_mut double-clone pattern in apply_subst and remap_vars. U=75/100.
    - **Sub-investigation: CHR duplicate-argument precheck — DISCARDED (no improvement).** See [docs/perf_investigations/chr_duparg_precheck.md](docs/perf_investigations/chr_duparg_precheck.md). Added precheck in normalize_owned to skip fixpoint when no rule can fire based on per-predicate arg indexes. U=34/100, -1.05% — precheck duplicated work already handled by IndexedTriggers dispatch. Only single-head rules exist in treecalc_synth_flip.
    - **Sub-investigation: selective dirty enqueue — DISCARDED (optimization target never fires).** See [docs/perf_investigations/selective_dirty_enqueue.md](docs/perf_investigations/selective_dirty_enqueue.md). Tracked which CInstances had args changed by apply_subst_to_data, to only re-enqueue dirty ones. U=22/100, -1.75% — instrumentation revealed every watermark==0 entry has zero alive constraints. Constraints consumed immediately by simplification rules; the args_changed branch never fires.
    - **Sub-investigation: per-instance ground flag — DISCARDED (2.6% regression).** See [docs/perf_investigations/instance_ground_flag.md](docs/perf_investigations/instance_ground_flag.md). Added `all_ground: bool` to CInstance to skip apply_subst for ground instances. U=17/100, -2.6% — redundant with existing per-TermId ground bit check in apply_subst; 1-arg instances make the flag overhead exceed savings.
    - **Sub-investigation: specialize solve_to_fixpoint for single-head simplification — ~7.1% improvement.** See [docs/perf_investigations/inline_chr_single_head.md](docs/perf_investigations/inline_chr_single_head.md). Added `all_single_head_simplification` flag to ChrProgram. When set, uses inline loop eliminating Vec allocations, SearchCtx, search_steps_inner recursion, and propagation token handling. U=100/100 (complete separation), neutral on secondary.
    - **Sub-investigation: pre-flatten CHR body instructions — DISCARDED (no improvement).** See [docs/perf_investigations/flat_body_exec.md](docs/perf_investigations/flat_body_exec.md). Pre-flattened BodyInstr into contiguous FlatBodyOp arrays (paralleling flat_chr_match). U=47/100, 0.10% — SmallVec<[TermId; 8]> is already stack-allocated, ArgExpr enum dispatch is branch-predicted, body execution is not the bottleneck.
    - **Sub-investigation: fuse apply_subst + combine_owned — DISCARDED (1.4% regression).** See [docs/perf_investigations/combine_apply_fuse.md](docs/perf_investigations/combine_apply_fuse.md). Fused ChrState::apply_subst + remap_and_apply_subst + combine_owned into single `combine_with_substs` to eliminate one ChrStateData clone. U=24/100, -1.37% — Arc's COW mechanism already makes intermediate clones free (refcount=1 after apply_subst), so fusing adds branching overhead without clone savings.
    - **Sub-investigation: memoized batch apply_subst for ChrState — DISCARDED (17.6% regression).** See [docs/perf_investigations/batch_subst_memo.md](docs/perf_investigations/batch_subst_memo.md). Added FxHashMap subtree memoization shared across all constraint arg apply_subst calls. U=0/100, -17.6% — per-node HashMap overhead (hash + probe + insert) far exceeds baseline per-node cost; apply_subst is already highly optimized (ground bit O(1) skip, all_same reuse, lock-free access). Subtree sharing in this workload is insufficient to amortize the memoization cost.
    - **Sub-investigation: contiguous CInstance args buffer — ~3.65% improvement.** See [docs/perf_investigations/compact_cinstance.md](docs/perf_investigations/compact_cinstance.md). Replaced per-CInstance `SmallVec<[TermId; 4]>` with a contiguous `Vec<TermId>` args buffer in ChrStore. CInstance shrinks from ~48B to ~16B. ChrStateData::clone cost reduced (one contiguous memcpy vs N SmallVec clones), cache locality improved for apply_subst_to_data traversal. U=100/100 (complete separation), neutral on secondary.
    - **Sub-investigation: dense Vec-based CHR index — DISCARDED (no improvement).** See [docs/perf_investigations/dense_chr_index.md](docs/perf_investigations/dense_chr_index.md). Replaced HashMap<FuncId, Vec<_>> with Vec<Vec<_>> in IndexedTriggers and IndexData::ArgTopFunctor. U=38/100, -0.62% — the 5.08% HashMap::get_inner is dominated by term store hash-consing, not CHR index lookups. CHR indexes have few entries per predicate (5 functors), making HashMap fast enough.
    - **Sub-investigation: Arc-wrap PredStore — DISCARDED (no improvement).** See [docs/perf_investigations/arc_predstore.md](docs/perf_investigations/arc_predstore.md). Arc-wrapped `Vec<PredStore>` in ChrStore to avoid deep-cloning PredStore HashMaps. U=62/100, 0.64% — ChrStateData is typically owned (refcount=1), so Arc::make_mut still deep-clones. PredStore portion of the 1.82% ChrStateData::clone is minor after compact_cinstance.
    - **Sub-investigation: skip PredStore index construction — ~6.2% improvement.** See [docs/perf_investigations/skip_chr_indexes.md](docs/perf_investigations/skip_chr_indexes.md). PredStore indexes are only used for join steps in multi-head rules. When `all_single_head_simplification` is true, skipping rebuild_indexes + PredStore::insert eliminates pure waste. U=85/100, exceeds 2.8% estimate due to HashMap allocation costs and cache pressure from unused index data.
    - **Sub-investigation: inline constraint matching before CHR store — ~23.0% improvement.** See [docs/perf_investigations/match_before_store.md](docs/perf_investigations/match_before_store.md). In single-head simplification, try matching newly created constraints against rules BEFORE adding to ChrStore. Matched constraints are consumed immediately via recursive DFS execution, bypassing store/agenda roundtrip entirely. Eliminates add_chr, agenda push/pop, store lookup, mark_dead for all matched constraints. U=100/100 (complete separation). Far exceeded 2-4% estimate due to compounding cache effects and DFS locality.
    - **Sub-investigation: iterative DFS body execution — DISCARDED (10% regression).** See [docs/perf_investigations/iterative_body_dfs.md](docs/perf_investigations/iterative_body_dfs.md). Attempted to convert recursive exec_body_inline to iterative DFS with explicit frame stack and RVarEnv pooling. U=0/100. Stack frames are nearly free, mimalloc makes RVarEnv::new O(1), Vec-indexing indirection adds overhead, and the compiler loses inlining optimizations.
    - **Sub-investigation: compact ChrStore after solve_to_fixpoint — DISCARDED (no opportunity).** See [docs/perf_investigations/store_compaction.md](docs/perf_investigations/store_compaction.md). Instrumentation revealed 82% of normalize_owned calls operate on empty stores (alive=0, dead=0). Remaining 18% have at most 1 dead entry. match_before_store already eliminated dead-entry accumulation.
    - ~~**Sub-investigation: SmallVec in instantiate_pat — DISCARDED (not significant).**~~ **Superseded by stacked_micro_opts below.** See [docs/perf_investigations/reuse_pat_vecs.md](docs/perf_investigations/reuse_pat_vecs.md). Replaced Vec with SmallVec<8> for stack and output in instantiate_pat to eliminate heap allocation. U=72/100 then 66/100 — consistent ~2-3% median improvement but below significance threshold due to high benchmark variance. Most body args are ArgExpr::RVar (O(1) lookup), so Pat-path allocation is infrequent.
    - **Sub-investigation: stacked micro-optimizations — ~3.7% improvement.** See [docs/perf_investigations/stacked_micro_opts.md](docs/perf_investigations/stacked_micro_opts.md). Combined three individually sub-threshold micro-optimizations: SmallVec in instantiate_pat, ground pre-check in apply_subst_to_data, and #[inline(always)] on match_flat_ops/match_head_direct. U=97/100 (p < 0.001). Confirms stacking hypothesis — individually borderline changes produce clearly significant cumulative effect.
        - **Sub-sub-investigation: stacked micro-optimizations round 2 — DISCARDED (not significant).** See [docs/perf_investigations/stacked_micro_opts_2.md](docs/perf_investigations/stacked_micro_opts_2.md). Stacked #[inline(always)] on resolve_var_chain_unlocked, SmallVec for compose indices, cached NF root functors. U=70/100, 1.73% — targets less hot paths than R44's stack; individual effects too small to accumulate past significance threshold.
        - **Sub-sub-investigation: SmallVec for Subst bindings — DISCARDED (not significant).** See [docs/perf_investigations/subst_smallvec.md](docs/perf_investigations/subst_smallvec.md). SmallVec<[Option<TermId>; 16]> for Subst::bindings to avoid heap allocation per compose. U=69/100, 1.1% — mimalloc already very efficient; 64K eliminated mallocs save only ~1ms.
        - **Sub-sub-investigation: mega-stack (all R46 micro-opts combined) — DISCARDED (not significant).** See [docs/perf_investigations/mega_stack.md](docs/perf_investigations/mega_stack.md). Combined all 4 R46 changes (inline resolve_var_chain, SmallVec compose indices, cached root functors, SmallVec Subst). U=61/100, 1.05% — changes interfere; larger NfInner and 136-byte Subst hurt cache locality, negating allocation savings.
        - **Sub-sub-investigation: mega-stack plus — DISCARDED (regression).** See [docs/perf_investigations/mega_stack_plus.md](docs/perf_investigations/mega_stack_plus.md). Subset of mega-stack changes (without cached root functors). U=36/100, -1.08% — confirms SmallVec<[Option<TermId>; 16]> for Subst is counterproductive due to 5× struct size increase causing cache pressure.
    - **Sub-investigation: Profile-Guided Optimization (PGO) — DISCARDED (secondary regression).** See [docs/perf_investigations/pgo_build.md](docs/perf_investigations/pgo_build.md). LLVM PGO produced 14.0% improvement on treecalc_synth_flip (U=100/100, complete separation) but 3.2% regression on recursive_even_backward_first64 (U=13/100). PGO optimizes hot paths at cost of cold paths; training was dominated by compose-heavy workload.
        - **Sub-sub-investigation: multi-workload PGO — DISCARDED (primary regression).** See [docs/perf_investigations/multi_pgo.md](docs/perf_investigations/multi_pgo.md). Balanced training (3x each workload) produced 3.9% regression on primary (U=12/100). Diluted profile data conflicted with LTO's static analysis, making combined decisions worse than LTO alone. PGO appears fundamentally incompatible with multi-workload optimization for this codebase.
    - **Sub-investigation: skip constraint apply_subst when subst doesn't affect constraint vars — DISCARDED (no improvement).** See [docs/perf_investigations/constraint_subst_shortcircuit.md](docs/perf_investigations/constraint_subst_shortcircuit.md). Added Bloom-filter bitmask check (Subst::bound_var_mask vs constraint arg var mask) to skip apply_subst when no overlap. U=50/100 — compound non-ground args prevent cheap detection, and variable overlap is common in practice.
    - **Sub-investigation: thread-local normalize_owned cache — ~33.7% improvement.** See [docs/perf_investigations/constraint_normalize_cache.md](docs/perf_investigations/constraint_normalize_cache.md). Cache normalize_owned results by 64-bit multiplicative hash of pre-normalization ChrState. 79.2% of calls (205K out of 259K) were duplicates from search tree branching. Thread-local HashMap with TermStore generation-based invalidation. U=100/100 (complete separation), neutral on secondary.
    - **Sub-investigation: empty-store shortcircuit for normalize_owned — DISCARDED (1.3% regression).** See [docs/perf_investigations/normalize_fast_path.md](docs/perf_investigations/normalize_fast_path.md). Early return when alive_count==0 and builtins empty, before hash+cache. U=23/100 — branch predictor already handles the empty hash loop perfectly, and the cache deterministically hits for empty stores. Added branch costs more than it saves.
    - **Sub-investigation: order-independent (commutative) hash for normalize_owned cache — ~76.1% improvement.** See [docs/perf_investigations/normalize_commutative_hash.md](docs/perf_investigations/normalize_commutative_hash.md). The multiplicative hash chain was order-dependent: two ChrStates with identical alive constraints at different inst Vec positions produced different hashes. This happened naturally after combine_owned with different operand orderings (And fairness rotation). Replaced with commutative wrapping_add of per-constraint hashes. Cache hit rate increased dramatically — steps dropped 41% (4978→2922), compose operations dropped 77% (278K→64K). U=100/100 (complete separation), neutral on secondary.
        - **Sub-sub-investigation: incremental hash maintenance in ChrStore — DISCARDED (not significant).** See [docs/perf_investigations/incremental_constraint_hash.md](docs/perf_investigations/incremental_constraint_hash.md). Maintained `constraints_hash` field incrementally at all mutation sites (add_chr, mark_dead, apply_subst_to_data, combine). U=62/100 then 46/100 — apply_subst_to_data requires full recompute (all args change), so the hash walk is just shifted from normalize_owned, with no net reduction in work.
    - **Sub-investigation: eliminate token storage for single-head simplification — ~3.5% improvement.** See [docs/perf_investigations/chrstate_lean_tokens.md](docs/perf_investigations/chrstate_lean_tokens.md). Added `TokenStore::empty()` with zero-capacity Vec for programs with `all_single_head_simplification = true`. Eliminates N empty HashSet allocations per ChrStateData create/clone/drop cycle. U=82/100, neutral on secondary.
    - **Sub-investigation: skip constraint ops when all args ground — ~1.1% improvement.** See [docs/perf_investigations/constraint_ground_skip.md](docs/perf_investigations/constraint_ground_skip.md). Added `all_args_ground` flag to ChrStateData. When all alive constraint args have the ground bit set and builtins are empty, apply_subst/remap_vars/remap_and_apply_subst skip the ChrStateData clone + arg walk entirely and return a cheap Arc refcount bump. U=100/100 (complete separation, CV<0.25%). Also improved secondary (recursive_even_backward_first64) by 5.47% (U=92).
    - **Sub-investigation: fuse constraint apply_subst + combine + normalize — DISCARDED (not significant).** See [docs/perf_investigations/fuse_constraint_compose.md](docs/perf_investigations/fuse_constraint_compose.md). Fused the 4-step constraint pipeline in compose_nf into a single `compose_constraint` method. Eliminates 1 ChrStateData clone for the (Some, Some) case. U=60/100, ~1.9% — savings per-call are tiny (stores have at most ~19 entries), and the (Some, Some) case is less common than expected.
    - **Sub-investigation: cache full constraint pipeline by (constraint_ptr, subst_hash) — DISCARDED (1.6% regression).** See [docs/perf_investigations/pre_constraint_cache.md](docs/perf_investigations/pre_constraint_cache.md). Thread-local LRU cache for the entire constraint pipeline (apply_subst + combine + normalize) keyed by Arc pointer identity and substitution hash. U=23/100 — extremely low hit rate because substitutions are unique per compose attempt and constraint Arc pointers change after every normalize_owned. Cache key computation overhead (hashing, TLS access) paid on every call with no payoff.
    - **Sub-investigation: speculative normalize cache probe — DISCARDED (3.8% regression).** See [docs/perf_investigations/speculative_normalize_probe.md](docs/perf_investigations/speculative_normalize_probe.md). Compute normalize_owned hash speculatively (without cloning ChrStateData) before constraint pipeline, check cache on hit to skip clone+combine+solver. U=2/100 — the speculative hash requires per-arg apply_subst calls (same work as the full pipeline), so savings from skipping clones are insufficient. Miss penalty (double arg walk) outweighs hit savings.
        - **Sub-sub-investigation: speculative probe via variable chain resolution — DISCARDED (1.9% regression).** See [docs/perf_investigations/lazy_subst_closures.md](docs/perf_investigations/lazy_subst_closures.md). Attempted lighter-weight speculative probe using `resolve_var_chain_unlocked` (cheap pointer chasing) instead of `apply_subst` per-arg. U=10/100, -1.9% — 98.6% bail rate because constraint args resolve to non-ground compound terms that cannot be cheaply hashed. Maximum potential savings only ~2% even with perfect hit rate. This target appears exhausted: two approaches have failed, and the remaining headroom is below the measurement threshold.
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
    - **Sub-investigation: compose failure cache — DISCARDED (1.2% regression).** See [docs/perf_investigations/compose_fail_cache.md](docs/perf_investigations/compose_fail_cache.md). Cached failed (a, b) NF pairs by hash to skip recomputation. The 21% duplication rate was driven by `recursive_add_*` cases; `treecalc_synth_flip` has 0% compose duplication, making every cache lookup pure overhead.
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
