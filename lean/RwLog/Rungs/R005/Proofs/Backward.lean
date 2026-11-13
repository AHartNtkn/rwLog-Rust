/-
# R004 on the mirror image of `chain k`

The mirror image of `chain k` is `(((c -> $x ; unbit) ; unbit) ; …) ; unbit`,
where `unbit` is the choice between the two unwrappers. Its first span forgets
everything, so each of its `2 ^ (k + 1)` products is `c -> $x`.

R004's race on it is won within 49 times the cost of R003's shared evaluation
(the two race bounds). The shared evaluation works from the left and finds the
one span `c -> $x` at every stage; `c -> $x` leaves no restriction to its
right, so the choice after it is evaluated once and looked up at every stage
above. Its cost is cubic in `k` (`shared_mir`): the look-up at stage `j`
passes the `j` entries of the stages below, each compared by its size.

The race may return the walk's answer instead, which repeats `c -> $x` once
for each product. The walk spends at least 15 ticks on each product
(`onDemand_mir`), and it wins only when it costs at most twice the shared
evaluation, so it never wins from `k = 7` on and the race never returns more
than 128 copies (`unfolder_mir`). The root table keeps one of them
(`fresh_copies`) and the first round emits it (`round_first_val`).

The first round costs at most `firstBound k`, which is
`98 k³ + 686 k² + 3010 k + 133650`; the constant is what comparing 128 copies
with each other would cost. That is below `mirrorFirst k` (`firstBound_le`),
which is obligation `r004_mirror`.
-/
import RwLog.Rungs.R005.Family
import RwLog.Rungs.R004.Proofs.Separation.Run
import Mathlib.Tactic.Ring

namespace RwLog

namespace R005

namespace Mirror

open Cost R000 R001

/-! ## The spans -/

/-- `c -> $x`, as it is written in the query. -/
abbrev fs : Span := ⟨.sym "c", .var 0, []⟩

/-- `c -> $x`, as a composition returns it: the one answer. -/
abbrev cx : Span := ⟨.sym "c", .var 1, []⟩

/-- The two unwrappers. -/
abbrev u0 : Span := ⟨.app (.sym "0") (.var 0), .var 0, []⟩
abbrev u1 : Span := ⟨.app (.sym "1") (.var 0), .var 0, []⟩

/-- `c -> $x`, either way. -/
def Hd (s : Span) : Prop := s = fs ∨ s = cx

/-- One of the two unwrappers. -/
def Un (s : Span) : Prop := s = u0 ∨ s = u1

theorem size_hd {s : Span} (h : Hd s) : s.size = 2 := by
  rcases h with rfl | rfl <;> simp [Span.size, Store.size, Term.size]

theorem size_un {s : Span} (h : Un s) : s.size = 4 := by
  rcases h with rfl | rfl <;> simp [Span.size, Store.size, Term.size]

/-- `c -> $x` followed by an unwrapper is `c -> $x`. -/
theorem compose_hd {a b : Span} (ha : Hd a) (hb : Un b) : a.compose b = some cx := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    simp [Span.compose, Pat.left, Pat.right, Term.rename, solve, Eqns.subst, finish, RwLog.extend,
      Term.single, enc, Equiv.natSumNatEquivNat, Term.vars]

theorem chain_hd {a b : Span} (ha : Hd a) (hb : Un b) : (Span.chain [a, b]).isSome = true := by
  simp [Span.chain, compose_hd ha hb]

/-- `c -> $x` leaves no restriction to its right. -/
theorem bound_hd {a : Span} (ha : Hd a) : bound a.rightIface = none := by
  rcases ha with rfl | rfl <;> decide

theorem covers_cx : cx.covers? cx = true := by decide

theorem live_cx : Tabled.live [] cx = ⟨[cx], 3⟩ := by
  refine Cost.ext ?_ ?_
  · simp [Tabled.live, Charged.simplify, Theory.simplify, Theory.simplifyWithin,
      Theory.refutes?, Theory.firings, Store.varCount]
  · simp [Tabled.live, Charged.simplify, Theory.simplifyCharge, Theory.refutes?,
      Theory.firings, Store.varCount, R003.Sep.saturate_nil, Theory.saturateWork_nil,
      Theory.firingsWork_nil, Theory.size, Span.size, Store.size, Term.size]

/-! ## The expressions -/

/-- A choice between the two unwrappers: the mirror image of `bit`. -/
abbrev unbit : Rel := .or (.span u0) (.span u1)

/-- What stands before the last choice of the mirror image of `chain k`. -/
def pre : Nat → Rel
  | 0 => .span fs
  | j + 1 => .seq (pre j) unbit

/-- The mirror image of `chain k`: `(((c -> $x ; unbit) ; unbit) ; …) ; unbit`. -/
abbrev mir (k : Nat) : Rel := .seq (pre k) unbit

theorem dual_chain : ∀ k, (chain k).dual = mir k
  | 0 => rfl
  | k + 1 => by
    have ih := dual_chain k
    simp only [chain, RelOf.dual, ih]
    rfl

theorem canon_unbit : canon unbit = unbit := by
  have h : compare "0" "1" = Ordering.lt := by decide
  simp [canon, orBranches, sortedBranches, relCmp, spanCmp, patCmp, List.eraseDups_cons, mkOr, h,
    listCmp]

theorem canon_pre : ∀ k, canon (pre k) = pre k
  | 0 => rfl
  | k + 1 => by rw [pre, canon, canon_pre k, canon_unbit]

theorem canon_mir (k : Nat) : canon (mir k) = mir k := canon_pre (k + 1)

theorem size_unbit : unbit.size = 11 := by simp [RelOf.size, Span.size, Store.size, Term.size]

theorem size_pre : ∀ k, (pre k).size = 12 * k + 3
  | 0 => by simp [pre, RelOf.size, Span.size, Store.size, Term.size]
  | k + 1 => by rw [pre, RelOf.size, size_pre k, size_unbit]; omega

theorem size_mir (k : Nat) : (mir k).size = 12 * k + 15 :=
  (size_pre (k + 1)).trans (by omega)

theorem pre_ne_unbit : ∀ k, pre k ≠ unbit
  | 0 => by simp [pre]
  | k + 1 => by simp [pre]

theorem mir_ne_unbit (k : Nat) : mir k ≠ unbit := pre_ne_unbit (k + 1)

theorem pre_ne_mir (k : Nat) : pre k ≠ mir k := fun h => by
  have := congrArg RelOf.size h
  rw [size_pre, size_mir] at this
  omega

/-- The goals of the first round, with no boundaries. -/
abbrev gM (k : Nat) : Goal := ⟨none, mir k, none⟩
abbrev gP (k : Nat) : Goal := ⟨none, pre k, none⟩
abbrev gU : Goal := ⟨none, unbit, none⟩

/-- The program of the family, mirrored: no definitions and no theory. -/
abbrev P0 : Program := ⟨[], []⟩

/-! ## The shared evaluation

The shared evaluation of `mir j` evaluates `pre j` with nothing to its left,
which leaves the one span `c -> $x`, and then the choice between the two
unwrappers after it. `c -> $x` restricts nothing to its right, so the choice
is evaluated with no interface at every level: once, at the innermost level,
and looked up at every level above. The memo holds one entry for each level
below, in front of the entry of the choice, so the look-up at level `j` passes
`j` entries, each compared by the size of its expression. The evaluation is
cubic. -/

open R003 in
/-- The summary of the choice: the two unwrappers. -/
abbrev G0 : R003.Summary := ⟨[u0, u1], []⟩

/-- The summary of every level: `c -> $x`. -/
abbrev Gc : R003.Summary := ⟨[cx], []⟩

abbrev kU (d : Nat) : R003.Key := ⟨false, unbit, d, none⟩
abbrev kM (d j : Nat) : R003.Key := ⟨false, mir j, d, none⟩

/-- The memo once `mir j` has been evaluated: its levels, the last one first,
and the choice. -/
def mu (d : Nat) : Nat → R003.Memo
  | 0 => [(kM d 0, Gc), (kU d, G0)]
  | j + 1 => (kM d (j + 1), Gc) :: mu d j

theorem sameKey_none (d : Nat) (e : Rel) :
    Costs (R003.sameKey ⟨false, e, d, none⟩ ⟨false, e, d, none⟩) true (2 * e.size + 1) := by
  refine ⟨?_, ?_⟩
  · simp [R003.sameKey, R003.sameCtx]
  · simp [R003.sameKey, R003.sameCtx]; omega

/-- The choice is found behind the levels. -/
theorem lookup_mu (d : Nat) :
    ∀ j, Costs (R003.lookup (mu d j) (kU d)) (some G0) (6 * (j * j) + 33 * j + 50)
  | 0 => by
    have h := R003.Sep.sameKey_ne (d := d) none none (mir_ne_unbit 0)
    refine (R003.Sep.lookup_miss h (R003.Sep.lookup_hit (sameKey_none d unbit))).mono ?_
    rw [size_mir, size_unbit]
  | j + 1 => by
    have h := R003.Sep.sameKey_ne (d := d) none none (mir_ne_unbit (j + 1))
    refine (R003.Sep.lookup_miss h (lookup_mu d j)).mono ?_
    have e : (j + 1) * (j + 1) = j * j + 2 * j + 1 := by ring
    rw [size_mir, size_unbit, e]; omega

theorem eval_span_none (d : Nat) (s : Span) (m : R003.Memo) :
    Costs (R003.eval P0 d false (.span s) none m) (⟨[s], []⟩, m) 1 := by
  rw [R003.eval]
  refine ⟨?_, ?_⟩ <;> simp [R003.alive]

theorem addSpan_u0_u1 : Costs (foldL R003.addSpan [u0] [u1]) [u0, u1] 8 := by
  refine ⟨?_, ?_⟩ <;> simp [foldL, R003.addSpan, anyL, Span.size, Store.size, Term.size]

/-- The choice when it is not in the memo: both unwrappers. -/
theorem eval_unbit_miss (d : Nat) {m : R003.Memo} {cl : Nat}
    (h : Costs (R003.lookup m (kU d)) none cl) :
    Costs (R003.eval P0 d false unbit none m) (G0, (kU d, G0) :: m) (cl + 11) := by
  rw [R003.eval]
  refine Costs.mono (c := cl + (1 + (1 + (1 + (8 + (0 + 0)))))) ?_ (by omega)
  refine R003.Sep.memo_miss h ?_
  refine Costs.bind (Costs.tick 1) ?_
  refine Costs.bind (eval_span_none d u0 m) ?_
  refine Costs.bind (eval_span_none d u1 m) ?_
  refine Costs.bind addSpan_u0_u1 ?_
  refine Costs.bind (v := []) ⟨rfl, le_rfl⟩ ?_
  exact Costs.pure _

/-- The choice when it is in the memo. -/
theorem eval_unbit_hit (d : Nat) {m : R003.Memo} {cl : Nat}
    (h : Costs (R003.lookup m (kU d)) (some G0) cl) :
    Costs (R003.eval P0 d false unbit none m) (G0, m) cl := by
  rw [R003.eval]
  exact R003.Sep.memo_hit _ h

theorem composes_hd {x : Span} (hx : Hd x) :
    Costs (filterMapL (fun y => Charged.compose x y) [u0, u1]) [cx, cx] 16 := by
  have h0 := compose_hd hx (Or.inl rfl : Un u0)
  have h1 := compose_hd hx (Or.inr rfl : Un u1)
  refine ⟨?_, ?_⟩
  · simp [filterMapL, Charged.compose, h0, h1]
  · have hs := size_hd hx
    simp only [Span.size, Store.size] at hs
    simp [filterMapL, Charged.compose, h0, h1, Charged.outSize, Span.size, Store.size, Term.size]
    omega

theorem addSpan_cx_cx : Costs (foldL R003.addSpan [] [cx, cx]) [cx] 4 := by
  refine ⟨?_, ?_⟩ <;> simp [foldL, R003.addSpan, anyL, Span.size, Store.size, Term.size]

/-- A level: what stands before the choice leaves `c -> $x`, and the choice
follows it with no interface. -/
theorem eval_seq (d : Nat) {a : Rel} {x : Span} (hx : Hd x) {m1 m2 : R003.Memo} {c1 c2 : Nat}
    (h1 : Costs (R003.eval P0 d false a none []) (⟨[x], []⟩, m1) c1)
    (h2 : Costs (R003.eval P0 d false unbit none m1) (G0, m2) c2) :
    Costs (R003.eval P0 d false (.seq a unbit) none [])
      (Gc, (⟨false, .seq a unbit, d, none⟩, Gc) :: m2) (c1 + c2 + 23) := by
  rw [R003.eval]
  refine Costs.mono (c := 0 + (1 + (c1 + ((2 + (c2 + (16 + (4 + (0 + 0))))) + 0 + (0 + 0))))) ?_
    (by omega)
  refine R003.Sep.memo_miss (R003.Sep.lookup_nil _) ?_
  refine Costs.bind (Costs.tick 1) ?_
  refine Costs.bind h1 ?_
  unfold R003.seqSummary
  refine Costs.bind (v := ([cx], [], m2)) ?_ ?_
  · simp only [foldL]
    refine Costs.bind ?_ (Costs.pure _)
    unfold R003.afterSpan
    refine Costs.bind (v := none) ?_ ?_
    · refine ⟨?_, ?_⟩
      · simp [R003.extend, bound_hd hx]
      · simp [R003.extend, size_hd hx]
    refine Costs.bind h2 ?_
    refine Costs.bind (composes_hd hx) ?_
    refine Costs.bind addSpan_cx_cx ?_
    refine Costs.bind (v := []) ⟨rfl, le_rfl⟩ ?_
    exact Costs.pure _
  · refine Costs.bind (v := ([cx], [], m2)) ⟨rfl, le_rfl⟩ ?_
    exact Costs.pure _

/-- What the evaluation of `mir j` costs at most. -/
def evalBound (j : Nat) : Nat := 2 * j ^ 3 + 14 * j ^ 2 + 58 * j + 35

/-- The evaluation of `mir j` with nothing to its left and an empty memo. -/
theorem eval_mir (d : Nat) :
    ∀ j, Costs (R003.eval P0 d false (mir j) none []) (Gc, mu d j) (evalBound j)
  | 0 => (eval_seq d (Or.inl rfl) (eval_span_none d fs [])
      (eval_unbit_miss d (R003.Sep.lookup_nil _))).mono (by unfold evalBound; omega)
  | j + 1 => by
    refine (eval_seq d (Or.inr rfl) (eval_mir d j) (eval_unbit_hit d (lookup_mu d j))).mono ?_
    have e : evalBound (j + 1) = evalBound j + (6 * (j * j) + 34 * j + 74) := by
      unfold evalBound; ring
    omega

/-- What the shared evaluation of `mir j` costs at most. -/
def sharedBound (j : Nat) : Nat := evalBound j + 3

/-- The shared evaluation of `mir j`: final, the one answer, cubic. -/
theorem shared_mir (d j : Nat) :
    Costs (R003.shared P0 d (gM j)) (true, [cx]) (sharedBound j) := by
  have hrel : (gM j).rel = mir j := rfl
  unfold R003.shared sharedBound
  rw [hrel]
  refine Costs.mono (c := evalBound j + (3 + (0 + 0))) ?_ (by omega)
  refine Costs.bind (eval_mir d j) ?_
  simp only [List.isEmpty_nil, ↓reduceIte]
  refine Costs.bind (v := [cx]) ?_ ?_
  · refine ⟨?_, ?_⟩ <;> simp [flatMapL, live_cx]
  · refine Costs.bind (v := [cx]) ⟨rfl, le_rfl⟩ ?_
    exact Costs.pure _

/-! ## The walk

R002's walk reads `mir j` from the left too, but it follows each product
separately: every choice doubles the products, and all `2 ^ (j + 1)` of them
reach the top. The walk returns the one answer that many times, and spends
at least 15 ticks on each. -/

open R002 in
/-- What the walk needs of the continuation it hands its products to: it
never stops, adds at most `m` products, and spends at least `c`. -/
def Cont (K : List Rel → List (List Rel) → Cost R002.Walk) (m c : Nat) : Prop :=
  ∀ x, Hd x → ∀ acc, (K [.span x] acc).val.1 = false ∧
    (K [.span x] acc).val.2.length ≤ acc.length + m ∧ c ≤ (K [.span x] acc).ticks

/-- Joining `c -> $x` with an unwrapper composes them. -/
theorem joinSeq_hd {x u : Span} (hx : Hd x) (hu : Un u) :
    R002.joinSeq [.span x] [.span u] = ⟨some [.span cx], 8⟩ := by
  have hc := compose_hd hx hu
  refine Cost.ext ?_ ?_
  · simp [R002.joinSeq, Charged.compose, hc]
  · simp [R002.joinSeq, Charged.compose, hc, Charged.outSize, size_hd hx, size_un hu,
      size_hd (Or.inr rfl : Hd cx)]

/-- The continuation of what stands before a choice: join, and hand on. -/
abbrev joinK (K : List Rel → List (List Rel) → Cost R002.Walk) (p : List Rel) :
    List Rel → List (List Rel) → Cost R002.Walk := fun q acc => do
  let r ← R002.joinSeq p q
  match r with
  | none => pure (false, acc)
  | some r => do
    let a ← R002.aliveR r []
    if a then K r acc else pure (false, acc)

/-- The walk of an unwrapper after `c -> $x`. -/
theorem walk_un (d : Nat) {x u : Span} (hx : Hd x) (hu : Un u)
    {K : List Rel → List (List Rel) → Cost R002.Walk} {m c : Nat} (hK : Cont K m c)
    (acc : List (List Rel)) :
    (R002.walk P0 d false (.span u) [x] [] (joinK K [.span x]) acc).val.1 = false ∧
      (R002.walk P0 d false (.span u) [x] [] (joinK K [.span x]) acc).val.2.length ≤
        acc.length + m ∧
      c + 15 ≤ (R002.walk P0 d false (.span u) [x] [] (joinK K [.span x]) acc).ticks := by
  obtain ⟨h1, h2, h3⟩ := hK cx (Or.inr rfl) acc
  have hc := chain_hd hx hu
  rw [R002.walk]
  simp only [Bool.false_eq_true, ↓reduceIte, R002.alive, R002.aliveL, R002.aliveR, R002.headSpan,
    Charged.composable, hc, joinSeq_hd hx hu, bind_val, bind_ticks, tick_ticks, pure_val,
    pure_ticks, List.nil_append, List.cons_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, size_hd hx, size_un hu, h1]
  refine ⟨trivial, h2, ?_⟩
  omega

/-- The walk of the choice after `c -> $x` hands both products on. -/
theorem walk_unbit (d : Nat) {x : Span} (hx : Hd x)
    {K : List Rel → List (List Rel) → Cost R002.Walk} {m c : Nat} (hK : Cont K m c)
    (acc : List (List Rel)) :
    (R002.walk P0 d false unbit [x] [] (joinK K [.span x]) acc).val.1 = false ∧
      (R002.walk P0 d false unbit [x] [] (joinK K [.span x]) acc).val.2.length ≤
        acc.length + 2 * m ∧
      2 * c + 31 ≤ (R002.walk P0 d false unbit [x] [] (joinK K [.span x]) acc).ticks := by
  obtain ⟨a1, a2, a3⟩ := walk_un d hx (Or.inl rfl : Un u0) hK acc
  obtain ⟨b1, b2, b3⟩ := walk_un d hx (Or.inr rfl : Un u1) hK
    (R002.walk P0 d false (.span u0) [x] [] (joinK K [.span x]) acc).val.2
  rw [R002.walk]
  simp only [bind_val, bind_ticks, tick_ticks, a1, Bool.false_eq_true, ↓reduceIte]
  exact ⟨b1, by omega, by omega⟩

/-- What stands before a choice hands `c -> $x` to the walk of the choice. -/
theorem cont_choice (d : Nat) {K : List Rel → List (List Rel) → Cost R002.Walk} {m c : Nat}
    (hK : Cont K m c) :
    Cont (fun p acc => R002.walk P0 d false unbit (R002.leftAfter [] p) [] (joinK K p) acc)
      (2 * m) (2 * c + 31) := by
  intro x hx acc
  have := walk_unbit d hx hK acc
  simpa [R002.leftAfter] using this

theorem rightOf_unbit : R002.rightOf false unbit [] = [] := by
  simp [R002.rightOf, R002.staticFirst]

/-- The walk of `pre j` with nothing around it: it does not stop, hands on
`2 ^ j` products, and spends at least `2 ^ j (c + 15)` when each product costs
`c` at the top. -/
theorem walk_pre (d : Nat) : ∀ (j : Nat) {K : List Rel → List (List Rel) → Cost R002.Walk}
    {m c : Nat}, Cont K m c → ∀ acc : List (List Rel),
    (R002.walk P0 d false (pre j) [] [] K acc).val.1 = false ∧
      (R002.walk P0 d false (pre j) [] [] K acc).val.2.length ≤ acc.length + 2 ^ j * m ∧
      2 ^ j * (c + 15) ≤ (R002.walk P0 d false (pre j) [] [] K acc).ticks + 14
  | 0, K, m, c, hK, acc => by
    obtain ⟨h1, h2, h3⟩ := hK fs (Or.inl rfl) acc
    rw [pre, R002.walk]
    simp only [Bool.false_eq_true, ↓reduceIte, R002.alive, R002.aliveL, R002.aliveR, bind_val,
      bind_ticks, tick_ticks, pure_val, pure_ticks, h1]
    refine ⟨trivial, by simpa using h2, ?_⟩
    omega
  | j + 1, K, m, c, hK, acc => by
    obtain ⟨h1, h2, h3⟩ := walk_pre d j (cont_choice d hK) acc
    rw [pre, R002.walk]
    simp only [rightOf_unbit, bind_val, bind_ticks, tick_ticks]
    have e1 : acc.length + 2 ^ j * (2 * m) = acc.length + 2 ^ (j + 1) * m := by ring
    have e2 : 2 ^ (j + 1) * (c + 15) ≤ 2 ^ j * (2 * c + 31 + 15) := by
      have e : 2 ^ (j + 1) * (c + 15) + 2 ^ j * 16 = 2 ^ j * (2 * c + 31 + 15) := by ring
      omega
    exact ⟨h1, le_trans h2 (le_of_eq e1),
      le_trans e2 (le_trans h3 (Nat.add_le_add_right (Nat.le_add_left _ 1) 14))⟩

theorem cont_top : Cont (fun p acc =>
    pure (if (toRel p).calls.isEmpty then (false, acc ++ [p]) else (true, acc))) 1 0 := by
  intro s _ acc
  simp [toRel, RelOf.calls]

/-- The walk on `mir j` returns at most `2 ^ (j + 1)` answers and spends at
least `15` on each. -/
theorem onDemand_mir (d j : Nat) :
    (R002.onDemand P0 d (gM j)).val.2.length ≤ 2 ^ (j + 1) ∧
      2 ^ (j + 1) * 15 ≤ (R002.onDemand P0 d (gM j)).ticks + 14 := by
  obtain ⟨h1, h2, h3⟩ := walk_pre d (j + 1) cont_top []
  have hrel : (gM j).rel = pre (j + 1) := rfl
  simp only [R002.onDemand, hrel, bind_val, bind_ticks, h1, Bool.false_eq_true, ↓reduceIte,
    pure_val, flatMapL_val]
  refine ⟨?_, ?_⟩
  · refine le_trans (R003.Sep.length_flatMap_live _ _) ?_
    refine le_trans (List.length_filterMap_le _ _) ?_
    simpa using h2
  · simp only [Nat.zero_add] at h3
    omega

/-! ## The race

R004's race returns the answer of the walk, of the shared evaluation or of
the evaluation pruned from the right, and costs at most 49 times the shared
evaluation. The last two return `c -> $x` once. The walk returns it once for
each product, but it can only win when it costs at most twice the shared
evaluation, and from `j = 7` on it costs more than that: the race never
returns more than 128 answers. -/

theorem sharedBound_succ (j : Nat) :
    sharedBound (j + 1) = sharedBound j + (6 * (j * j) + 34 * j + 74) := by
  unfold sharedBound evalBound; ring

/-- From `j = 7` on, the walk costs more than twice the shared evaluation. -/
theorem walk_loses : ∀ j, 7 ≤ j → 2 * sharedBound j + 14 < 2 ^ (j + 1) * 15 := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => decide
  | succ j hj ih =>
    have hc : 7 ^ 3 ≤ j ^ 3 := Nat.pow_le_pow_left hj 3
    have hb : 6 * (j * j) + 34 * j + 74 ≤ sharedBound j + 7 := by
      have e : j ^ 2 = j * j := by ring
      unfold sharedBound evalBound
      omega
    have e : 2 ^ (j + 1 + 1) = 2 * 2 ^ (j + 1) := by ring
    rw [sharedBound_succ, e]
    omega

/-- The race on `mir j`: at most 49 times the shared evaluation; final;
copies of `c -> $x`, at least one and at most 128. -/
theorem unfolder_mir (d j : Nat) :
    (R004.unfolder P0 d (gM j)).ticks ≤ 49 * sharedBound j ∧
      (R004.unfolder P0 d (gM j)).val.1 = true ∧
      (R004.unfolder P0 d (gM j)).val.2 ≠ [] ∧
      (∀ x ∈ (R004.unfolder P0 d (gM j)).val.2, x = cx) ∧
      (R004.unfolder P0 d (gM j)).val.2.length ≤ 128 := by
  obtain ⟨sv, st⟩ := shared_mir d j
  obtain ⟨w1, w2⟩ := onDemand_mir d j
  have hsx := R003.shared_exact P0 d (gM j)
  rw [sv] at hsx
  have hfin : R001.unfoldFinal P0 d (gM j) = true := (congrArg Prod.fst hsx).symm
  have hdup : (R001.unfoldAnswers P0 d (gM j)).eraseDups = [cx] := (congrArg Prod.snd hsx).symm
  have hpv : (R004.pruned P0 d (gM j)).val = (true, [cx]) := by
    rw [R004.pruned_exact P0 d (gM j), hfin, hdup]
  have hov : (R002.onDemand P0 d (gM j)).val = (true, R001.unfoldAnswers P0 d (gM j)) := by
    rw [R002.onDemand_exact P0 d (gM j), hfin]
  have hmem : ∀ x, x ∈ R001.unfoldAnswers P0 d (gM j) ↔ x = cx := by
    intro x
    rw [← List.mem_eraseDups, hdup]
    simp
  have hne : R001.unfoldAnswers P0 d (gM j) ≠ [] := by
    intro h
    rw [h] at hdup
    simp at hdup
  refine ⟨?_, ?_⟩
  · have h1 := R004.unfolder_ticks_le P0 d (gM j)
    have h2 := R003.unfolder_ticks P0 d (gM j)
    omega
  · have key : (R004.unfolder P0 d (gM j)).val = (true, [cx]) ∨
        ((R004.unfolder P0 d (gM j)).val = (R002.onDemand P0 d (gM j)).val ∧
          (R002.onDemand P0 d (gM j)).ticks ≤ 2 * (R003.shared P0 d (gM j)).ticks) := by
      rcases R003.Sep.race_cases (R003.unfolder P0 d (gM j)) (R004.pruned P0 d (gM j)) with
        h | ⟨h, -⟩
      · exact Or.inl (h.trans hpv)
      · rcases R003.Sep.race_cases (R002.onDemand P0 d (gM j)) (R003.shared P0 d (gM j)) with
          h' | ⟨h', hle⟩
        · exact Or.inl (h.trans (h'.trans sv))
        · exact Or.inr ⟨h.trans h', hle⟩
    rcases key with h | ⟨h, hle⟩
    · rw [h]; simp
    · rw [h, hov]
      rw [hov] at w1
      refine ⟨rfl, hne, fun x hx => (hmem x).1 hx, le_trans w1 ?_⟩
      have hj : j < 7 := by
        by_contra hj
        have := walk_loses j (by omega)
        omega
      have : 2 ^ (j + 1) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
      omega

/-! ## The fresh answers -/

theorem covers_cost : Charged.covers cx cx = ⟨true, 4⟩ := by
  refine Cost.ext covers_cx ?_
  simp [Charged.covers, Charged.coversWork, matchAllWork, Span.size, Store.size, Term.size]
  split <;> rfl

/-- What the root keeps of copies of `c -> $x`: one. -/
def keep (acc : List Span) (x : Span) : List Span :=
  if acc.any (fun y => y.covers? x) then acc else acc ++ [x]

theorem foldl_keep : ∀ as : List Span, (∀ x ∈ as, x = cx) → as.foldl keep [cx] = [cx]
  | [], _ => rfl
  | a :: as, h => by
    obtain rfl := h a (by simp)
    have e : keep [cx] cx = [cx] := by simp [keep, covers_cx]
    rw [List.foldl_cons, e]
    exact foldl_keep as fun x hx => h x (by simp [hx])

/-- The fresh answers among `n` copies of `c -> $x` for an empty table: one
copy, after every copy has been compared with every other. -/
theorem fresh_copies {as : List Span} (hne : as ≠ []) (hall : ∀ x ∈ as, x = cx) :
    Costs (Tabled.fresh [] as) [cx] (as.length * (as.length * 8) + as.length * 4) := by
  unfold Tabled.fresh
  refine Costs.mono (c := as.length * 0 + (as.length * (as.length * 8 + 0) + as.length * 4)) ?_
    (by simp)
  refine Costs.bind (v := as) ?_ ?_
  · have h := Costs.filterL (f := fun c => do
        let b ← anyL (fun t => Charged.covers t c) ([] : List Span)
        pure !b) (g := fun _ => true) (c := 0) (xs := as)
      (fun x _ => ⟨by simp [anyL], by simp [anyL]⟩)
    simpa using h
  · unfold Tabled.maxima
    refine Costs.bind (v := as) ?_ ?_
    · have h := Costs.filterL (f := fun x => do
          let b ← anyL (fun y => do
            let c ← Charged.covers y x
            if c then do
              let c' ← Charged.covers x y
              pure !c'
            else pure false) as
          pure !b) (g := fun _ => true) (c := as.length * 8 + 0) (xs := as) (by
        intro x hx
        obtain rfl := hall x hx
        refine Costs.bind (v := false) ?_ (Costs.pure _)
        have h := Costs.anyL (f := fun y => do
            let c ← Charged.covers y cx
            if c then do
              let c' ← Charged.covers cx y
              pure !c'
            else pure false) (g := fun _ => false) (c := 8) (xs := as) (by
          intro y hy
          obtain rfl := hall y hy
          refine ⟨?_, ?_⟩ <;> simp [covers_cost])
        have e : (as.any fun _ : Span => false) = false :=
          List.any_eq_false.2 fun _ _ => Bool.false_ne_true
        rw [e] at h
        simpa using h)
      simpa using h
    · obtain ⟨a, as', rfl⟩ := List.exists_cons_of_ne_nil hne
      obtain rfl := hall a (by simp)
      have h := Costs.foldL (f := fun acc x => do
          let b ← anyL (fun y => Charged.covers y x) acc
          pure (if b then acc else acc ++ [x])) (g := keep) (c := 4)
        (fun acc => acc = [] ∨ acc = [cx]) (xs := cx :: as') (b := []) (Or.inl rfl) (by
          intro acc hacc x hx
          obtain rfl := hall x hx
          rcases hacc with rfl | rfl
          · exact ⟨⟨by simp [anyL, keep], by simp [anyL]⟩, Or.inr (by simp [keep])⟩
          · exact ⟨⟨by simp [anyL, keep, covers_cost, covers_cx], by simp [anyL, covers_cost]⟩,
              Or.inr (by simp [keep, covers_cx])⟩)
      have e : (cx :: as').foldl keep [] = [cx] := by
        have e0 : keep [] cx = [cx] := by simp [keep]
        rw [List.foldl_cons, e0]
        exact foldl_keep as' fun x hx => hall x (by simp [hx])
      rw [e] at h
      exact h

/-! ## The first round

The root table is alone. Its race answers with copies of `c -> $x`, of which
the table keeps one, and that one is emitted. The tables of the two halves of
the root do not exist yet, so the strategies that read them find nothing and
ask for them. -/

theorem norm_gM (k : Nat) : (gM k).norm = (false, gM k) := by
  rw [GoalOf.norm, canon_mir, GoalOf.stripConv]
  intro lb a rb h
  cases h

theorem norm_gP (k : Nat) : (gP k).norm = (false, gP k) := by
  rw [GoalOf.norm, canon_pre, GoalOf.stripConv]
  intro lb a rb h
  cases k <;> simp [pre] at h

theorem norm_gU : gU.norm = (false, gU) := by
  rw [GoalOf.norm, canon_unbit, GoalOf.stripConv]
  intro lb a rb h
  cases h

theorem goalSize_gM (k : Nat) : goalSize (gM k) = 12 * k + 15 := by simp [goalSize, size_mir]
theorem goalSize_gP (k : Nat) : goalSize (gP k) = 12 * k + 3 := by simp [goalSize, size_pre]
theorem goalSize_gU : goalSize gU = 11 := by simp [goalSize, size_unbit]

theorem tsame_gM_gP (k : Nat) :
    Tabled.same (gM k) (gP k) = ⟨false, goalSize (gM k) + goalSize (gP k)⟩ := by
  rw [Tabled.same_eq_of_none ⟨rfl, rfl⟩ ⟨rfl, rfl⟩]
  simp [GoalOf.same, (pre_ne_mir k).symm]

theorem tsame_gM_gU (k : Nat) :
    Tabled.same (gM k) gU = ⟨false, goalSize (gM k) + goalSize gU⟩ := by
  rw [Tabled.same_eq_of_none ⟨rfl, rfl⟩ ⟨rfl, rfl⟩]
  simp [GoalOf.same]

theorem tsame_gP_gU (k : Nat) :
    Tabled.same (gP k) gU = ⟨false, goalSize (gP k) + goalSize gU⟩ := by
  rw [Tabled.same_eq_of_none ⟨rfl, rfl⟩ ⟨rfl, rfl⟩]
  simp [GoalOf.same, pre_ne_unbit k]

/-- The first state: the root table alone. -/
abbrev st0 (k : Nat) : R001.State := ⟨P0, [⟨gM k, [], false⟩], false, 0⟩

theorem init_eq (k : Nat) : R004.costed.start (sepFam k).1.dual (sepFam k).2.dual = st0 k := by
  show (Tabled.ofGoal (sepFam k).1.dual ⟨none, (chain k).dual, none⟩).val = _
  rw [dual_chain]
  simp [Tabled.ofGoal, Tabled.norm, norm_gM, sepFam, ProgramOf.dual]

/-- What the first round costs at most. -/
def firstBound (k : Nat) : Nat := 49 * sharedBound k + 168 * k + 131788

/-- What the root's race returns in the first round, and what the root keeps
of it. -/
theorem race_first (k : Nat) : ∃ (as : List Span) (T F : Nat),
    R004.unfolder P0 0 (gM k) = ⟨(true, as), T⟩ ∧ Tabled.fresh [] as = ⟨[cx], F⟩ ∧
      T ≤ 49 * sharedBound k ∧ F ≤ 131584 := by
  obtain ⟨hT, h1, hne, hall, hlen⟩ := unfolder_mir 0 k
  obtain ⟨fv, ft⟩ := fresh_copies hne hall
  refine ⟨_, _, _, Cost.ext (Prod.ext h1 rfl) rfl, Cost.ext fv rfl, hT, le_trans ft ?_⟩
  have hsq := Nat.mul_le_mul hlen (Nat.mul_le_mul_right 8 hlen)
  omega

/-- The first round emits `c -> $x`. -/
theorem round_first_val (k : Nat) : (Tabled.round R004.unfolder (st0 k)).val.2 = [cx] := by
  obtain ⟨as, T, F, hu, hf, -, -⟩ := race_first k
  simp [Tabled.round, mapL, hu, hf, Tabled.produce, Tabled.produceStrategies, seqLeft, seqRight,
    flatMapL, Tabled.answersOf, Tabled.doneOf, Tabled.norm, norm_gP, norm_gU, Tabled.findTable,
    findL, tsame_gM_gP, tsame_gM_gU, tsame_gP_gU, anyL, foldL, Tabled.completing,
    Tabled.gfpFrom, R001.orient]

/-- The first round costs at most `firstBound k`. -/
theorem round_first_ticks (k : Nat) :
    (Tabled.round R004.unfolder (st0 k)).ticks ≤ firstBound k := by
  obtain ⟨as, T, F, hu, hf, hT, hF⟩ := race_first k
  simp [Tabled.round, mapL, hu, hf, Tabled.produce, Tabled.produceStrategies, seqLeft, seqRight,
    flatMapL, Tabled.answersOf, Tabled.doneOf, Tabled.norm, norm_gP, norm_gU, Tabled.findTable,
    findL, tsame_gM_gP, tsame_gM_gU, tsame_gP_gU, anyL, foldL, Tabled.completing,
    Tabled.gfpFrom, R001.orient, goalSize_gM, goalSize_gP, goalSize_gU]
  unfold firstBound
  omega

/-- The first round fits in the allowance of `Family.lean`. -/
theorem firstBound_le (k : Nat) : firstBound k ≤ mirrorFirst k := by
  have e : (k + 2) ^ 3 = k ^ 3 + 6 * k ^ 2 + 12 * k + 8 := by ring
  unfold firstBound sharedBound evalBound mirrorFirst
  rw [e]
  generalize k ^ 3 = c
  generalize k ^ 2 = b
  omega

end Mirror

/-- From the right, R004's first round on the mirror image of `chain k` emits
`c -> $x`, which relates `c` to `z`, and costs at most `mirrorFirst k`. -/
theorem r004_mirror : Obligation.r004_mirror := by
  intro k
  have hv := Mirror.round_first_val k
  have ht := Mirror.round_first_ticks k
  obtain ⟨sv, st⟩ := R003.Sep.step_emit (U := R004.unfolder) (st := Mirror.st0 k) rfl
  rw [hv] at sv
  have e : (R004.costed.step (Mirror.st0 k)).ticks = _ := st
  rw [Mirror.init_eq]
  refine ⟨[Mirror.cx], _, sv, ⟨Mirror.cx, by simp, fun M => ⟨fun _ => .sym "z", rfl, rfl, by simp⟩⟩,
    ?_⟩
  rw [e]
  exact le_trans ht (Mirror.firstBound_le k)

end R005

end RwLog
