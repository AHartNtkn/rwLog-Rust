/-
# The separating family: what R003 pays

R003 answers the unfolding race of the query by the cheaper of R002's walk and
the shared evaluation, and both go through `gen k` before they reach the test
that follows it.

* The walk hands on every one of the `2 ^ (k + 1)` products of `gen k`: a
  chain of wrappers always composes, so none is ruled out by what stands to
  its left, and what stands to its right is read from the expression, which
  says nothing about a choice (`walk_gen`).
* The shared evaluation computes the summary of `gen k`, which lists its
  `2 ^ (k + 1)` different spans, and then continues after each of them
  (`shared_ge`).

A race costs at least what the cheaper of the two costs (`le_race_ticks`), so
R003's first round costs at least `2 ^ k` (`r003_first`).
-/
import RwLog.Rungs.R004.Proofs.Separation.Family
import RwLog.Rungs.R003.Proofs.SharedExact
import RwLog.Rungs.R003.Proofs.Separation.Run
import RwLog.Kernel.Size

namespace RwLog

namespace R004

namespace Sep

open Cost R000 R001 R002

/-! ## The walk -/

/-- The continuation does not stop the walk on a single span. -/
def Cont (K : List Rel → List (List Rel) → Cost Walk) : Prop :=
  ∀ s acc, (K [.span s] acc).val.1 = false

theorem cont_top : Cont (fun p acc =>
    pure (if (toRel p).calls.isEmpty then (false, acc ++ [p]) else (true, acc))) := by
  intro s acc
  simp [toRel, Rel.calls]

/-- The continuation of the first factor of a sequence: join, and hand on. -/
theorem cont_join {K : List Rel → List (List Rel) → Cost Walk} (hK : Cont K) (a : Span)
    (R : List Span) :
    Cont (fun q acc => do
      let r ← R002.joinSeq [.span a] q
      match r with
      | none => pure (false, acc)
      | some r => do
        let x ← aliveR r R
        if x then K r acc else pure (false, acc)) := by
  intro b acc
  have hj : (R002.joinSeq [.span a] [.span b]).val = (a.compose b).map fun c => [Rel.span c] := by
    simp [R002.joinSeq, Charged.compose]
  simp only [bind_val, hj]
  cases a.compose b with
  | none => rfl
  | some c =>
    simp only [Option.map_some, bind_val]
    by_cases h : (aliveR [Rel.span c] R).val = true
    · simp [h, hK c acc]
    · simp [h]

/-- The walk of a span does not stop, whatever stands around it. -/
theorem walk_span_any (s : Span) (L R : List Span)
    {K : List Rel → List (List Rel) → Cost Walk} (hK : Cont K) (acc : List (List Rel)) :
    (walk P0 0 false (.span s) L R K acc).val.1 = false ∧
      1 ≤ (walk P0 0 false (.span s) L R K acc).ticks := by
  rw [walk]
  simp only [Bool.false_eq_true, ↓reduceIte, bind_val, bind_ticks, tick_ticks]
  refine ⟨?_, by omega⟩
  by_cases h : (R002.alive L [Rel.span s] R).val = true
  · simp [h, hK s acc]
  · simp [h]

/-- The walk of a wrapper after a chain of wrappers hands it on. -/
theorem walk_wrap {s : Span} (hs : Wrap s) {L : List Span} (hL : ∀ t ∈ L, Wrap t)
    (K : List Rel → List (List Rel) → Cost Walk) (acc : List (List Rel)) :
    (walk P0 0 false (.span s) L [] K acc).val.1 = (K [.span s] acc).val.1 ∧
      (K [.span s] acc).ticks ≤ (walk P0 0 false (.span s) L [] K acc).ticks := by
  have ha : (R002.alive L [Rel.span s] []).val = true := by
    cases L with
    | nil => simp [R002.alive, aliveL, aliveR]
    | cons a L =>
      have hc : (Span.chain (a :: L ++ [s])).isSome = true := chain_wraps fun t ht => by
        rcases List.mem_append.1 ht with h | h
        · exact hL t h
        · rw [List.mem_singleton.1 h]; exact hs
      simp only [List.cons_append] at hc
      simp [R002.alive, aliveL, aliveR, headSpan, Charged.composable, hc]
  rw [walk]
  simp only [Bool.false_eq_true, ↓reduceIte, bind_val, bind_ticks, tick_ticks, ha]
  exact ⟨trivial, by omega⟩

/-- The walk of a choice after a chain of wrappers hands both wrappers on. -/
theorem walk_bit {L : List Span} (hL : ∀ t ∈ L, Wrap t)
    (K : List Rel → List (List Rel) → Cost Walk) {c : Nat}
    (hK : ∀ s, Wrap s → ∀ acc, (K [.span s] acc).val.1 = false ∧ c ≤ (K [.span s] acc).ticks)
    (acc : List (List Rel)) :
    (walk P0 0 false bit L [] K acc).val.1 = false ∧
      2 * c ≤ (walk P0 0 false bit L [] K acc).ticks := by
  obtain ⟨a1, a2⟩ := walk_wrap (s := wrap "0") (Or.inl rfl) hL K acc
  obtain ⟨c1, c2⟩ := hK (wrap "0") (Or.inl rfl) acc
  rw [c1] at a1
  obtain ⟨b1, b2⟩ := walk_wrap (s := wrap "1") (Or.inr rfl) hL K
    (walk P0 0 false (.span (wrap "0")) L [] K acc).val.2
  obtain ⟨d1, d2⟩ := hK (wrap "1") (Or.inr rfl)
    (walk P0 0 false (.span (wrap "0")) L [] K acc).val.2
  rw [d1] at b1
  rw [bit, walk]
  simp only [bind_val, bind_ticks, tick_ticks, a1, Bool.false_eq_true, ↓reduceIte]
  exact ⟨b1, by omega⟩

theorem staticFirst_gen : ∀ j, staticFirst false (gen j) = none
  | 0 => rfl
  | j + 1 => by simp [gen, bit, staticFirst]

/-- The walk of `gen j` after a chain of wrappers does not stop, and goes
through all `2 ^ (j + 1)` products. -/
theorem walk_gen : ∀ (j : Nat) {L : List Span}, (∀ t ∈ L, Wrap t) → ∀ (R : List Span)
    {K : List Rel → List (List Rel) → Cost Walk}, Cont K → ∀ acc : List (List Rel),
    (walk P0 0 false (gen j) L R K acc).val.1 = false ∧
      2 ^ (j + 1) ≤ (walk P0 0 false (gen j) L R K acc).ticks
  | 0, L, _, R, K, hK, acc => by
    obtain ⟨a1, a2⟩ := walk_span_any (wrap "0") L R hK acc
    obtain ⟨b1, b2⟩ := walk_span_any (wrap "1") L R hK
      (walk P0 0 false (.span (wrap "0")) L R K acc).val.2
    rw [gen, bit, walk]
    simp only [bind_val, bind_ticks, tick_ticks, a1, Bool.false_eq_true, ↓reduceIte]
    exact ⟨b1, by omega⟩
  | j + 1, L, hL, R, K, hK, acc => by
    have hin : ∀ s, Wrap s → ∀ acc : List (List Rel),
        (walk P0 0 false (gen j) (leftAfter L [.span s]) R (fun q acc => do
          let r ← R002.joinSeq [.span s] q
          match r with
          | none => pure (false, acc)
          | some r => do
            let a ← aliveR r R
            if a then K r acc else pure (false, acc)) acc).val.1 = false ∧
        2 ^ (j + 1) ≤ (walk P0 0 false (gen j) (leftAfter L [.span s]) R (fun q acc => do
          let r ← R002.joinSeq [.span s] q
          match r with
          | none => pure (false, acc)
          | some r => do
            let a ← aliveR r R
            if a then K r acc else pure (false, acc)) acc).ticks := by
      intro s hs acc
      have hL' : ∀ t ∈ L ++ [s], Wrap t := by
        intro t ht
        rcases List.mem_append.1 ht with h | h
        · exact hL t h
        · rw [List.mem_singleton.1 h]; exact hs
      exact walk_gen j hL' R (cont_join hK s R) acc
    obtain ⟨h1, h2⟩ := walk_bit hL (fun p acc =>
      walk P0 0 false (gen j) (leftAfter L p) R (fun q acc => do
        let r ← R002.joinSeq p q
        match r with
        | none => pure (false, acc)
        | some r => do
          let a ← aliveR r R
          if a then K r acc else pure (false, acc)) acc) hin acc
    rw [gen, walk]
    simp only [rightOf, staticFirst_gen, bind_val, bind_ticks, tick_ticks]
    refine ⟨h1, ?_⟩
    rw [pow_succ, Nat.mul_comm]
    exact le_trans h2 (Nat.le_add_left _ _)

/-- The walk of the branch with no answers goes through all the products of
`gen k`. -/
theorem walk_dead (k : Nat) {K : List Rel → List (List Rel) → Cost Walk} (hK : Cont K)
    (acc : List (List Rel)) : 2 ^ (k + 1) ≤ (walk P0 0 false (dead k) [] [] K acc).ticks := by
  have h := (walk_gen k (L := []) (by simp) [qq]
    (K := fun p acc => walk P0 0 false (.span qq) (leftAfter [] p) [] (fun q acc => do
        let r ← R002.joinSeq p q
        match r with
        | none => pure (false, acc)
        | some r => do
          let a ← aliveR r []
          if a then K r acc else pure (false, acc)) acc)
    (fun s acc => (walk_span_any qq _ _ (cont_join hK s []) acc).1) acc).2
  rw [walk]
  simp only [bind_ticks, tick_ticks]
  exact le_trans h (Nat.le_add_left _ _)

theorem walk_root (k : Nat) {K : List Rel → List (List Rel) → Cost Walk} (hK : Cont K)
    (acc : List (List Rel)) :
    2 ^ (k + 1) ≤ (walk P0 0 false (.or (.span aa) (dead k)) [] [] K acc).ticks := by
  obtain ⟨a1, -⟩ := walk_span_any aa [] [] hK acc
  have h := walk_dead k hK (walk P0 0 false (.span aa) [] [] K acc).val.2
  rw [walk]
  simp only [bind_ticks, tick_ticks, a1, Bool.false_eq_true, ↓reduceIte]
  exact le_trans h (le_trans (Nat.le_add_left _ _) (Nat.le_add_left _ _))

/-- The walk on the query goes through all the products of `gen k`. -/
theorem onDemand_ge (k : Nat) : 2 ^ (k + 1) ≤ (onDemand P0 0 (g0 k)).ticks := by
  have hrel : (g0 k).rel = .or (.span aa) (dead k) := rfl
  simp only [onDemand, hrel, bind_ticks]
  exact le_trans (walk_root k cont_top []) (Nat.le_add_right _ _)

/-! ## The shared evaluation -/

open R003 in
theorem closed_map (S : List Span) : closed (S.map fun s => [Rel.span s]) = S := by
  induction S with
  | nil => rfl
  | cons s S ih => simp only [closed, List.map_cons, List.filterMap_cons, single_span] at ih ⊢; rw [ih]

/-- The summary of `gen k` lists its `2 ^ (k + 1)` spans. -/
theorem spans_gen (k : Nat) :
    (R003.eval P0 0 false (gen k) none []).val.1.spans.length = 2 ^ (k + 1) := by
  obtain ⟨S, e, hn, hl⟩ := norm_gen k
  have h := ((R003.eval_ok P0 0 (gen k) false) none [] (R003.memoOK_nil P0)).1.1
  have hu : unfoldN P0 0 (gen k) = gen k := rfl
  have hf : S.filter (R003.aliveB (R003.rng none)) = S :=
    List.filter_eq_self.2 fun s _ => R003.aliveB_iff.2 (R003.aliveP_univ s)
  rw [h, hu, e, closed_map, hf, firsts_eq_eraseDups, length_eraseDups,
    List.toFinset_card_of_nodup hn, hl]

theorem memo_nil_ticks (key : R003.Key) (body : R003.Memo → Cost (R003.Summary × R003.Memo)) :
    (R003.memo key [] body).ticks = (body []).ticks := by
  simp [R003.memo, R003.lookup, findL]

/-- Continuing after each span of the first factor costs at least one tick
for each. -/
theorem seqSummary_ge (first : R003.Summary)
    (second : Option Span → R003.Memo → Cost (R003.Summary × R003.Memo)) (m : R003.Memo) :
    first.spans.length ≤ (R003.seqSummary none first second m).ticks := by
  have h : ∀ (acc : R003.Acc) (x : Span), 1 ≤ (R003.afterSpan none second acc x).ticks := by
    intro acc x
    have := Span.size_pos x
    simp only [R003.afterSpan, R003.extend, bind_ticks, tick_ticks]
    omega
  simp only [R003.seqSummary, bind_ticks]
  exact le_trans (length_le_foldL_ticks _ h _ _) (Nat.le_add_right _ _)

theorem eval_dead_ge (k : Nat) : 2 ^ (k + 1) ≤ (R003.eval P0 0 false (dead k) none []).ticks := by
  rw [R003.eval, memo_nil_ticks]
  simp only [bind_ticks, tick_ticks]
  exact le_trans (le_of_eq (spans_gen k).symm) (le_trans (seqSummary_ge _ _ _)
    (le_trans (Nat.le_add_left _ _) (Nat.le_add_left _ _)))

theorem eval_root_ge (k : Nat) :
    2 ^ (k + 1) ≤ (R003.eval P0 0 false (.or (.span aa) (dead k)) none []).ticks := by
  have hx : (R003.eval P0 0 false (.span aa) none []).val.2 = [] := by rw [R003.eval]; rfl
  rw [R003.eval, memo_nil_ticks]
  simp only [bind_ticks, tick_ticks, hx]
  exact le_trans (eval_dead_ge k) (le_trans (Nat.le_add_right _ _)
    (le_trans (Nat.le_add_left _ _) (Nat.le_add_left _ _)))

/-- The shared evaluation of the query continues after each of the
`2 ^ (k + 1)` spans of `gen k`. -/
theorem shared_ge (k : Nat) : 2 ^ (k + 1) ≤ (R003.shared P0 0 (g0 k)).ticks := by
  have hrel : (g0 k).rel = .or (.span aa) (dead k) := rfl
  simp only [R003.shared, hrel, bind_ticks]
  exact le_trans (eval_root_ge k) (Nat.le_add_right _ _)

/-! ## The round -/

/-- R003's unfolding race on the query costs at least `2 ^ (k + 1)`. -/
theorem r003_unfolder_ge (k : Nat) : 2 ^ (k + 1) ≤ (R003.unfolder P0 0 (g0 k)).ticks :=
  le_trans (le_min (onDemand_ge k) (shared_ge k)) (Cost.le_race_ticks _ _)

/-- R003's first round costs at least its unfolding race on the query. -/
theorem r003_first (k : Nat) : 2 ^ k ≤ (R003.costed.step (st0 k)).ticks := by
  obtain ⟨K, hK⟩ := Tabled.round_split (st0 k)
  have s1 := (R003.Sep.step_emit (U := R003.unfolder) (st := st0 k) rfl).2
  have e : (R003.costed.step (st0 k)).ticks = _ := s1
  have h := r003_unfolder_ge k
  rw [e, hK R003.unfolder]
  simp only [bind_ticks, tick_ticks, mapL, Tabled.ask, Bool.false_eq_true, ↓reduceIte, pure_ticks]
  rw [pow_succ] at h
  omega

end Sep

end R004

end RwLog
