/-
# The on-demand unfolder is R001's unfolding race

`walk_val` is the invariant of the walk: with the ticks forgotten, walking `e`
at depth `d` between the chains `L` and `R` runs the continuation over exactly
the products of rung zero's normal form of the unfolding of `e` to depth `d`
that are alive between `L` and `R`, in the normalizer's order, until the
continuation says stop (`run`). At the top both chains are empty, so nothing
is dropped, and the continuation collects the products until one contains a
call; `onDemand_exact` follows.
-/
import RwLog.Rungs.R002.Proofs.Chains
import RwLog.Rungs.R000.Unfold

namespace RwLog

namespace R002

open Cost

/-! ## Running a continuation over a list of products -/

/-- Hand the products to `k` in order, threading what it has collected, until
it says stop. -/
def run (k : List Rel → List (List Rel) → Cost Walk) : List (List Rel) → List (List Rel) → Walk
  | [], acc => (false, acc)
  | p :: ps, acc => if (k p acc).val.1 then (k p acc).val else run k ps (k p acc).val.2

theorem run_singleton (k : List Rel → List (List Rel) → Cost Walk) (p : List Rel)
    (acc : List (List Rel)) : run k [p] acc = (k p acc).val := by
  simp only [run]
  split
  · rfl
  · rename_i h
    have h' : (k p acc).val.1 = false := by simpa using h
    exact Prod.ext h'.symm rfl

theorem run_append (k : List Rel → List (List Rel) → Cost Walk) (xs ys : List (List Rel))
    (acc : List (List Rel)) :
    run k (xs ++ ys) acc =
      if (run k xs acc).1 then run k xs acc else run k ys (run k xs acc).2 := by
  induction xs generalizing acc with
  | nil => simp [run]
  | cons p xs ih =>
    simp only [List.cons_append, run]
    split
    · simp
    · exact ih _

theorem run_flatMap (k k' : List Rel → List (List Rel) → Cost Walk)
    (F : List Rel → List (List Rel)) (xs : List (List Rel))
    (h : ∀ p acc, (k' p acc).val = run k (F p) acc) (acc : List (List Rel)) :
    run k' xs acc = run k (xs.flatMap F) acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons p xs ih =>
    rw [List.flatMap_cons, run_append]
    simp only [run, h, ih]

theorem run_filterMap (k k₂ : List Rel → List (List Rel) → Cost Walk)
    (f : List Rel → Option (List Rel)) (g : List Rel → Bool)
    (h : ∀ q acc, (k₂ q acc).val = match f q with
      | none => (false, acc)
      | some r => if g r then (k r acc).val else (false, acc))
    (xs : List (List Rel)) (acc : List (List Rel)) :
    run k₂ xs acc = run k ((xs.filterMap f).filter g) acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons q xs ih =>
    rw [List.filterMap_cons]
    simp only [run, h]
    cases hf : f q with
    | none => simpa using ih acc
    | some r =>
      simp only [List.filter_cons]
      cases hg : g r <;> simp [run, ih]

/-! ## What the expression says about its products -/

/-- An expression that is a span has that span as its only product. -/
theorem static_true (P : Program) (d : Nat) : ∀ (e : Rel) (neg : Bool) (t : Span),
    staticFirst neg e = some (t, true) → R000.norm neg (R000.unfoldN P d e) = [[.span t]] := by
  intro e
  induction e with
  | zero => intro neg t h; cases neg <;> simp [staticFirst] at h
  | span s =>
    intro neg t h
    simp only [staticFirst, Option.some.injEq, Prod.mk.injEq, and_true] at h
    rw [R000.unfoldN_span, R000.norm, h]
  | or a b _ _ => intro neg t h; cases neg <;> simp [staticFirst] at h
  | and a b _ _ => intro neg t h; cases neg <;> simp [staticFirst] at h
  | seq a b _ _ => intro neg t h; cases neg <;> simp [staticFirst] at h
  | conv a iha =>
    intro neg t h
    rw [R000.unfoldN_conv]
    exact iha (!neg) t (by simpa only [staticFirst] using h)
  | call n => intro neg t h; cases neg <;> simp [staticFirst] at h

/-- Every product of an expression that starts with a span starts with a span
that factors through it. -/
theorem static_head (P : Program) (d : Nat) : ∀ (e : Rel) (neg : Bool) (t : Span) (fl : Bool),
    staticFirst neg e = some (t, fl) →
      ∀ q ∈ R000.norm neg (R000.unfoldN P d e), HeadFrom t q := by
  intro e
  induction e with
  | zero => intro neg t fl h; cases neg <;> simp [staticFirst] at h
  | span s =>
    intro neg t fl h q hq
    simp only [staticFirst, Option.some.injEq, Prod.mk.injEq] at h
    rw [R000.unfoldN_span, R000.norm, h.1, List.mem_singleton] at hq
    subst hq
    exact ⟨t, GRel.id, rfl, (GRel.comp_id _).symm⟩
  | or a b _ _ => intro neg t fl h; cases neg <;> simp [staticFirst] at h
  | and a b _ _ => intro neg t fl h; cases neg <;> simp [staticFirst] at h
  | seq a b iha ihb =>
    intro neg t fl h r hr
    rw [R000.unfoldN_seq] at hr
    cases neg
    · simp only [staticFirst, Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨⟨t', fl'⟩, ha, rfl, -⟩ := h
      simp only [R000.norm, List.mem_flatMap, List.mem_filterMap] at hr
      obtain ⟨p, hp, q, -, hj⟩ := hr
      exact headFrom_join (iha false _ fl' ha p hp) hj
    · simp only [staticFirst, Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨⟨t', fl'⟩, hb, rfl, -⟩ := h
      simp only [R000.norm, List.mem_flatMap, List.mem_filterMap] at hr
      obtain ⟨p, hp, q, -, hj⟩ := hr
      exact headFrom_join (ihb true _ fl' hb p hp) hj
  | conv a iha =>
    intro neg t fl h q hq
    rw [R000.unfoldN_conv] at hq
    exact iha (!neg) t fl (by simpa only [staticFirst] using h) q hq
  | call n => intro neg t fl h; cases neg <;> simp [staticFirst] at h

/-- The chain the walk puts to the right of the first factor of a sequence
is true of the products of the second factor. -/
theorem static_rightOf (P : Program) (d : Nat) (neg : Bool) (e : Rel) (R : List Span) :
    Static (R000.norm neg (R000.unfoldN P d e)) R (rightOf neg e R) := by
  unfold rightOf
  cases h : staticFirst neg e with
  | none => exact .inl rfl
  | some r =>
    obtain ⟨t, fl⟩ := r
    cases fl
    · exact .inr (.inr ⟨t, rfl, static_head P d e neg t false h⟩)
    · exact .inr (.inl ⟨t, rfl, static_true P d e neg t h⟩)

/-! ## The invariant of the walk -/

theorem joinK_val (k : List Rel → List (List Rel) → Cost Walk) (R : List Span) (p q : List Rel)
    (acc : List (List Rel)) :
    ((do
      let r ← R002.joinSeq p q
      match r with
      | none => pure (false, acc)
      | some r => do
        let a ← aliveR r R
        if a then k r acc else pure (false, acc)) : Cost Walk).val =
      match R000.joinSeq p q with
      | none => (false, acc)
      | some r => if (aliveR r R).val then (k r acc).val else (false, acc) := by
  simp only [bind_val, joinSeq_val]
  cases R000.joinSeq p q with
  | none => rfl
  | some r =>
    simp only [bind_val]
    cases (aliveR r R).val <;> rfl

theorem andK_val (k : List Rel → List (List Rel) → Cost Walk) (L R : List Span) (p q : List Rel)
    (acc : List (List Rel)) :
    ((do
      let r ← R002.mkAnd p q
      match r with
      | none => pure (false, acc)
      | some r => do
        let a ← alive L r R
        if a then k r acc else pure (false, acc)) : Cost Walk).val =
      match R000.mkAnd p q with
      | none => (false, acc)
      | some r => if keep L R r then (k r acc).val else (false, acc) := by
  simp only [bind_val, mkAnd_val]
  cases R000.mkAnd p q with
  | none => rfl
  | some r =>
    simp only [bind_val, keep]
    by_cases h : (alive L r R).val = true
    · simp only [h, ↓reduceIte]
    · simp only [h]
      rfl

theorem spanK_val (k : List Rel → List (List Rel) → Cost Walk) (L R : List Span) (p : List Rel)
    (acc : List (List Rel)) :
    ((do
      let a ← alive L p R
      if a then k p acc else pure (false, acc)) : Cost Walk).val =
      run k ([p].filter (keep L R)) acc := by
  simp only [bind_val, List.filter_cons, List.filter_nil]
  change (if keep L R p = true then _ else _ : Cost Walk).val = _
  cases hk : keep L R p
  · rfl
  · exact (run_singleton k p acc).symm

/-- The invariant at one depth, given it for the calls at that depth. -/
theorem walk_step (P : Program) (d : Nat)
    (hcall : ∀ n neg L R k acc, (walk P d neg (.call n) L R k acc).val =
      run k ((R000.norm neg (R000.unfoldN P d (.call n))).filter (keep L R)) acc) :
    ∀ e neg L R k acc, (walk P d neg e L R k acc).val =
      run k ((R000.norm neg (R000.unfoldN P d e)).filter (keep L R)) acc := by
  intro e
  induction e with
  | zero =>
    intro neg L R k acc
    rw [R000.unfoldN_zero, walk]
    rfl
  | span s =>
    intro neg L R k acc
    rw [R000.unfoldN_span, walk]
    exact spanK_val k L R _ acc
  | or a b iha ihb =>
    intro neg L R k acc
    rw [R000.unfoldN_or, walk, R000.norm, List.filter_append, run_append, ← iha, ← ihb]
    simp only [bind_val]
    split <;> rfl
  | seq a b iha ihb =>
    intro neg L R k acc
    rw [R000.unfoldN_seq]
    cases neg
    · rw [walk]
      simp only [bind_val]
      rw [iha, R000.norm, ← seq_filter _ _ L R _ (fun p hp => R000.norm_ne_nil _ _ p hp)
        (static_rightOf P d false b R)]
      refine run_flatMap k _ _ _ (fun p acc => ?_) acc
      rw [ihb]
      exact run_filterMap k _ _ _ (fun q acc => joinK_val k R p q acc) _ _
    · rw [walk]
      simp only [bind_val]
      rw [ihb, R000.norm, ← seq_filter _ _ L R _ (fun p hp => R000.norm_ne_nil _ _ p hp)
        (static_rightOf P d true a R)]
      refine run_flatMap k _ _ _ (fun p acc => ?_) acc
      rw [iha]
      exact run_filterMap k _ _ _ (fun q acc => joinK_val k R p q acc) _ _
  | and a b iha ihb =>
    intro neg L R k acc
    rw [R000.unfoldN_and, walk]
    simp only [bind_val]
    rw [iha, R000.norm, List.filter_flatMap, filter_keep_nil]
    refine run_flatMap k _ _ _ (fun p acc => ?_) acc
    rw [ihb, filter_keep_nil]
    exact run_filterMap k _ _ _ (fun q acc => andK_val k L R p q acc) _ _
  | conv a iha =>
    intro neg L R k acc
    rw [R000.unfoldN_conv, walk, R000.norm, ← iha]
    rfl
  | call n => exact hcall n

/-- The invariant of the walk: it hands the continuation exactly the products
of the normal form that are alive between the two chains, in order. -/
theorem walk_val (P : Program) : ∀ (d : Nat) (e : Rel) (neg : Bool) (L R : List Span)
    (k : List Rel → List (List Rel) → Cost Walk) (acc : List (List Rel)),
    (walk P d neg e L R k acc).val =
      run k ((R000.norm neg (R000.unfoldN P d e)).filter (keep L R)) acc := by
  intro d
  induction d with
  | zero =>
    refine walk_step P 0 fun n neg L R k acc => ?_
    rw [walk]
    have hk : keep L R [if neg then RelOf.conv (.call n) else .call n] = true :=
      keep_iff.mpr ⟨fun _ s hs => by cases neg <;> simp [headSpan] at hs,
        fun _ s hs => by cases neg <;> simp [lastSpan] at hs⟩
    change _ = run k ([[if neg then RelOf.conv (.call n) else .call n]].filter (keep L R)) acc
    rw [List.filter_cons, ite_eq_left hk]
    exact (run_singleton k _ acc).symm
  | succ d ih =>
    refine walk_step P (d + 1) fun n neg L R k acc => ?_
    rw [walk]
    exact ih (P.body n) neg L R k acc

/-! ## The race -/

/-- The continuation at the top collects products until one contains a
call. -/
theorem run_top (xs acc : List (List Rel)) :
    run (fun p acc => pure (if (toRel p).calls.isEmpty then (false, acc ++ [p]) else (true, acc)))
        xs acc =
      if xs.all (fun p => (toRel p).calls.isEmpty) then (false, acc ++ xs)
      else (true, acc ++ xs.takeWhile fun p => (toRel p).calls.isEmpty) := by
  induction xs generalizing acc with
  | nil => simp [run]
  | cons p xs ih =>
    rw [run]
    simp only [pure_val, List.all_cons, List.takeWhile_cons]
    cases h : (toRel p).calls.isEmpty
    · simp
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.true_and]
      rw [ih]
      split <;> simp

/-- The on-demand unfolder computes R001's unfolding race. -/
theorem onDemand_exact : Obligation.onDemand_exact := by
  intro P d g
  unfold onDemand
  simp only [bind_val]
  rw [walk_val, filter_keep_nil, run_top]
  unfold R001.unfoldAnswers R001.unfoldFinal R000.roundFinal R000.roundSpans R000.products
  split
  · rename_i h
    simp only [List.nil_append, Bool.false_eq_true, ↓reduceIte, bind_val, pure_val, answers_val, h,
      closed_eq_derivs _ _ h]
  · rename_i h
    simp only [↓reduceIte, pure_val, h]

end R002

end RwLog
