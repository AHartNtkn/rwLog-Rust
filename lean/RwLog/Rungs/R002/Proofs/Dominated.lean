/-
# One call of the on-demand unfolder is never much worse

`walk_spec` instantiates the bound of `WalkCost.lean` at every expression and
depth, by induction on the depth and then on the expression: the walk of `e`
at depth `d` is charged against the eager normalization of `e` unfolded `d`
times. `onDemand_dominated` reads it at the top, where both chains are empty
and the continuation collects the products: the walk costs at most
`c (3 + d) + c² (S + 1)` for `c` the ticks of the eager normalizer and `S` the
size of the program and the goal, and the answers of what it collected cost
what they cost the eager unfolder.

The eager unfolder pays at least `d` to unfold `d` times, so this is within
the cubic polynomial of the obligation.
-/
import RwLog.Rungs.R002.Proofs.WalkCost

namespace RwLog

namespace R002

open Cost

/-! ## The ticks of the eager normalizer -/

namespace Eager

theorem norm_ticks_zero (neg : Bool) : (norm neg .zero).ticks = 1 := by
  cases neg <;> rfl

theorem norm_ticks_span (neg : Bool) (s : Span) : (norm neg (.span s)).ticks = 1 + s.size := by
  cases neg <;> rfl

theorem norm_ticks_or (neg : Bool) (a b : Rel) :
    (norm neg (.or a b)).ticks = 1 + (norm neg a).ticks + (norm neg b).ticks := by
  simp only [norm, bind_ticks, tick_ticks, pure_ticks]
  omega

theorem norm_ticks_seq_false (a b : Rel) :
    (norm false (.seq a b)).ticks = 1 + (norm false a).ticks +
      ((R000.norm false a).map fun p => (norm false b).ticks +
        ((R000.norm false b).map fun q => (R002.joinSeq p q).ticks).sum).sum := by
  simp only [norm, bind_ticks, tick_ticks, flatMapL_ticks, filterMapL_ticks, norm_val]
  omega

theorem norm_ticks_seq_true (a b : Rel) :
    (norm true (.seq a b)).ticks = 1 + (norm true b).ticks +
      ((R000.norm true b).map fun p => (norm true a).ticks +
        ((R000.norm true a).map fun q => (R002.joinSeq p q).ticks).sum).sum := by
  simp only [norm, bind_ticks, tick_ticks, flatMapL_ticks, filterMapL_ticks, norm_val]
  omega

theorem norm_ticks_and (neg : Bool) (a b : Rel) :
    (norm neg (.and a b)).ticks = 1 + (norm neg a).ticks +
      ((R000.norm neg a).map fun p => (norm neg b).ticks +
        ((R000.norm neg b).map fun q => (R002.mkAnd p q).ticks).sum).sum := by
  simp only [norm, bind_ticks, tick_ticks, flatMapL_ticks, filterMapL_ticks, norm_val]
  omega

theorem norm_ticks_conv (neg : Bool) (a : Rel) :
    (norm neg (.conv a)).ticks = 1 + (norm (!neg) a).ticks := by
  simp only [norm, bind_ticks, tick_ticks]

theorem norm_ticks_call (neg : Bool) (n : Name) : (norm neg (.call n)).ticks = 1 := by
  cases neg <;> rfl

theorem unfold_ticks_pos (P : Program) (e : Rel) : 1 ≤ (unfold P e).ticks := by
  cases e <;> simp only [unfold, bind_ticks, tick_ticks] <;> omega

/-- Unfolding `d` times costs at least `d`. -/
theorem unfoldN_ticks_ge (P : Program) : ∀ (d : Nat) (e : Rel), d ≤ (unfoldN P d e).ticks
  | 0, _ => Nat.zero_le _
  | d + 1, e => by
    have h1 := unfold_ticks_pos P e
    have h2 := unfoldN_ticks_ge P d (unfold P e).val
    simp only [unfoldN, bind_ticks]
    omega

end Eager

/-! ## The spans written in an expression -/

/-- Every span written in the expression has size at most `S`. -/
def SB (S : Nat) : Rel → Prop
  | .zero => True
  | .span s => s.size ≤ S
  | .or a b => SB S a ∧ SB S b
  | .and a b => SB S a ∧ SB S b
  | .seq a b => SB S a ∧ SB S b
  | .conv a => SB S a
  | .call _ => True

theorem SB_mono {S S' : Nat} (h : S ≤ S') : ∀ e : Rel, SB S e → SB S' e
  | .zero, _ => trivial
  | .span _, hs => Nat.le_trans hs h
  | .or a b, hs => ⟨SB_mono h a hs.1, SB_mono h b hs.2⟩
  | .and a b, hs => ⟨SB_mono h a hs.1, SB_mono h b hs.2⟩
  | .seq a b, hs => ⟨SB_mono h a hs.1, SB_mono h b hs.2⟩
  | .conv a, hs => SB_mono h a hs
  | .call _, _ => trivial

theorem SB_size : ∀ e : Rel, SB e.size e
  | .zero => trivial
  | .span s => Nat.le_add_left _ _
  | .or a b => ⟨SB_mono (by simp only [Rel.size]; omega) a (SB_size a),
      SB_mono (by simp only [Rel.size]; omega) b (SB_size b)⟩
  | .and a b => ⟨SB_mono (by simp only [Rel.size]; omega) a (SB_size a),
      SB_mono (by simp only [Rel.size]; omega) b (SB_size b)⟩
  | .seq a b => ⟨SB_mono (by simp only [Rel.size]; omega) a (SB_size a),
      SB_mono (by simp only [Rel.size]; omega) b (SB_size b)⟩
  | .conv a => SB_mono (by simp only [Rel.size]; omega) a (SB_size a)
  | .call _ => trivial

theorem lookup_size (n : Name) (b : Rel) : ∀ defs : List (Name × Rel), defs.lookup n = some b →
    b.size ≤ (defs.map fun d => 1 + d.2.size).sum
  | [], h => by cases h
  | (m, c) :: defs, h => by
    rw [List.lookup_cons] at h
    simp only [List.map_cons, List.sum_cons]
    split at h
    · cases h; omega
    · have := lookup_size n b defs h
      omega

theorem SB_body (P : Program) (n : Name) : SB P.size (P.body n) := by
  unfold Program.body
  cases h : P.defs.lookup n with
  | none => trivial
  | some b =>
    refine SB_mono ?_ b (SB_size b)
    have := lookup_size n b P.defs h
    unfold Program.size
    omega

theorem SB_goal (g : R001.Goal) : SB (goalSize g) g.rel := by
  obtain ⟨lb, e, rb⟩ := g
  have he := SB_size e
  have hsz : goalSize ⟨lb, e, rb⟩ = e.size + ((lb.toList ++ rb.toList).map Span.size).sum := rfl
  rw [hsz]
  cases lb with
  | none =>
    cases rb with
    | none => exact SB_mono (Nat.le_add_right _ _) e he
    | some r =>
      refine And.intro (SB_mono (Nat.le_add_right _ _) e he) ?_
      show r.size ≤ e.size + (r.size + 0)
      omega
  | some l =>
    cases rb with
    | none =>
      refine And.intro ?_ (SB_mono (Nat.le_add_right _ _) e he)
      show l.size ≤ e.size + (l.size + 0)
      omega
    | some r =>
      refine And.intro ?_ (And.intro (SB_mono (Nat.le_add_right _ _) e he) ?_)
      · show l.size ≤ e.size + (l.size + (r.size + 0))
        omega
      · show r.size ≤ e.size + (l.size + (r.size + 0))
        omega

/-- A span the expression is known to start with is written in it, and the
eager normalizer pays for it. -/
theorem static_size (P : Program) (d S : Nat) : ∀ (e : Rel) (neg : Bool) (t : Span) (fl : Bool),
    staticFirst neg e = some (t, fl) → SB S e →
      t.size ≤ S ∧ t.size + 1 ≤ (Eager.norm neg (R000.unfoldN P d e)).ticks := by
  intro e
  induction e with
  | zero => intro neg t fl h; cases neg <;> simp [staticFirst] at h
  | span s =>
    intro neg t fl h hs
    simp only [staticFirst, Option.some.injEq, Prod.mk.injEq] at h
    rw [R000.unfoldN_span, Eager.norm_ticks_span, ← h.1]
    have hsz : (if neg = true then s.swap else s).size = s.size := by
      cases neg
      · rfl
      · exact Span.size_swap s
    rw [hsz]
    exact ⟨hs, by omega⟩
  | or a b _ _ => intro neg t fl h; cases neg <;> simp [staticFirst] at h
  | and a b _ _ => intro neg t fl h; cases neg <;> simp [staticFirst] at h
  | seq a b iha ihb =>
    intro neg t fl h hs
    rw [R000.unfoldN_seq]
    cases neg
    · simp only [staticFirst, Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨⟨t', fl'⟩, ha, rfl, -⟩ := h
      obtain ⟨h1, h2⟩ := iha false _ fl' ha hs.1
      rw [Eager.norm_ticks_seq_false]
      exact ⟨h1, Nat.le_trans h2 (by omega)⟩
    · simp only [staticFirst, Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨⟨t', fl'⟩, hb, rfl, -⟩ := h
      obtain ⟨h1, h2⟩ := ihb true _ fl' hb hs.2
      rw [Eager.norm_ticks_seq_true]
      exact ⟨h1, Nat.le_trans h2 (by omega)⟩
  | conv a iha =>
    intro neg t fl h hs
    rw [R000.unfoldN_conv, Eager.norm_ticks_conv]
    have := iha (!neg) t fl (by simpa only [staticFirst] using h) hs
    exact ⟨this.1, by omega⟩
  | call n => intro neg t fl h; cases neg <;> simp [staticFirst] at h

/-! ## The walk against the eager normalizer -/

/-- The bound at one depth, given it for the calls at that depth. -/
theorem walk_spec_step (P : Program) (S d : Nat)
    (hcall : ∀ n neg, Spec (3 + d) S (walk P d neg (.call n))
      (R000.norm neg (R000.unfoldN P d (.call n)))
      (Eager.norm neg (R000.unfoldN P d (.call n))).ticks) :
    ∀ e neg, SB S e → Spec (3 + d) S (walk P d neg e)
      (R000.norm neg (R000.unfoldN P d e)) (Eager.norm neg (R000.unfoldN P d e)).ticks := by
  intro e
  induction e with
  | zero =>
    intro neg _
    have hw : walk P d neg .zero = (fun _ _ _ acc => do tick 1; pure (false, acc)) := by
      funext L R k acc
      rw [walk]
    rw [hw, R000.unfoldN_zero, Eager.norm_ticks_zero]
    exact Spec.zero _ _
  | span s =>
    intro neg _
    have hw : walk P d neg (.span s) = (fun L R k acc => do
        tick 1
        let a ← alive L [.span (if neg then s.swap else s)] R
        if a then k [.span (if neg then s.swap else s)] acc else pure (false, acc)) := by
      funext L R k acc
      rw [walk]
    rw [hw, R000.unfoldN_span, Eager.norm_ticks_span]
    refine Spec.leaf _ _ (by omega) _ _ ?_
    cases neg
    · rfl
    · exact congrArg _ (Span.size_swap s).symm
  | or a b iha ihb =>
    intro neg hs
    have hw : walk P d neg (.or a b) = (fun L R k acc => do
        tick 1
        let r ← walk P d neg a L R k acc
        if r.1 then pure r else walk P d neg b L R k r.2) := by
      funext L R k acc
      rw [walk]
    rw [hw, R000.unfoldN_or, Eager.norm_ticks_or]
    exact Spec.or (iha neg hs.1) (ihb neg hs.2)
  | seq a b iha ihb =>
    intro neg hs
    rw [R000.unfoldN_seq]
    cases neg
    · have hw : walk P d false (.seq a b) = (fun L R k acc => do
          tick 1
          walk P d false a L (rightBy (staticFirst false b) R) (fun p acc =>
            walk P d false b (leftAfter L p) R (joinK k R p) acc) acc) := by
        funext L R k acc
        rw [walk]
        rfl
      rw [hw, Eager.norm_ticks_seq_false]
      exact Spec.seq (by omega) (iha false hs.1) (ihb false hs.2) _ fun t fl h =>
        ⟨(static_size P d S b false t fl h hs.2).1, (static_size P d S b false t fl h hs.2).2,
          fun hfl => static_true P d b false t (hfl ▸ h)⟩
    · have hw : walk P d true (.seq a b) = (fun L R k acc => do
          tick 1
          walk P d true b L (rightBy (staticFirst true a) R) (fun p acc =>
            walk P d true a (leftAfter L p) R (joinK k R p) acc) acc) := by
        funext L R k acc
        rw [walk]
        rfl
      rw [hw, Eager.norm_ticks_seq_true]
      exact Spec.seq (by omega) (ihb true hs.2) (iha true hs.1) _ fun t fl h =>
        ⟨(static_size P d S a true t fl h hs.1).1, (static_size P d S a true t fl h hs.1).2,
          fun hfl => static_true P d a true t (hfl ▸ h)⟩
  | and a b iha ihb =>
    intro neg hs
    have hw : walk P d neg (.and a b) = (fun L R k acc => do
        tick 1
        walk P d neg a [] [] (fun p acc =>
          walk P d neg b [] [] (fun q acc => do
            let r ← R002.mkAnd p q
            match r with
            | none => pure (false, acc)
            | some r => do
              let a ← alive L r R
              if a then k r acc else pure (false, acc)) acc) acc) := by
      funext L R k acc
      rw [walk]
      rfl
    rw [hw, R000.unfoldN_and, Eager.norm_ticks_and]
    exact Spec.and (by omega) (iha neg hs.1) (ihb neg hs.2)
  | conv a iha =>
    intro neg hs
    have hw : walk P d neg (.conv a) = (fun L R k acc => do
        tick 1
        walk P d (!neg) a L R k acc) := by
      funext L R k acc
      rw [walk]
    rw [hw, R000.unfoldN_conv, Eager.norm_ticks_conv]
    exact Spec.step (iha (!neg) hs) (Nat.le_refl _) (by omega) (by omega)
  | call n => intro neg _; exact hcall n neg

/-- The walk of `e` at depth `d` against the eager normalization of `e`
unfolded `d` times. -/
theorem walk_spec (P : Program) (S : Nat) (hP : ∀ n, SB S (P.body n)) :
    ∀ (d : Nat) (e : Rel) (neg : Bool), SB S e → Spec (3 + d) S (walk P d neg e)
      (R000.norm neg (R000.unfoldN P d e)) (Eager.norm neg (R000.unfoldN P d e)).ticks := by
  intro d
  induction d with
  | zero =>
    refine walk_spec_step P S 0 fun n neg => ?_
    have hw : walk P 0 neg (.call n) = (fun _ _ k acc => do
        tick 1
        k [if neg then .conv (.call n) else .call n] acc) := by
      funext L R k acc
      rw [walk]
    rw [hw, R000.unfoldN_zero_apply, Eager.norm_ticks_call]
    exact Spec.atom _ _ _ (fun s h => by cases neg <;> cases h)
  | succ d ih =>
    refine walk_spec_step P S (d + 1) fun n neg => ?_
    have hw : walk P (d + 1) neg (.call n) = (fun L R k acc => do
        tick 1
        walk P d neg (P.body n) L R k acc) := by
      funext L R k acc
      rw [walk]
    rw [hw, R000.unfoldN_call]
    exact Spec.step (ih (P.body n) neg (hP n)) (by omega) (Nat.le_refl _) (by omega)

/-! ## One call of the unfolder -/

/-- What the answers of a list of products cost. -/
def liveCost (T : Theory) (acc : List (List Rel)) : Nat :=
  (flatMapL (Tabled.live T) (closed acc)).ticks

theorem liveCost_append (T : Theory) (xs ys : List (List Rel)) :
    liveCost T (xs ++ ys) = liveCost T xs + liveCost T ys := by
  simp only [liveCost, flatMapL_ticks, closed_append, List.map_append, List.sum_append]

theorem liveCost_eq_sum (T : Theory) (xs : List (List Rel)) :
    liveCost T xs = (xs.map fun p => liveCost T [p]).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [show x :: xs = [x] ++ xs from rfl, liveCost_append, ih]
    rfl

theorem dominated_arith (u d l S Eu : Nat) (hd : d ≤ Eu) :
    Phi (3 + d) S u 0 + l ≤ 4 * (Eu + u + l + S + 1) ^ 3 := by
  have hu : u ≤ Eu + u + l + S + 1 := by omega
  have hs : S + 1 ≤ Eu + u + l + S + 1 := by omega
  have hul : u + l ≤ Eu + u + l + S + 1 := by omega
  have h3 : 3 + d ≤ 3 * (Eu + u + l + S + 1) := by omega
  have hX : 1 ≤ Eu + u + l + S + 1 := by omega
  generalize Eu + u + l + S + 1 = X at *
  have h1 : u * u * (S + 1) ≤ X * X * X := Nat.mul_le_mul (Nat.mul_le_mul hu hu) hs
  have h2 : (u + l) * (3 + d) ≤ X * (3 * X) := Nat.mul_le_mul hul h3
  have h4 : u * (0 + (3 + d)) + l ≤ (u + l) * (3 + d) := by
    rw [Nat.zero_add, Nat.add_mul]
    exact Nat.add_le_add_left (Nat.le_mul_of_pos_right _ (by omega)) _
  have h5 : X * (3 * X) ≤ 3 * (X * X * X) := by
    have : X * X ≤ X * X * X := Nat.le_mul_of_pos_right _ hX
    calc X * (3 * X) = 3 * (X * X) := by ring
      _ ≤ 3 * (X * X * X) := Nat.mul_le_mul_left 3 this
  have h6 : X ^ 3 = X * X * X := by ring
  unfold Phi
  rw [h6]
  omega

/-- One call of the on-demand unfolder costs at most a cubic polynomial of
what the eager one costs on the same goal at the same depth, and of the sizes
of the program and the goal. -/
theorem onDemand_dominated : Obligation.onDemand_dominated := by
  intro P d g
  have hspec := walk_spec P (P.size + goalSize g)
    (fun n => SB_mono (Nat.le_add_right _ _) _ (SB_body P n)) d g.rel false
    (SB_mono (Nat.le_add_left _ _) _ (SB_goal g))
  have hd := Eager.unfoldN_ticks_ge P d g.rel
  have heag : (eager P d g).ticks = (Eager.unfoldN P d g.rel).ticks +
      (Eager.norm false (R000.unfoldN P d g.rel)).ticks +
      (if (R000.norm false (R000.unfoldN P d g.rel)).all (fun p => (toRel p).calls.isEmpty) = true
        then liveCost P.theory (R000.norm false (R000.unfoldN P d g.rel)) else 0) := by
    unfold eager
    simp only [bind_ticks, Eager.unfoldN_val, Eager.norm_val, ite_ticks, pure_ticks,
      Nat.add_zero, liveCost]
    omega
  have hond : (onDemand P d g).ticks ≤
      (walk P d false g.rel [] []
        (fun p acc => pure (if (toRel p).calls.isEmpty then (false, acc ++ [p]) else (true, acc)))
        []).ticks +
      (if (walk P d false g.rel [] []
          (fun p acc => pure (if (toRel p).calls.isEmpty then (false, acc ++ [p]) else (true, acc)))
          []).val.1 = true then 0
        else liveCost P.theory (walk P d false g.rel [] []
          (fun p acc => pure (if (toRel p).calls.isEmpty then (false, acc ++ [p]) else (true, acc)))
          []).val.2) := by
    unfold onDemand
    simp only [bind_ticks, ite_ticks, pure_ticks, Nat.add_zero, liveCost]
    exact Nat.le_refl _
  rw [heag]
  refine Nat.le_trans ?_ (Nat.le_trans (dominated_arith
    (Eager.norm false (R000.unfoldN P d g.rel)).ticks d
    (if (R000.norm false (R000.unfoldN P d g.rel)).all (fun p => (toRel p).calls.isEmpty) = true
      then liveCost P.theory (R000.norm false (R000.unfoldN P d g.rel)) else 0)
    (P.size + goalSize g) (Eager.unfoldN P d g.rel).ticks hd)
    (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left (by omega) 3)))
  refine Nat.le_trans hond ?_
  by_cases hall : (R000.norm false (R000.unfoldN P d g.rel)).all
      (fun p => (toRel p).calls.isEmpty) = true
  · rw [ite_eq_left hall]
    have hb := hspec.bound [] []
      (fun p acc => pure (if (toRel p).calls.isEmpty then (false, acc ++ [p]) else (true, acc))) []
      (liveCost P.theory) (fun p => liveCost P.theory [p]) (by
        intro p acc _
        simp only [pure_ticks, pure_val]
        split
        · rw [liveCost_append]; omega
        · dsimp only; omega)
    have hsum : ((R000.norm false (R000.unfoldN P d g.rel)).map fun p =>
          if Ok [] [] p then liveCost P.theory [p] +
            (Eager.norm false (R000.unfoldN P d g.rel)).ticks * rch [] p else 0).sum ≤
        liveCost P.theory (R000.norm false (R000.unfoldN P d g.rel)) := by
      rw [liveCost_eq_sum P.theory (R000.norm false (R000.unfoldN P d g.rel))]
      refine sum_map_le fun p _ => ?_
      split
      · rw [rch_nil]; omega
      · exact Nat.zero_le _
    have h0 : liveCost P.theory [] = 0 := rfl
    simp only [sz_nil, Nat.add_zero] at hb
    split <;> omega
  · rw [ite_eq_right hall]
    have hval : (onDemand P d g).val.1 = (eager P d g).val.1 := by
      rw [onDemand_exact P d g, eager_exact P d g]
    have hev : (eager P d g).val.1 = false := by
      unfold eager
      simp only [bind_val, Eager.unfoldN_val, Eager.norm_val, ite_val, pure_val]
      rw [ite_eq_right hall]
    have hov : (onDemand P d g).val.1 = !(walk P d false g.rel [] []
        (fun p acc => pure (if (toRel p).calls.isEmpty then (false, acc ++ [p]) else (true, acc)))
        []).val.1 := by
      unfold onDemand
      simp only [bind_val, ite_val, pure_val]
      split
      · rename_i h; rw [h]; rfl
      · rename_i h; rw [Bool.not_eq_true] at h; rw [h]; rfl
    have hstop : (walk P d false g.rel [] []
        (fun p acc => pure (if (toRel p).calls.isEmpty then (false, acc ++ [p]) else (true, acc)))
        []).val.1 = true := by
      rw [hval, hev] at hov
      cases h : (walk P d false g.rel [] []
        (fun p acc => pure (if (toRel p).calls.isEmpty then (false, acc ++ [p]) else (true, acc)))
        []).val.1 with
      | true => rfl
      | false => rw [h] at hov; cases hov
    have hb := hspec.bound [] []
      (fun p acc => pure (if (toRel p).calls.isEmpty then (false, acc ++ [p]) else (true, acc))) []
      (fun _ => 0) (fun _ => 0) (by
        intro p acc _
        simp only [pure_ticks]
        omega)
    have hsum : ((R000.norm false (R000.unfoldN P d g.rel)).map fun p =>
          if Ok [] [] p then 0 +
            (Eager.norm false (R000.unfoldN P d g.rel)).ticks * rch [] p else 0).sum ≤ 0 := by
      refine Nat.le_trans (sum_map_le (g := fun _ => 0) fun p _ => ?_) (by simp)
      split
      · rw [rch_nil]; omega
      · exact Nat.zero_le _
    simp only [sz_nil, Nat.add_zero] at hb
    rw [ite_eq_left hstop]
    omega

end R002

end RwLog
