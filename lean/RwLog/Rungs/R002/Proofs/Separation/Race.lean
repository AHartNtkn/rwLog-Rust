/-
# The separating family: the unfolding race on demand

What `onDemand` returns and spends on each goal of the run. The walk of a
link of the chain follows the chain down, one tick per link, and reaches `@z`
or runs out of depth. The walk of `w` goes down one branch to depth zero and
stops there, two ticks per level. So the race costs at most `2 d + k + 5` on
any goal of the run, where the eager unfolder builds `2 ^ d` copies of `w`.
-/
import RwLog.Rungs.R002.Proofs.Separation.State
import RwLog.Rungs.Framework.CostCalculus
import RwLog.Rungs.Framework.Cost

namespace RwLog

namespace R002

namespace Sep

open Cost R000 R001

/-- The continuation at the top of the walk: collect a product without calls,
stop at one with a call. -/
def topK : List Rel → List (List Rel) → Cost Walk :=
  fun p acc => pure (if (toRel p).calls.isEmpty then (false, acc ++ [p]) else (true, acc))

/-- The walk of a link of the chain: down the chain to `@z`, or as far as the
depth allows. -/
theorem walk_chain (k : Nat) : ∀ (d j : Nat), j ≤ k →
    ∀ (K : List Rel → List (List Rel) → Cost Walk) (acc : List (List Rel)),
    walk (prog k) d false (.call (chainName j)) [] [] K acc =
      (tick (if d ≤ j then d + 1 else j + 2) >>= fun _ =>
        K (if d ≤ j then [.call (chainName (j - d))] else [.span zz]) acc)
  | 0, j, _, K, acc => by
    rw [walk]
    simp
  | d + 1, 0, _, K, acc => by
    rw [walk, body_zero, walk]
    refine Cost.ext ?_ ?_
    · simp [alive, aliveL, aliveR]
    · simp [alive, aliveL, aliveR]; omega
  | d + 1, j + 1, hj, K, acc => by
    rw [walk, body_succ (by omega), walk_chain k d j (by omega)]
    by_cases h : d ≤ j
    · have h' : d + 1 ≤ j + 1 := by omega
      refine Cost.ext ?_ ?_
      · simp [h, h']
      · simp [h, h']; omega
    · have h' : ¬ d + 1 ≤ j + 1 := by omega
      refine Cost.ext ?_ ?_
      · simp [h, h']
      · simp [h, h']; omega

/-- The walk of `w` stops at the first call it meets at depth zero. -/
theorem walk_w (k : Nat) : ∀ (d : Nat) (acc : List (List Rel)),
    walk (prog k) d false (.call "w") [] [] topK acc = ⟨(true, acc), 2 * d + 1⟩
  | 0, acc => by
    rw [walk]
    refine Cost.ext ?_ ?_ <;> simp [topK, toRel, Rel.calls]
  | d + 1, acc => by
    rw [walk, body_w, walk]
    refine Cost.ext ?_ ?_
    · simp [walk_w k d]
    · simp [walk_w k d]; omega

/-! ## The empty theory -/

theorem saturate_nil (c : Store) : Theory.saturate [] c = c := by
  rw [Theory.saturate]
  simp [Theory.newAtoms, Theory.firings]

/-- Simplifying `z -> z` by the empty theory returns it, for three ticks. -/
theorem live_zz : Costs (Tabled.live [] zz) [zz] 3 := by
  refine ⟨?_, ?_⟩
  · simp [Tabled.live, Charged.simplify, Theory.simplify, Theory.simplifyWithin, Theory.refutes?,
      Theory.firings, Store.varCount]
  · simp [Tabled.live, Charged.simplify, Theory.simplifyCharge, Theory.refutes?, Theory.firings,
      Store.varCount, saturate_nil, Theory.size, Span.size, Store.size, Term.size]

/-! ## The race on each goal -/

theorem topK_call (n : Name) (acc : List (List Rel)) : topK [.call n] acc = pure (true, acc) := by
  simp [topK, toRel, Rel.calls]

theorem topK_span (s : Span) (acc : List (List Rel)) :
    topK [.span s] acc = pure (false, acc ++ [[.span s]]) := by
  simp [topK, toRel, Rel.calls]

theorem onDemand_def (P : Program) (d : Nat) (g : Goal) :
    onDemand P d g = (walk P d false g.rel [] [] topK [] >>= fun r =>
      if r.1 then pure (false, []) else
        flatMapL (Tabled.live P.theory) (r.2.flatMap fun p => derivs (toRel p)) >>= fun xs =>
          pure (true, xs)) := rfl

theorem live_zz_val : (Tabled.live [] zz).val = [zz] := live_zz.1

theorem live_zz_ticks : (Tabled.live [] zz).ticks ≤ 3 := live_zz.2

theorem race_root (k d : Nat) : Costs (onDemand (prog k) d (gR k)) (false, []) (2 * d + k + 5) := by
  have hrel : (gR k).rel = .or (.call (chainName k)) (.call "w") := rfl
  rw [onDemand_def, hrel, walk, walk_chain k d k le_rfl]
  by_cases h : d ≤ k
  · simp only [h, ↓reduceIte, topK_call]
    exact ⟨rfl, by simp; omega⟩
  · simp only [h, ↓reduceIte, topK_span, List.nil_append]
    refine ⟨?_, ?_⟩
    · simp [walk_w]
    · simp [walk_w]; omega

theorem race_chain (k d j : Nat) (hj : j ≤ k) :
    Costs (onDemand (prog k) d (gC j)) (if j + 1 ≤ d then (true, [zz]) else (false, []))
      (2 * d + k + 5) := by
  have hrel : (gC j).rel = .call (chainName j) := rfl
  rw [onDemand_def, hrel, walk_chain k d j hj]
  by_cases h : d ≤ j
  · have h' : ¬ j + 1 ≤ d := by omega
    simp only [h, h', ↓reduceIte, topK_call]
    exact ⟨rfl, by simp; omega⟩
  · have h' : j + 1 ≤ d := by omega
    have ht := live_zz_ticks
    simp only [h, h', ↓reduceIte, topK_span, List.nil_append]
    refine ⟨?_, ?_⟩
    · simp [toRel, derivs, live_zz_val]
    · simp [toRel, derivs, flatMapL]; omega

theorem race_w (k d : Nat) : Costs (onDemand (prog k) d gW) (false, []) (2 * d + k + 5) := by
  have hrel : gW.rel = .call "w" := rfl
  rw [onDemand_def, hrel, walk_w k d []]
  exact ⟨rfl, by simp; omega⟩

theorem race_z (k d : Nat) : Costs (onDemand (prog k) d gZ) (true, [zz]) (2 * d + k + 5) := by
  have hrel : gZ.rel = .span zz := rfl
  have ht := live_zz_ticks
  rw [onDemand_def, hrel, walk]
  refine ⟨?_, ?_⟩
  · simp [alive, aliveL, aliveR, topK_span, toRel, derivs, live_zz_val]
  · simp [alive, aliveL, aliveR, topK_span, toRel, derivs, flatMapL]; omega

/-- The race on the goal of every table of the run. -/
theorem race (k d : Nat) (s : Slot) (hs : s.inAt k d) :
    Costs (onDemand (prog k) d (goal k s)) (uval d s) (2 * d + k + 5) := by
  cases s with
  | root => exact race_root k d
  | c j => exact race_chain k d j hs.1
  | w => exact race_w k d
  | z => exact race_z k d

end Sep

end R002

end RwLog
