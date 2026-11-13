/-
# The separating family: what R004 pays

The walk from the right reaches the test `q -> q` before `gen k`. It then
walks `gen k` with `q -> q` to its right: at the last choice neither wrapper
can be followed by the test, so nothing is handed back, and each choice before
it is visited once and finds nothing behind it (`walkR_gen`). The race pruned
from the right therefore costs `k + 37` ticks and returns the answer `a -> a`
(`pruned_g0`), and so does R004's race, within 7 times that (`unfolder_g0`).

The first round then emits `a -> a` (`round_st0`): the root has nothing to
read from other tables yet, and asks for the tables of its two branches.
-/
import RwLog.Rungs.R004.Proofs.Separation.Family
import RwLog.Rungs.R004.Proofs.SameMachine
import RwLog.Rungs.R003.Proofs.Separation.Run

namespace RwLog

namespace R004

namespace Sep

open Cost R000 R001

/-! ## The walk from the right -/

/-- A wrapper before `q -> q` is dropped where it stands. -/
theorem walkR_wrap {α : Type} {s : Span} (hs : Wrap s) (K : Path → α → Cost (Bool × α))
    (acc : α) : walkR P0 0 false (.span s) [qq] K acc = ⟨(false, acc), 11⟩ := by
  have hc := chain_wrap_qq hs
  rw [walkR]
  refine Cost.ext ?_ ?_
  · simp [fits, Charged.composable, hc]
  · simp [fits, Charged.composable, hc, size_wrap hs, size_qq]

/-- The walk of `gen j` before `q -> q` hands nothing on, and visits each
choice once. -/
theorem walkR_gen {α : Type} : ∀ (j : Nat) (K : Path → α → Cost (Bool × α)) (acc : α),
    walkR P0 0 false (gen j) [qq] K acc = ⟨(false, acc), j + 23⟩
  | 0, K, acc => by
    rw [gen, bit, walkR, walkR_wrap (Or.inl rfl)]
    simp only [walkR_wrap (Or.inr rfl : Wrap (wrap "1"))]
    refine Cost.ext ?_ ?_ <;> simp
  | j + 1, K, acc => by
    rw [gen, walkR, walkR_gen j]
    refine Cost.ext ?_ ?_
    · simp
    · simp only [bind_ticks, tick_ticks]; omega

theorem live_aa : Tabled.live [] aa = ⟨[aa], 3⟩ := by
  refine Cost.ext ?_ ?_
  · simp [Tabled.live, Charged.simplify, Theory.simplify, Theory.simplifyWithin,
      Theory.refutes?, Theory.firings, Store.varCount]
  · simp [Tabled.live, Charged.simplify, Theory.simplifyCharge, Theory.refutes?,
      Theory.firings, Store.varCount, R003.Sep.saturate_nil, Theory.size, Span.size, Store.size,
      Term.size]

/-- The race pruned from the right on the query: final, the answer `a -> a`,
`k + 37` ticks. -/
theorem pruned_g0 (k : Nat) : pruned P0 0 (g0 k) = ⟨(true, [aa]), k + 37⟩ := by
  have hrel : (g0 k).rel = .or (.span aa) (dead k) := rfl
  have hw : walkR P0 0 false (.or (.span aa) (dead k)) [] collect [] =
      ⟨(false, [(.inl .leaf, [.span aa])]), k + 34⟩ := by
    have h1 : walkR P0 0 false (.span aa) []
        (fun x acc => collect ⟨.inl x.key, x.pe⟩ acc) [] =
        ⟨(false, [(.inl .leaf, [.span aa])]), 6⟩ := by
      rw [walkR]
      refine Cost.ext ?_ ?_
      · simp [fits, collect, R002.Eager.norm, toRel, Rel.calls]
      · simp [fits, collect, R002.Eager.norm, toRel, Rel.calls, size_aa]
    have h2 : ∀ acc : List Found, walkR P0 0 false (dead k) []
        (fun y acc => collect ⟨.inr y.key, y.pe⟩ acc) acc = ⟨(false, acc), k + 27⟩ := by
      intro acc
      rw [walkR, walkR]
      simp only [Bool.false_eq_true, ↓reduceIte, fits, front, walkR_gen]
      refine Cost.ext ?_ ?_
      · simp
      · simp only [bind_ticks, tick_ticks, pure_val, pure_ticks, ↓reduceIte, size_qq]; omega
    rw [walkR, h1]
    simp only [h2]
    refine Cost.ext ?_ ?_ <;> simp
    omega
  rw [pruned, hrel, hw]
  refine Cost.ext ?_ ?_
  · simp [sort, foldL, insert, toRel, derivs, flatMapL, live_aa, R003.addSpan, anyL]
  · simp [sort, foldL, insert, toRel, derivs, flatMapL, live_aa, R003.addSpan, anyL]

/-- R004's race on the query: final, the answer `a -> a`, within 7 times the
race pruned from the right. -/
theorem unfolder_g0 (k : Nat) : ∃ T, T ≤ 7 * (k + 37) ∧
    unfolder P0 0 (g0 k) = ⟨(true, [aa]), T⟩ := by
  refine ⟨_, ?_, Cost.ext ?_ rfl⟩
  · have := unfolder_ticks_le_pruned P0 0 (g0 k)
    rw [pruned_g0] at this
    exact this
  · obtain ⟨h1, h2⟩ := unfolder_exact P0 0 (g0 k)
    obtain ⟨hf, ha⟩ := unfold_g0 k
    rw [hf] at h1
    rw [ha] at h2
    have h3 : (unfolder P0 0 (g0 k)).val.2 = [aa] := by
      rcases h2 with h | h
      · exact h
      · rw [h]; rfl
    exact Prod.ext h1 h3

/-! ## The first round -/

/-- The goals of the two branches of the query. -/
abbrev gA : Goal := ⟨none, .span aa, none⟩
abbrev gD (k : Nat) : Goal := ⟨none, dead k, none⟩

theorem norm_gA : gA.norm = (false, gA) := by
  rw [Goal.norm, canon, Goal.stripConv]
  intro lb a rb h
  cases h

theorem norm_gD (k : Nat) : (gD k).norm = (false, gD k) := by
  rw [Goal.norm, canon_dead, Goal.stripConv]
  intro lb a rb h
  cases h

theorem goalSize_g0 (k : Nat) : goalSize (g0 k) = 12 * k + 19 := by simp [goalSize, size_sepRel]
theorem goalSize_gA : goalSize gA = 3 := by simp [goalSize, Rel.size, size_aa]
theorem goalSize_gD (k : Nat) : goalSize (gD k) = 12 * k + 15 := by simp [goalSize, size_dead]

theorem same_g0_gA (k : Nat) : (g0 k).same gA = false := by simp [Goal.same, sepRel_eq]
theorem same_g0_gD (k : Nat) : (g0 k).same (gD k) = false := by simp [Goal.same, sepRel_eq]
theorem same_gA_gD (k : Nat) : gA.same (gD k) = false := by simp [Goal.same]

theorem round_st0 (k : Nat) : (Tabled.round unfolder (st0 k)).val.2 = [aa] ∧
    (Tabled.round unfolder (st0 k)).ticks + 12 * (k + 2) ≤ 1000 * (k + 2) := by
  obtain ⟨T, hT, hu⟩ := unfolder_g0 k
  have hcov : aa.covers? aa = true := by decide
  refine ⟨?_, ?_⟩
  · simp [Tabled.round, mapL, hu, Tabled.produce, Tabled.produceStrategies, sepRel_eq, orLeaves,
      orBranches, flatMapL, Tabled.answersOf, Tabled.norm, norm_gA, norm_gD, Tabled.findTable,
      findL, Tabled.same, same_g0_gA, same_g0_gD, same_gA_gD, Tabled.fresh, filterL, anyL,
      Tabled.maxima, foldL, Charged.covers, hcov, Tabled.completing, Tabled.gfpFrom, R001.orient]
  · simp [Tabled.round, mapL, hu, Tabled.produce, Tabled.produceStrategies, sepRel_eq, orLeaves,
      orBranches, flatMapL, Tabled.answersOf, Tabled.norm, norm_gA, norm_gD, Tabled.findTable,
      findL, Tabled.same, same_g0_gA, same_g0_gD, same_gA_gD, Tabled.fresh, filterL, anyL,
      Tabled.maxima, foldL, Charged.covers, hcov, Tabled.completing, Tabled.gfpFrom, R001.orient,
      goalSize_g0, goalSize_gA, goalSize_gD, size_aa]
    omega
end Sep

end R004

end RwLog
