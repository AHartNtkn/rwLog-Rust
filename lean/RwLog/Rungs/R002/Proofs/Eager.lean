/-
# The eager unfolder is R001's unfolding race

Forgetting the ticks of the charged traversals gives the list functions of the
same name, the charged unfolding and normalizer give rung zero's, and so
`eager` returns exactly `(R001.unfoldFinal, R001.unfoldAnswers)`.
-/
import RwLog.Rungs.R002.Spec
import RwLog.Rungs.Framework.Cost
import RwLog.Rungs.R002.Proofs.Closed

namespace RwLog

namespace R002

open Cost

/-! ## The charged normalizer is rung zero's -/

theorem joinSeq_val (p q : List Rel) : (R002.joinSeq p q).val = R000.joinSeq p q := by
  unfold R002.joinSeq R000.joinSeq
  split
  · rename_i h
    simp only [h]
    rfl
  · rename_i h
    split
    · rename_i h₁
      exact (h _ _ _ h₁ rfl).elim
    · rfl

theorem mkAnd_val (p q : List Rel) : (R002.mkAnd p q).val = R000.mkAnd p q := by
  unfold R002.mkAnd R000.mkAnd
  split
  · rfl
  · rename_i h
    split
    · exact (h _ _ rfl rfl).elim
    · rfl

theorem live_val (T : Theory) (s : Span) : (Tabled.live T s).val = RwLog.live T s := rfl

namespace Eager

theorem unfold_val (P : Program) (e : Rel) : (unfold P e).val = R000.unfold P e := by
  induction e with
  | zero => rfl
  | span s => rfl
  | or a b iha ihb => simp only [unfold, bind_val, pure_val, iha, ihb, R000.unfold]
  | and a b iha ihb => simp only [unfold, bind_val, pure_val, iha, ihb, R000.unfold]
  | seq a b iha ihb => simp only [unfold, bind_val, pure_val, iha, ihb, R000.unfold]
  | conv a iha => simp only [unfold, bind_val, pure_val, iha, R000.unfold]
  | call n => rfl

theorem unfoldN_val (P : Program) (k : Nat) (e : Rel) :
    (unfoldN P k e).val = R000.unfoldN P k e := by
  induction k generalizing e with
  | zero => rfl
  | succ k ih =>
    simp only [unfoldN, bind_val, unfold_val, ih]
    rfl

theorem norm_val (neg : Bool) (e : Rel) : (norm neg e).val = R000.norm neg e := by
  induction e generalizing neg with
  | zero => rfl
  | span s => rfl
  | or a b iha ihb => simp only [norm, bind_val, pure_val, iha, ihb, R000.norm]
  | and a b iha ihb =>
    simp only [norm, bind_val, flatMapL_val, filterMapL_val, mkAnd_val, iha, ihb, R000.norm]
  | seq a b iha ihb =>
    cases neg <;>
      simp only [norm, bind_val, flatMapL_val, filterMapL_val, joinSeq_val, iha, ihb, R000.norm]
  | conv a iha => simp only [norm, bind_val, iha, R000.norm]
  | call n => rfl

end Eager

/-- The answers of a final unfolding, with the ticks forgotten. -/
theorem answers_val (T : Theory) (xs : List Span) :
    (flatMapL (Tabled.live T) xs).val = xs.flatMap (RwLog.live T) := by
  rw [flatMapL_val]; rfl

/-- The eager unfolder computes R001's unfolding race. -/
theorem eager_exact : Obligation.eager_exact := by
  intro P d g
  unfold eager
  simp only [bind_val, Eager.unfoldN_val, Eager.norm_val]
  unfold R001.unfoldAnswers R001.unfoldFinal R000.roundFinal R000.roundSpans R000.products
  split
  · rename_i h
    simp only [bind_val, pure_val, answers_val, h, closed_eq_derivs _ _ h]
  · rename_i h
    simp only [pure_val, h]

end R002

end RwLog
