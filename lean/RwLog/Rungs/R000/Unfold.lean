/-
# Unfolding, as a function on expressions

`unfold` and `unfoldN` are defined in `Normalize.lean`. These are their
equations: how `unfoldN` steps, that it commutes with every constructor, what
it does to a call, and that it commutes with the converse of a program. Every
rung that unfolds (eagerly or on demand) is compared against these.
-/
import RwLog.Rungs.R000.Normalize
import RwLog.SpanLayer.Dual

namespace RwLog

namespace R000

variable (P : Program)

@[simp] theorem unfoldN_zero_apply (e : Rel) : unfoldN P 0 e = e := rfl

/-- Unfold once more on the outside. -/
theorem unfoldN_succ (k : Nat) (e : Rel) : unfoldN P (k + 1) e = unfold P (unfoldN P k e) := by
  simp only [unfoldN, Function.iterate_succ_apply']

/-- Unfold once more on the inside. -/
theorem unfoldN_succ' (k : Nat) (e : Rel) : unfoldN P (k + 1) e = unfoldN P k (unfold P e) := rfl

theorem unfoldN_add (j k : Nat) (e : Rel) : unfoldN P (j + k) e = unfoldN P j (unfoldN P k e) := by
  simp only [unfoldN, Function.iterate_add_apply]

theorem unfoldN_zero (k : Nat) : unfoldN P k .zero = .zero := by
  induction k with
  | zero => rfl
  | succ k ih => rw [unfoldN_succ, ih]; rfl

theorem unfoldN_span (k : Nat) (s : Span) : unfoldN P k (.span s) = .span s := by
  induction k with
  | zero => rfl
  | succ k ih => rw [unfoldN_succ, ih]; rfl

theorem unfoldN_or (k : Nat) (a b : Rel) :
    unfoldN P k (.or a b) = .or (unfoldN P k a) (unfoldN P k b) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [unfoldN_succ, ih, unfold]

theorem unfoldN_and (k : Nat) (a b : Rel) :
    unfoldN P k (.and a b) = .and (unfoldN P k a) (unfoldN P k b) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [unfoldN_succ, ih, unfold]

theorem unfoldN_seq (k : Nat) (a b : Rel) :
    unfoldN P k (.seq a b) = .seq (unfoldN P k a) (unfoldN P k b) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [unfoldN_succ, ih, unfold]

theorem unfoldN_conv (k : Nat) (a : Rel) : unfoldN P k (.conv a) = .conv (unfoldN P k a) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [unfoldN_succ, ih, unfold]

/-- Unfolding a call `k + 1` times is unfolding its body `k` times. -/
theorem unfoldN_call (k : Nat) (n : Name) :
    unfoldN P (k + 1) (.call n) = unfoldN P k (P.body n) := rfl

theorem unfold_dual : ∀ e : Rel, unfold P.dual e.dual = (unfold P e).dual
  | .zero => rfl
  | .span _ => rfl
  | .or a b => by simp only [Rel.dual, unfold, unfold_dual a, unfold_dual b]
  | .and a b => by simp only [Rel.dual, unfold, unfold_dual a, unfold_dual b]
  | .seq a b => by simp only [Rel.dual, unfold, unfold_dual a, unfold_dual b]
  | .conv a => by simp only [Rel.dual, unfold, unfold_dual a]
  | .call n => by simp only [Rel.dual, unfold, Program.dual_body]

theorem unfoldN_dual (k : Nat) (e : Rel) : unfoldN P.dual k e.dual = (unfoldN P k e).dual := by
  induction k with
  | zero => rfl
  | succ k ih => rw [unfoldN_succ, unfoldN_succ, ih, unfold_dual]

end R000

end RwLog
