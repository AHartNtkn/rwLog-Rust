/-
# The unfolding races at the kernel of the language

Each definition of `Gen.lean`, taken at the kernel of the language, is the
definition of `Unfold.lean` with the same name. So the engines built from the
generic races are, at that kernel, the machines the proofs are about
(`baselineEngine_std`, `engine_std`).
-/
import RwLog.Rungs.R002.Gen
import RwLog.Rungs.R002.Engine
import RwLog.Rungs.Tabled.Reading

namespace RwLog

namespace R002

open R000 Cost Traverse

theorem toRel_std : ∀ p : List Rel, Gen.toRel p = toRel p
  | [] => rfl
  | [_] => rfl
  | f :: g :: fs => by simp only [Gen.toRel, toRel, toRel_std (g :: fs)]

theorem single_std (p : List Rel) : Gen.single p = single p := by
  unfold Gen.single single; same_text

theorem closed_std (N : List (List Rel)) : Gen.closed N = closed N := by
  simp only [Gen.closed, closed, funext single_std]

theorem headSpan_std (p : List Rel) : Gen.headSpan p = headSpan p := by
  unfold Gen.headSpan headSpan; same_text

theorem lastSpan_std (p : List Rel) : Gen.lastSpan p = lastSpan p := by
  unfold Gen.lastSpan lastSpan; same_text

theorem staticFirst_std : ∀ (e : Rel) (neg : Bool), Gen.staticFirst neg e = staticFirst neg e := by
  intro e
  induction e with
  | seq a b iha ihb => intro neg; cases neg <;> simp only [Gen.staticFirst, staticFirst, iha, ihb]
  | conv a ih => intro neg; simp only [Gen.staticFirst, staticFirst, ih]
  | _ => intro neg; cases neg <;> rfl

theorem rightOf_std (neg : Bool) (e : Rel) (R : List Span) : Gen.rightOf neg e R = rightOf neg e R := by
  simp only [Gen.rightOf, rightOf, staticFirst_std]; same_text

theorem leftAfter_std (L : List Span) (p : List Rel) : Gen.leftAfter L p = leftAfter L p := by
  simp only [Gen.leftAfter, leftAfter, lastSpan_std]; same_text

namespace Eager

theorem unfold_std (P : Program) : ∀ e : Rel, Gen.Eager.unfold P e = unfold P e := by
  intro e
  induction e with
  | or a b iha ihb => simp only [Gen.Eager.unfold, unfold, iha, ihb]; rfl
  | and a b iha ihb => simp only [Gen.Eager.unfold, unfold, iha, ihb]; rfl
  | seq a b iha ihb => simp only [Gen.Eager.unfold, unfold, iha, ihb]; rfl
  | conv a ih => simp only [Gen.Eager.unfold, unfold, ih]; rfl
  | _ => rfl

theorem unfoldN_std (P : Program) : ∀ (k : Nat) (e : Rel), Gen.Eager.unfoldN P k e = unfoldN P k e
  | 0, _ => rfl
  | k + 1, e => by simp only [Gen.Eager.unfoldN, unfoldN, unfold_std, unfoldN_std P k]

end Eager

theorem joinSeq_std (p q : List Rel) : Gen.joinSeq p q = joinSeq p q := by
  unfold Gen.joinSeq joinSeq; same_text

theorem mkAnd_std (p q : List Rel) : Gen.mkAnd p q = mkAnd p q := by
  simp only [Gen.mkAnd, mkAnd, toRel_std]; same_text

namespace Eager

theorem norm_std : ∀ (e : Rel) (neg : Bool), Gen.Eager.norm neg e = norm neg e := by
  intro e
  induction e with
  | zero => intro neg; rfl
  | span s => intro neg; rfl
  | or a b iha ihb => intro neg; simp only [Gen.Eager.norm, norm, iha, ihb]; rfl
  | and a b iha ihb =>
    intro neg
    simp only [Gen.Eager.norm, norm, iha, ihb, flatMapL_std, filterMapL_std, funext (mkAnd_std _)]
    rfl
  | seq a b iha ihb =>
    intro neg
    cases neg <;>
      simp only [Gen.Eager.norm, norm, iha, ihb, flatMapL_std, filterMapL_std,
        funext (joinSeq_std _)] <;> rfl
  | conv a ih => intro neg; simp only [Gen.Eager.norm, norm, ih]; rfl
  | call n => intro neg; rfl

end Eager

theorem eager_std (P : Program) (d : Nat) (g : R001.Goal) : Gen.eager P d g = eager P d g := by
  simp only [Gen.eager, eager, Eager.unfoldN_std, Eager.norm_std, toRel_std, closed_std,
    flatMapL_std, funext (Tabled.live_std _)]

theorem aliveL_std (L : List Span) (p : List Rel) : Gen.aliveL L p = aliveL L p := by
  simp only [Gen.aliveL, aliveL, headSpan_std]; same_text

theorem aliveR_std (p : List Rel) (R : List Span) : Gen.aliveR p R = aliveR p R := by
  simp only [Gen.aliveR, aliveR, lastSpan_std]; same_text

theorem alive_std (L : List Span) (p : List Rel) (R : List Span) : Gen.alive L p R = alive L p R := by
  simp only [Gen.alive, alive, aliveL_std, aliveR_std]

/-- The walk at one depth, given the walk of a call at that depth. -/
theorem walk_std_step (P : Program) (d : Nat)
    (hcall : ∀ neg n L R k acc,
      Gen.walk P d neg (.call n) L R k acc = walk P d neg (.call n) L R k acc) :
    ∀ (e : Rel) neg L R k acc, Gen.walk P d neg e L R k acc = walk P d neg e L R k acc := by
  intro e
  induction e with
  | zero => intro neg L R k acc; rw [Gen.walk, walk]; rfl
  | span s => intro neg L R k acc; rw [Gen.walk, walk]; simp only [alive_std]; rfl
  | or a b iha ihb =>
    intro neg L R k acc
    rw [Gen.walk, walk]
    simp only [iha, ihb]; rfl
  | and a b iha ihb =>
    intro neg L R k acc
    rw [Gen.walk, walk]
    simp only [iha, ihb, mkAnd_std, alive_std]; same_text
  | seq a b iha ihb =>
    intro neg L R k acc
    cases neg <;> rw [Gen.walk, walk] <;>
      simp only [iha, ihb, joinSeq_std, aliveR_std, rightOf_std, leftAfter_std] <;> same_text
  | conv a ih => intro neg L R k acc; rw [Gen.walk, walk]; simp only [ih]; rfl
  | call n => exact fun neg L R k acc => hcall neg n L R k acc

theorem walk_std (P : Program) : ∀ (d : Nat) (e : Rel) neg L R k acc,
    Gen.walk P d neg e L R k acc = walk P d neg e L R k acc
  | 0 => walk_std_step P 0 fun neg n L R k acc => by rw [Gen.walk, walk]; rfl
  | d + 1 => walk_std_step P (d + 1) fun neg n L R k acc => by
    rw [Gen.walk, walk, walk_std P d]; rfl

theorem onDemand_std (P : Program) (d : Nat) (g : R001.Goal) : Gen.onDemand P d g = onDemand P d g := by
  simp only [Gen.onDemand, onDemand, walk_std, toRel_std, closed_std, flatMapL_std,
    funext (Tabled.live_std _)]

theorem baselineEngine_std : baselineEngine.costed = baseline := by
  unfold baselineEngine
  rw [Tabled.engine_costed]
  show Tabled.machine (fun P d g => Gen.eager P d g) = Tabled.machine eager
  simp only [eager_std]

theorem engine_std : engine.costed = costed := by
  unfold engine
  rw [Tabled.engine_costed]
  show Tabled.machine (fun P d g => Gen.onDemand P d g) = Tabled.machine onDemand
  simp only [onDemand_std]

end R002

end RwLog
