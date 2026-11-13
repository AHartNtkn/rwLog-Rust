/-
# The pruned unfolding race at the kernel of the language

Each definition of `Gen.lean`, taken at the kernel of the language, is the
definition of `Pruned.lean` with the same name. So the engine built from the
generic race is, at that kernel, the machine the proofs are about
(`engine_std`).
-/
import RwLog.Rungs.R004.Gen
import RwLog.Rungs.R004.Engine
import RwLog.Rungs.R003.Reading

namespace RwLog

namespace R004

open R000 R001 Cost Traverse

theorem front_std : ∀ (e : Rel) (R : List Span), Gen.front e R = front e R := by
  intro e
  induction e with
  | seq a b iha ihb => intro R; simp only [Gen.front, front, iha, ihb]
  | _ => intro R; rfl

theorem fits_std (s : Span) (R : List Span) : Gen.fits s R = fits s R := by
  unfold Gen.fits fits; same_text

/-- The walk at one depth, given the walk of a call at that depth. -/
theorem walkR_std_step {α : Type} (P : Program) (d : Nat)
    (hcall : ∀ neg n R (k : Path → α → Cost (Bool × α)) acc,
      Gen.walkR P d neg (.call n) R k acc = walkR P d neg (.call n) R k acc) :
    ∀ (e : Rel) neg R (k : Path → α → Cost (Bool × α)) acc,
      Gen.walkR P d neg e R k acc = walkR P d neg e R k acc := by
  intro e
  induction e with
  | zero => intro neg R k acc; rw [Gen.walkR, walkR]; rfl
  | span s => intro neg R k acc; rw [Gen.walkR, walkR]; simp only [fits_std]; rfl
  | or a b iha ihb => intro neg R k acc; rw [Gen.walkR, walkR]; simp only [iha, ihb]; rfl
  | and a b iha ihb => intro neg R k acc; rw [Gen.walkR, walkR]; simp only [iha, ihb]; rfl
  | seq a b iha ihb =>
    intro neg R k acc
    cases neg <;> rw [Gen.walkR, walkR] <;> simp only [iha, ihb, front_std] <;> rfl
  | conv a ih => intro neg R k acc; rw [Gen.walkR, walkR]; simp only [ih]; rfl
  | call n => exact fun neg R k acc => hcall neg n R k acc

theorem walkR_std {α : Type} (P : Program) : ∀ (d : Nat) (e : Rel) neg R
    (k : Path → α → Cost (Bool × α)) acc, Gen.walkR P d neg e R k acc = walkR P d neg e R k acc
  | 0 => walkR_std_step P 0 fun neg n R k acc => by rw [Gen.walkR, walkR]; rfl
  | d + 1 => walkR_std_step P (d + 1) fun neg n R k acc => by
    rw [Gen.walkR, walkR, walkR_std P d]; rfl

theorem collect_std (x : Path) (acc : List Found) : Gen.collect x acc = collect x acc := by
  simp only [Gen.collect, collect, R002.Eager.norm_std, R002.toRel_std]

theorem before_std (x y : Found) : Gen.before x y = before x y := rfl

theorem insert_std (x : Found) : ∀ ys : List Found, Gen.insert x ys = insert x ys
  | [] => rfl
  | y :: ys => by simp only [Gen.insert, insert, before_std, insert_std x ys]

theorem sort_std (xs : List Found) : Gen.sort xs = sort xs := by
  have h : (fun acc x => Gen.insert x acc) = fun (acc : List Found) x => insert x acc :=
    funext fun acc => funext fun x => insert_std x acc
  simp only [Gen.sort, sort, foldL_std, h]

theorem pruned_std (P : Program) (d : Nat) (g : Goal) : Gen.pruned P d g = pruned P d g := by
  have h : (Gen.collect : Path → List Found → Cost (Bool × List Found)) = collect :=
    funext fun x => funext fun acc => collect_std x acc
  simp only [Gen.pruned, pruned, walkR_std, h, sort_std, R002.closed_std, flatMapL_std, foldL_std,
    funext (Tabled.live_std _), funext fun xs => funext (R003.addSpan_std xs)]

theorem unfolder_std (P : Program) (d : Nat) (g : Goal) : Gen.unfolder P d g = unfolder P d g := by
  simp only [Gen.unfolder, unfolder, R003.unfolder_std, pruned_std]; rfl

theorem engine_std : engine.costed = costed := by
  unfold engine
  rw [Tabled.engine_costed]
  show Tabled.machine (fun P d g => Gen.unfolder P d g) = Tabled.machine unfolder
  simp only [unfolder_std]

end R004

end RwLog
