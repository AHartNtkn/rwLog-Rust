/-
# The shared unfolding race at the kernel of the language

Each definition of `Gen.lean`, taken at the kernel of the language, is the
definition of `Shared.lean` with the same name. Where `Shared.lean` spells out
a comparison or the reading of an interface as ticks and a value, the generic
text calls the kernel, and the two are the same computation (`eqRel_then`,
`rightBound_std`, `eq_std`, `eqOpt_std`). So the engine built from the generic
race is, at that kernel, the machine the proofs are about (`engine_std`).
-/
import RwLog.Rungs.R003.Gen
import RwLog.Rungs.R003.Engine
import RwLog.Rungs.R002.Reading

namespace RwLog

namespace R003

open R001 Cost Traverse

/-! ## The kernel's operations, spelled out -/

theorem eqRel_then {β : Type} (a b : Rel) (X Y : Cost β) :
    (do let r ← Kernel.eqRel a b; if r then X else Y) =
      (do tick (a.size + b.size); if a = b then X else Y) := by
  by_cases h : a = b
  · show (Charged.eqRel a b >>= _) = _
    simp only [Charged.eqRel, h, ite_true]
    rfl
  · show (Charged.eqRel a b >>= _) = _
    simp only [Charged.eqRel, h, ite_false]
    rfl
theorem rightBound_std (a : Span) : (Kernel.rightBound a : Cost _) = (do tick a.size; pure (bound a.rightIface)) := rfl
theorem eq_std (x y : Span) : (Kernel.eq y x : Cost _) = (do tick (x.size + y.size); pure (decide (y = x))) :=
  Cost.ext rfl (by show y.size + x.size = x.size + y.size + 0; omega)
theorem eqOpt_std : ∀ x y : Option Span,
    Gen.eqOpt y x = (do tick (optSize x + optSize y); pure (decide (y = x)))
  | none, none => Cost.ext (by show true = decide ((none : Option Span) = none); simp) rfl
  | none, some b => Cost.ext (by show false = decide (some b = none); simp)
      (by show b.size + 1 + 0 = 1 + b.size + 0; omega)
  | some a, none => Cost.ext (by show false = decide (none = some a); simp)
      (by show 1 + a.size + 0 = a.size + 1 + 0; omega)
  | some a, some b => Cost.ext (by show decide (b = a) = decide (some b = some a); simp)
      (by show b.size + a.size = a.size + b.size + 0; omega)

/-! ## The definitions -/

theorem sameCtx_std (a b : Option Span) : Gen.sameCtx a b = sameCtx a b := by
  unfold Gen.sameCtx sameCtx; same_text

theorem sameKey_std (k k' : Key) : Gen.sameKey k k' = sameKey k k' := by
  simp only [Gen.sameKey, sameKey, sameCtx_std, eqRel_then]
  rfl

theorem lookup_std (m : Memo) (k : Key) : Gen.lookup m k = lookup m k := by
  simp only [Gen.lookup, lookup, sameKey_std, findL_std]

theorem alive_std (ctx : Option Span) (s : Span) : Gen.alive ctx s = alive ctx s := by
  unfold Gen.alive alive; same_text

theorem extend_std (ctx : Option Span) (a : Span) : Gen.extend ctx a = extend ctx a := by
  simp only [Gen.extend, extend, rightBound_std]; same_text

theorem addSpan_std (xs : List Span) (x : Span) : Gen.addSpan xs x = addSpan xs x := by
  simp only [Gen.addSpan, addSpan, eq_std, anyL_std]

theorem addOpen_std (xs : List (Option Span)) (x : Option Span) :
    Gen.addOpen xs x = addOpen xs x := by
  simp only [Gen.addOpen, addOpen, eqOpt_std, anyL_std]

theorem memo_std (k : Key) (m : Memo) (body : Memo → Cost (Summary × Memo)) :
    Gen.memo k m body = memo k m body := by
  simp only [Gen.memo, memo, lookup_std]; same_text

theorem afterSpan_std (ctx : Option Span) (second : Option Span → Memo → Cost (Summary × Memo))
    (acc : Acc) (x : Span) : Gen.afterSpan ctx second acc x = afterSpan ctx second acc x := by
  simp only [Gen.afterSpan, afterSpan, extend_std, filterMapL_std, foldL_std,
    funext fun xs => funext (addSpan_std xs), funext fun xs => funext (addOpen_std xs)]
  rfl

theorem afterOpen_std (second : Option Span → Memo → Cost (Summary × Memo))
    (acc : Acc) (c : Option Span) : Gen.afterOpen second acc c = afterOpen second acc c := by
  simp only [Gen.afterOpen, afterOpen, funext (extend_std _), mapL_std, foldL_std,
    funext fun xs => funext (addOpen_std xs)]

theorem seqSummary_std (ctx : Option Span) (first : Summary)
    (second : Option Span → Memo → Cost (Summary × Memo)) (m : Memo) :
    Gen.seqSummary ctx first second m = seqSummary ctx first second m := by
  have h1 : Gen.afterSpan ctx second = afterSpan ctx second :=
    funext fun acc => funext fun x => afterSpan_std ctx second acc x
  have h2 : Gen.afterOpen second = afterOpen second :=
    funext fun acc => funext fun c => afterOpen_std second acc c
  simp only [Gen.seqSummary, seqSummary, foldL_std, h1, h2]

theorem andSummary_std (ctx : Option Span) (a b : Summary) :
    Gen.andSummary ctx a b = andSummary ctx a b := by
  simp only [Gen.andSummary, andSummary, flatMapL_std, filterMapL_std, filterL_std, foldL_std,
    funext (alive_std _), funext fun xs => funext (addSpan_std xs)]
  rfl

/-- The evaluation at one depth, given the evaluation of a call at that
depth. -/
theorem eval_std_step (P : Program) (d : Nat)
    (hcall : ∀ neg n ctx m, Gen.eval P d neg (.call n) ctx m = eval P d neg (.call n) ctx m) :
    ∀ (e : Rel) neg ctx m, Gen.eval P d neg e ctx m = eval P d neg e ctx m := by
  intro e
  induction e with
  | zero => intro neg ctx m; rw [Gen.eval, eval]; rfl
  | span s => intro neg ctx m; rw [Gen.eval, eval]; simp only [alive_std]; rfl
  | or a b iha ihb =>
    intro neg ctx m
    rw [Gen.eval, eval]
    simp only [iha, ihb, memo_std, foldL_std, funext fun xs => funext (addSpan_std xs),
      funext fun xs => funext (addOpen_std xs)]
    rfl
  | and a b iha ihb =>
    intro neg ctx m
    rw [Gen.eval, eval]
    simp only [iha, ihb, memo_std, andSummary_std]; rfl
  | seq a b iha ihb =>
    intro neg ctx m
    cases neg <;> rw [Gen.eval, eval] <;> simp only [iha, ihb, memo_std, seqSummary_std] <;> rfl
  | conv a ih => intro neg ctx m; rw [Gen.eval, eval]; simp only [ih]; rfl
  | call n => exact fun neg ctx m => hcall neg n ctx m

theorem eval_std (P : Program) : ∀ (d : Nat) (e : Rel) neg ctx m,
    Gen.eval P d neg e ctx m = eval P d neg e ctx m
  | 0 => eval_std_step P 0 fun neg n ctx m => by rw [Gen.eval, eval]; rfl
  | d + 1 => eval_std_step P (d + 1) fun neg n ctx m => by
    rw [Gen.eval, eval]; simp only [eval_std P d, memo_std]; rfl

theorem shared_std (P : Program) (d : Nat) (g : Goal) : Gen.shared P d g = shared P d g := by
  simp only [Gen.shared, shared, eval_std, flatMapL_std, foldL_std, funext (Tabled.live_std _),
    funext fun xs => funext (addSpan_std xs)]

theorem unfolder_std (P : Program) (d : Nat) (g : Goal) : Gen.unfolder P d g = unfolder P d g := by
  simp only [Gen.unfolder, unfolder, R002.onDemand_std, shared_std]; rfl

theorem engine_std : engine.costed = costed := by
  unfold engine
  rw [Tabled.engine_costed]
  show Tabled.machine (fun P d g => Gen.unfolder P d g) = Tabled.machine unfolder
  simp only [unfolder_std]

end R003

end RwLog
