/-
# The tabled engine at the kernel of the language

`Gen.lean` writes the tabled round machine against an arbitrary kernel.
`Machine.lean` is the same text in the cost monad with the charged primitives
written out. Here each definition of the first, taken at the kernel of the
language, is shown equal to the definition of the second with the same name,
so `(Tabled.Gen.engine U).costed` is `Tabled.machine` with `U` read at that
kernel (`engine_costed`). The proofs about the machine are carried out on the
reading and hold of the engine by this equality.
-/
import RwLog.Rungs.Tabled.Gen
import RwLog.Rungs.Tabled.Machine
import RwLog.Rungs.Framework.TraverseStd
import RwLog.Rungs.Framework.Cost
import RwLog.Rungs.Tabled.Base.Proofs.SymmetryGoals

namespace RwLog

open R001 Cost Traverse

theorem Gen.relSize_std : ∀ e : Rel, Gen.relSize e = e.size
  | .zero => rfl
  | .span _ => rfl
  | .or a b => by simp only [Gen.relSize, RelOf.size, relSize_std a, relSize_std b]
  | .and a b => by simp only [Gen.relSize, RelOf.size, relSize_std a, relSize_std b]
  | .seq a b => by simp only [Gen.relSize, RelOf.size, relSize_std a, relSize_std b]
  | .conv a => by simp only [Gen.relSize, RelOf.size, relSize_std a]
  | .call _ => rfl

theorem Gen.goalSize_std (g : Goal) : Gen.goalSize g = RwLog.goalSize g := by
  simp only [Gen.goalSize, RwLog.goalSize, Gen.relSize_std]
  rfl

namespace Tabled

theorem stripConv_std : ∀ (e : Rel) (lb rb : Option Span),
    Gen.stripConv lb e rb = GoalOf.stripConv ⟨lb, e, rb⟩ := by
  intro e
  induction e with
  | conv a ih =>
    intro lb rb
    rw [Gen.stripConv, R001.Symmetry.stripConv_conv, ih]
    rfl
  | _ =>
    intro lb rb
    rw [R001.Symmetry.stripConv_other _ _ _ (by intro a h; cases h)]
    rfl

theorem norm_std (g : Goal) : Gen.norm g = norm g := by
  refine Cost.ext ?_ ?_
  · show Gen.stripConv g.lb (canon g.e) g.rb = g.norm
    rw [stripConv_std]; rfl
  · show g.e.size + (((g.lb.toList ++ g.rb.toList).map Span.size).sum + 0) = goalSize g
    rfl

theorem sameBound_std (a b : Option Span) : Gen.sameBound a b = sameBound a b := by
  cases a <;> cases b <;> same_text

theorem same_std (g h : Goal) : Gen.same g h = same g h := by
  simp only [Gen.same, same, sameBound_std]
  rfl

theorem findTable_std (ts : Tables) (g : Goal) : Gen.findTable ts g = findTable ts g := by
  simp only [Gen.findTable, findTable, same_std, findL_std]

theorem indexFrom_std (g : Goal) : ∀ (i : Nat) (ts : Tables),
    Gen.indexFrom g i ts = indexFrom g i ts
  | _, [] => rfl
  | i, t :: ts => by simp only [Gen.indexFrom, indexFrom, same_std, indexFrom_std g (i + 1) ts]

theorem indexOf_std (ts : Tables) (g : Goal) : Gen.indexOf ts g = indexOf ts g := by
  simp only [Gen.indexOf, indexOf, indexFrom_std]

theorem orient_std (flip : Bool) (xs : List Span) : Gen.orient flip xs = orient flip xs := rfl

theorem convGoal_std (g : Goal) (a : Rel) : Gen.convGoal g a = convGoal g a := rfl

theorem answersOf_std (ts : Tables) (g : Goal) : Gen.answersOf ts g = answersOf ts g := by
  simp only [Gen.answersOf, answersOf, norm_std, findTable_std, orient_std]
  same_text

theorem doneOf_std (ts : Tables) (g : Goal) : Gen.doneOf ts g = doneOf ts g := by
  simp only [Gen.doneOf, doneOf, norm_std, findTable_std]
  same_text

theorem live_std (T : Theory) (s : Span) : Gen.live T s = live T s := rfl

theorem composeLive_std (T : Theory) (x y : Span) : Gen.composeLive T x y = composeLive T x y := by
  simp only [Gen.composeLive, composeLive, live_std]
  same_text

theorem meetLive_std (T : Theory) (x y : Span) : Gen.meetLive T x y = meetLive T x y := by
  simp only [Gen.meetLive, meetLive, live_std]
  same_text

theorem spanAnswer_std (T : Theory) (lb : Option Span) (s : Span) (rb : Option Span) :
    Gen.spanAnswer T lb s rb = spanAnswer T lb s rb := by
  simp only [Gen.spanAnswer, spanAnswer, live_std]
  same_text

theorem maxima_std (xs : List Span) : Gen.maxima xs = maxima xs := by
  simp only [Gen.maxima, maxima, filterL_std, anyL_std, foldL_std]
  same_text

theorem fresh_std (old cands : List Span) : Gen.fresh old cands = fresh old cands := by
  simp only [Gen.fresh, fresh, filterL_std, anyL_std, maxima_std]
  same_text

theorem seqPushL_std (g : Goal) (b : Rel) (x : Span) : Gen.seqPushL g b x = seqPushL g b x := rfl

theorem seqPushR_std (g : Goal) (a : Rel) (y : Span) : Gen.seqPushR g a y = seqPushR g a y := rfl

theorem andPush_std (e : Rel) (x : Span) : Gen.andPush e x = andPush e x := rfl

theorem pushes_std (f : Span → Cost Goal) (xs : List Span) : Gen.pushes f xs = pushes f xs := by
  simp only [Gen.pushes, pushes, mapL_std]

theorem produceStrategies_std (P : Program) (ts : Tables) (g : Goal) :
    Gen.produceStrategies P ts g = produceStrategies P ts g := by
  obtain ⟨lb, e, rb⟩ := g
  cases e <;>
    simp only [Gen.produceStrategies, produceStrategies, spanAnswer_std, answersOf_std, funext (answersOf_std _),
      doneOf_std, flatMapL_std, composeLive_std, meetLive_std, maxima_std, pushes_std,
      convGoal_std, funext (seqPushL_std _ _), funext (seqPushR_std _ _),
      funext (andPush_std _)]
  all_goals same_text

theorem produce_std (P : Program) (ts : Tables) (g : Goal) (u : Bool × List Span) :
    Gen.produce P ts g u = produce P ts g u := by
  simp only [Gen.produce, produce, produceStrategies_std]

theorem tableStrategies_std (P : Program) (ts : Tables) (g : Goal) :
    Gen.tableStrategies P ts g = tableStrategies P ts g := by
  obtain ⟨lb, e, rb⟩ := g
  cases e <;>
    simp only [Gen.tableStrategies, tableStrategies, answersOf_std, doneOf_std, maxima_std,
      mapL_std, convGoal_std, funext (seqPushL_std _ _), funext (seqPushR_std _ _),
      funext (andPush_std _)]

theorem strategies_std (P : Program) (final : Bool) (ts : Tables) (g : Goal) :
    Gen.strategies P final ts g = strategies P final ts g := by
  simp only [Gen.strategies, strategies, tableStrategies_std]

theorem gfpFrom_std (ok : List Nat → Nat → Cost Bool) : ∀ (n : Nat) (S : List Nat),
    Gen.gfpFrom ok n S = gfpFrom ok n S
  | 0, _ => rfl
  | n + 1, S => by simp only [Gen.gfpFrom, gfpFrom, filterL_std, gfpFrom_std ok n]

theorem completing_std (P : Program) (finals : List Bool) (ts ts' : Tables) :
    Gen.completing P finals ts ts' = completing P finals ts ts' := by
  simp only [Gen.completing, completing, strategies_std, anyL_std, allL_std, norm_std,
    indexOf_std, gfpFrom_std]
  same_text

theorem round_std (U : Oracle) (st : State) : Gen.round U st = round U st := by
  simp only [Gen.round, round, mapL_std, foldL_std, anyL_std, produce_std, fresh_std, norm_std,
    same_std, completing_std, Gen.goalSize_std, orient_std]
  refine bind_congr fun _ => bind_congr fun _ => bind_congr fun _ => bind_congr fun ts1 =>
    bind_congr fun _ => bind_congr fun _ => bind_congr fun _ => ?_
  cases st.tables.head? <;> cases ts1.head? <;> rfl

theorem step_std (U : Oracle) (st : State) : Gen.step U st = step U st := by
  simp only [Gen.step, step, round_std]

theorem ofGoal_std (P : Program) (g : Goal) : Gen.ofGoal P g = ofGoal P g := by
  simp only [Gen.ofGoal, ofGoal, norm_std]

/-- The tabled engine at the kernel of the language is the tabled machine
with the engine's unfolding race read at that kernel. -/
theorem engine_costed (U : Unfolder) : (Gen.engine U).costed = machine U := by
  show (⟨State, fun P q => Gen.ofGoal P ⟨none, q, none⟩, fun st => Gen.step U st⟩ :
    CostedRuntime) = ⟨State, fun P q => ofGoal P ⟨none, q, none⟩, fun st => step U st⟩
  simp only [ofGoal_std, step_std]

end Tabled

end RwLog
