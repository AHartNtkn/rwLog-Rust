/-
# The goal-directed engine at the kernel of the language

Each definition of `Gen.lean`, taken at the kernel of the language, is the
definition of `Machine.lean` with the same name, so `Directed.Gen.engine`
there is `Directed.machine` (`engine_costed`).
-/
import RwLog.Rungs.Directed.Machine
import RwLog.Rungs.Tabled.Reading

namespace RwLog

open R001 Cost Traverse

namespace Directed

open Tabled

theorem seqCandidates_std (P : Program) (ts : Tables) (g : Goal) (a b : Rel) :
    Gen.seqCandidates P ts g a b = seqCandidates P ts g a b := by
  simp only [Gen.seqCandidates, seqCandidates, answersOf_std,
    flatMapL_std, composeLive_std, maxima_std, pushes_std, funext (seqPushL_std _ _),
    funext (seqPushR_std _ _)]

theorem candidates_std (P : Program) (ts : Tables) (g : Goal) :
    Gen.candidates P ts g = candidates P ts g := by
  obtain ⟨lb, e, rb⟩ := g
  cases e <;> simp only [Gen.candidates, candidates, seqCandidates_std, produceStrategies_std]

theorem round_std (st : State) : Gen.round st = round st := by
  simp only [Gen.round, round, mapL_std, foldL_std, anyL_std, candidates_std, fresh_std, norm_std,
    same_std, Gen.goalSize_std, orient_std]
  refine bind_congr fun _ => bind_congr fun _ => bind_congr fun ts1 =>
    bind_congr fun _ => bind_congr fun _ => ?_
  cases st.tables.head? <;> cases ts1.head? <;> rfl

theorem step_std (st : State) : Gen.step st = step st := by
  simp only [Gen.step, step, round_std]

/-- The goal-directed engine at the kernel of the language is the
goal-directed machine. -/
theorem engine_costed : Gen.engine.costed = machine := by
  show (⟨State, fun P q => Tabled.Gen.ofGoal P ⟨none, q, none⟩, fun st => Gen.step st⟩ :
    CostedRuntime) = ⟨State, fun P q => ofGoal P ⟨none, q, none⟩, fun st => step st⟩
  simp only [ofGoal_std, step_std]

end Directed

end RwLog
