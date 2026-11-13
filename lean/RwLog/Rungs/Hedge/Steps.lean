/-
# One step of the hedge

What a step of `Hedge.machine A B` is and what it spends, by who won the race.
-/
import RwLog.Rungs.Hedge.Filters

namespace RwLog

open Cost

namespace Hedge

variable (A B : CostedRuntime)

/-- What the hedge keeps true of its state: the answers of `B` it emitted
carry no constraints, and are among the answers emitted. -/
structure Inv (st : State A.State B.State) : Prop where
  plain : ∀ t ∈ st.seenB, t.c = []
  sub : ∀ t ∈ st.seenB, t ∈ st.seen

variable {A B}

theorem sideA_val (st : State A.State B.State) : (sideA A B st).val = .inl (A.step st.a).val := rfl

theorem sideA_ticks (st : State A.State B.State) :
    (sideA A B st).ticks = padA A B st + (A.step st.a).ticks := by
  simp [sideA]

/-- What `B`'s side of the race returns: `B` is done, or its step with the
answers that are plain and new. -/
def resB (st : State A.State B.State) : Option (List Span × B.State) :=
  match (B.step st.b).val with
  | .done => none
  | .emit bs b' => some (RwLog.fresh st.seen (bs.filter fun x => (plain x).val), b')

theorem sideB_val (st : State A.State B.State) : (sideB A B st).val = .inr (resB st) := by
  unfold sideB resB
  simp only [bind_val]
  cases (B.step st.b).val with
  | done => rfl
  | emit bs b' => simp

theorem padB_le_sideB (st : State A.State B.State) : padB A B st ≤ (sideB A B st).ticks := by
  simp only [sideB, bind_ticks, tick_ticks]
  omega

theorem step_le_sideB (st : State A.State B.State) :
    padB A B st + (B.step st.b).ticks ≤ (sideB A B st).ticks := by
  simp only [sideB, bind_ticks, tick_ticks]
  omega

/-- The answers `B`'s side returns are paid for by their sizes, inside the
race. -/
theorem resB_sizes {st : State A.State B.State} {out : List Span} {b' : B.State}
    (h : resB st = some (out, b')) : sizes out ≤ (sideB A B st).ticks := by
  unfold resB at h
  unfold sideB
  simp only [bind_ticks, tick_ticks]
  cases hs : (B.step st.b).val with
  | done => rw [hs] at h; cases h
  | emit bs b'' =>
    rw [hs] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    have hf := fresh_sizes_le st.seen (filterL plain bs).val
    simp only [bind_ticks, pure_ticks, Tabled.fresh_val, filterL_val] at hf ⊢
    rw [h.1] at hf
    omega

theorem resB_plain {st : State A.State B.State} {out : List Span} {b' : B.State}
    (h : resB st = some (out, b')) : ∀ t ∈ out, t.c = [] := by
  unfold resB at h
  cases hs : (B.step st.b).val with
  | done => rw [hs] at h; cases h
  | emit bs b'' =>
    rw [hs] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    intro t ht
    rw [← h.1] at ht
    have := (List.mem_filter.1 (fresh_sub ht).1).2
    exact plain_sound this

/-- A step of the hedge while `B` is running: `A`'s step was taken, at up to
7 times its handicapped cost, or `B`'s was, which then cost less than `A`'s
would have. -/
theorem step_live {st : State A.State B.State} (h : st.live = true) :
    ((step A B st).val = (afterA A B st (A.step st.a).val).val ∧
      (step A B st).ticks ≤ 7 * (padA A B st + (A.step st.a).ticks) +
        (afterA A B st (A.step st.a).val).ticks ∧
      padA A B st + (A.step st.a).ticks ≤ 2 * (sideB A B st).ticks) ∨
    ((step A B st).val = afterB A B st (resB st) ∧
      (step A B st).ticks ≤ 7 * (sideB A B st).ticks ∧
      (sideB A B st).ticks < padA A B st + (A.step st.a).ticks) := by
  have ht := race_ticks (sideA A B st) (sideB A B st)
  rw [sideA_ticks] at ht
  rcases race_cases (sideA A B st) (sideB A B st) with ⟨hv, hc⟩ | ⟨hv, hc⟩
  · left
    rw [sideA_ticks] at hc
    rw [sideA_val] at hv
    simp only [step, h, ite_true, bind_val, bind_ticks, hv]
    refine ⟨trivial, ?_, hc⟩
    have := Nat.min_le_left (padA A B st + (A.step st.a).ticks) (sideB A B st).ticks
    omega
  · right
    rw [sideA_ticks] at hc
    rw [sideB_val] at hv
    simp only [step, h, ite_true, bind_val, bind_ticks, hv, pure_val, pure_ticks]
    refine ⟨trivial, ?_, hc⟩
    have := Nat.min_le_right (padA A B st + (A.step st.a).ticks) (sideB A B st).ticks
    omega

/-- A step of the hedge once `B` is done is a step of `A`. -/
theorem step_dead {st : State A.State B.State} (h : st.live = false) :
    (step A B st).val = (afterA A B st (A.step st.a).val).val ∧
      (step A B st).ticks = (A.step st.a).ticks + (afterA A B st (A.step st.a).val).ticks := by
  simp [step, h]

end Hedge

end RwLog
