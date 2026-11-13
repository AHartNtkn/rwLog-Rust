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
  le : sizes st.seenB ≤ sizes st.seen

variable {A B}

theorem sideA_val (st : State A.State B.State) : (sideA A B st).val = .inl (A.step st.a).val := rfl

theorem sideA_ticks (st : State A.State B.State) :
    (sideA A B st).ticks = padA A B st + (A.step st.a).ticks := by
  simp [sideA]

/-- What `B`'s side of the race returns: `B` is done, or its step with the
answers that are plain. -/
def resB (st : State A.State B.State) : Option (List Span × B.State) :=
  match (B.step st.b).val with
  | .done => none
  | .emit bs b' => some (bs.filter fun x => (plain x).val, b')

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

/-- The answers `B`'s side returns are no larger than what `B`'s step cost,
when `B` pays for the answers it emits. -/
theorem resB_sizes (hB : ∀ (s : B.State) (bs : List Span) (s' : B.State),
      (B.step s).val = .emit bs s' → sizes bs ≤ (B.step s).ticks)
    {st : State A.State B.State} {ps : List Span} {b' : B.State}
    (h : resB st = some (ps, b')) : sizes ps ≤ (sideB A B st).ticks := by
  unfold resB at h
  cases hs : (B.step st.b).val with
  | done => rw [hs] at h; cases h
  | emit bs b'' =>
    rw [hs] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    have h1 := hB st.b bs b'' hs
    have h2 : sizes ps ≤ sizes bs := by
      rw [← h.1]; exact sizes_sublist List.filter_sublist
    have h3 := step_le_sideB st
    omega

theorem resB_plain {st : State A.State B.State} {ps : List Span} {b' : B.State}
    (h : resB st = some (ps, b')) : ∀ t ∈ ps, t.c = [] := by
  unfold resB at h
  cases hs : (B.step st.b).val with
  | done => rw [hs] at h; cases h
  | emit bs b'' =>
    rw [hs] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    intro t ht
    rw [← h.1] at ht
    exact plain_sound (List.mem_filter.1 ht).2

/-! ## After the race -/

/-- The answers of `A` that pass the filter. -/
def outA (st : State A.State B.State) (as : List Span) : List Span :=
  as.filter fun x => !st.seenB.any fun t => t.covers? x

/-- The state after a step of `A`. -/
def stA (st : State A.State B.State) (as : List Span) (a' : A.State) : State A.State B.State :=
  { st with a := a', last := true, streak := if st.last then st.streak + 1 else 1,
            seen := st.seen ++ outA st as }

theorem afterA_emit (st : State A.State B.State) (as : List Span) (a' : A.State) :
    (afterA A B st (.emit as a')).val = .emit (outA st as) (stA st as a') ∧
      (afterA A B st (.emit as a')).ticks = (dropCovered st.seenB as).ticks := by
  simp [afterA, outA, stA]

theorem inv_stA {st : State A.State B.State} (h : Inv A B st) (as : List Span) (a' : A.State) :
    Inv A B (stA st as a') :=
  ⟨h.plain, fun t ht => List.mem_append_left _ (h.sub t ht), by
    have e : sizes (stA st as a').seen = sizes st.seen + sizes (outA st as) := sizes_append _ _
    have := h.le
    show sizes st.seenB ≤ sizes (stA st as a').seen
    omega⟩

theorem sizes_stA (st : State A.State B.State) (as : List Span) (a' : A.State) :
    sizes (stA st as a').seen ≤ sizes st.seen + sizes as := by
  have e : sizes (stA st as a').seen = sizes st.seen + sizes (outA st as) := sizes_append _ _
  have : sizes (outA st as) ≤ sizes as := sizes_sublist List.filter_sublist
  omega

/-- What the comparison of `A`'s answers with `B`'s costs. -/
theorem afterA_ticks_le {st : State A.State B.State} (h : Inv A B st) {as : List Span} {o S : Nat}
    (ho : sizes as ≤ o) (hS : sizes st.seen ≤ S) :
    (dropCovered st.seenB as).ticks ≤ 2 * o * S := by
  have h1 := dropCovered_ticks h.plain as
  have h2 := length_le_sizes as
  have h3 := length_le_sizes st.seenB
  have hσ : sizes st.seenB ≤ S := le_trans h.le hS
  have h4 : as.length * sizes st.seenB ≤ o * S := Nat.mul_le_mul (le_trans h2 ho) hσ
  have h5 : st.seenB.length * sizes as ≤ S * o := Nat.mul_le_mul (le_trans h3 hσ) ho
  have h6 : 2 * o * S = o * S + S * o := by ring
  omega

/-- The answers of `B` that are new. -/
def outB (st : State A.State B.State) (ps : List Span) : List Span := RwLog.fresh st.seen ps

/-- The state after a step of `B`. -/
def stB (st : State A.State B.State) (ps : List Span) (b' : B.State) : State A.State B.State :=
  { st with b := b', last := false, streak := if st.last then 1 else st.streak + 1,
            seen := st.seen ++ outB st ps, seenB := st.seenB ++ outB st ps }

theorem afterB_some (st : State A.State B.State) (ps : List Span) (b' : B.State) :
    (afterB A B st (some (ps, b'))).val = .emit (outB st ps) (stB st ps b') ∧
      (afterB A B st (some (ps, b'))).ticks = (Tabled.fresh st.seen ps).ticks := by
  simp [afterB, outB, stB]

theorem afterB_none (st : State A.State B.State) :
    (afterB A B st none).val = .emit [] { st with live := false } ∧
      (afterB A B st none).ticks = 0 := ⟨rfl, rfl⟩

theorem inv_stB {st : State A.State B.State} (h : Inv A B st) {ps : List Span}
    (hp : ∀ t ∈ ps, t.c = []) (b' : B.State) : Inv A B (stB st ps b') :=
  ⟨fun t ht => by
    rcases List.mem_append.1 ht with h' | h'
    · exact h.plain t h'
    · exact hp t ((fresh_sublist _ _).subset h'),
   fun t ht => by
    rcases List.mem_append.1 ht with h' | h'
    · exact List.mem_append_left _ (h.sub t h')
    · exact List.mem_append_right _ h', by
    have e1 : sizes (stB st ps b').seen = sizes st.seen + sizes (outB st ps) := sizes_append _ _
    have e2 : sizes (stB st ps b').seenB = sizes st.seenB + sizes (outB st ps) := sizes_append _ _
    have := h.le
    omega⟩

theorem sizes_stB (st : State A.State B.State) (ps : List Span) (b' : B.State) :
    sizes (stB st ps b').seen ≤ sizes st.seen + sizes ps := by
  have e : sizes (stB st ps b').seen = sizes st.seen + sizes (outB st ps) := sizes_append _ _
  have : sizes (outB st ps) ≤ sizes ps := sizes_sublist (fresh_sublist _ _)
  omega

/-- What entering `B`'s plain answers costs. -/
theorem afterB_ticks_le (st : State A.State B.State) {ps : List Span} (hp : ∀ t ∈ ps, t.c = [])
    {π S : Nat} (hπ : sizes ps ≤ π) (hS : sizes st.seen ≤ S) :
    (Tabled.fresh st.seen ps).ticks ≤ 2 * π * S + 6 * π * π := by
  have h1 := fresh_ticks_plain st.seen hp
  have h2 := length_le_sizes ps
  have h3 := length_le_sizes st.seen
  have h4 : ps.length * sizes st.seen ≤ π * S := Nat.mul_le_mul (le_trans h2 hπ) hS
  have h5 : st.seen.length * sizes ps ≤ S * π := Nat.mul_le_mul (le_trans h3 hS) hπ
  have h6 : 6 * ps.length * sizes ps ≤ 6 * π * π :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 6 (le_trans h2 hπ)) hπ
  have h7 : 2 * π * S = π * S + S * π := by ring
  omega

/-! ## The step -/

/-- A step of the hedge while `B` is running: `A`'s step was taken, at up to
7 times its handicapped cost, or `B`'s was, which then cost less than `A`'s
would have. -/
theorem step_live {st : State A.State B.State} (h : st.live = true) :
    ((step A B st).val = (afterA A B st (A.step st.a).val).val ∧
      (step A B st).ticks ≤ 7 * (padA A B st + (A.step st.a).ticks) +
        (afterA A B st (A.step st.a).val).ticks ∧
      (step A B st).ticks ≤ 7 * (sideB A B st).ticks +
        (afterA A B st (A.step st.a).val).ticks ∧
      padA A B st + (A.step st.a).ticks ≤ 2 * (sideB A B st).ticks) ∨
    ((step A B st).val = (afterB A B st (resB st)).val ∧
      (step A B st).ticks ≤ 7 * (sideB A B st).ticks + (afterB A B st (resB st)).ticks ∧
      (sideB A B st).ticks < padA A B st + (A.step st.a).ticks) := by
  have ht := race_ticks (sideA A B st) (sideB A B st)
  rw [sideA_ticks] at ht
  have m1 := Nat.min_le_left (padA A B st + (A.step st.a).ticks) (sideB A B st).ticks
  have m2 := Nat.min_le_right (padA A B st + (A.step st.a).ticks) (sideB A B st).ticks
  rcases race_cases (sideA A B st) (sideB A B st) with ⟨hv, hc⟩ | ⟨hv, hc⟩
  · left
    rw [sideA_ticks] at hc
    rw [sideA_val] at hv
    simp only [step, h, ite_true, bind_val, bind_ticks, hv]
    refine ⟨trivial, ?_, ?_, hc⟩ <;> omega
  · right
    rw [sideA_ticks] at hc
    rw [sideB_val] at hv
    simp only [step, h, ite_true, bind_val, bind_ticks, hv]
    refine ⟨trivial, ?_, hc⟩
    omega

/-- A step of the hedge once `B` is done is a step of `A`. -/
theorem step_dead {st : State A.State B.State} (h : st.live = false) :
    (step A B st).val = (afterA A B st (A.step st.a).val).val ∧
      (step A B st).ticks = (A.step st.a).ticks + (afterA A B st (A.step st.a).val).ticks := by
  simp [step, h]

end Hedge

end RwLog
