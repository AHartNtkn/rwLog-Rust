/-
# What two engines side by side keep

The step of the pair (`Beside.step`) read at a kernel that returns what a
domain returns, in the monad of `Cost` (`Beside.stepC`).
-/
import RwLog.Rungs.Framework.Beside
import RwLog.Rungs.Framework.KernelAt
import RwLog.Rungs.Framework.Derivation

namespace RwLog

namespace Beside

variable {A X Y : Type}

/-- `counted` in the monad of `Cost`. -/
def countedC (m : Cost (StepOf A X)) : Cost (StepOf A X) := do
  let r ← m
  Cost.tick (shown r)
  pure r

/-- `step` in the monad of `Cost`. -/
def stepC (f : X → Cost (StepOf A X)) (g : Y → Cost (StepOf A Y)) (s : State X Y) :
    Cost (StepOf A (State X Y)) :=
  match s.snd with
  | some y =>
    if s.paidFst ≤ s.paidSnd then do
      let r ← Cost.metered (Cost.within (budget s.gaveFst) (countedC (f s.fst)))
      match r.1 with
      | none => pure (.emit [] { s with paidFst := s.paidFst + budget s.gaveFst,
                                        gaveFst := budget s.gaveFst })
      | some (.emit as x) => pure (.emit as { s with fst := x, paidFst := s.paidFst + r.2 + 1,
                                                     gaveFst := 0 })
      | some (.progress n x) =>
        pure (.progress n { s with fst := x, paidFst := s.paidFst + r.2 + 1, gaveFst := 0 })
      | some (.done fin) => pure (.done fin)
    else do
      let r ← Cost.metered (Cost.within (budget s.gaveSnd) (countedC (g y)))
      match r.1 with
      | none => pure (.emit [] { s with paidSnd := s.paidSnd + budget s.gaveSnd,
                                        gaveSnd := budget s.gaveSnd })
      | some (.emit as y') =>
        pure (.emit as { s with snd := some y', paidSnd := s.paidSnd + r.2 + 1, gaveSnd := 0 })
      | some (.progress _ y') =>
        pure (.emit [] { s with snd := some y', paidSnd := s.paidSnd + r.2 + 1, gaveSnd := 0 })
      | some (.done fin) =>
        pure (.emit fin { s with snd := none, paidSnd := s.paidSnd + r.2 + 1, gaveSnd := 0 })
  | none => do
    let r ← f s.fst
    match r with
    | .emit as x => pure (.emit as { s with fst := x })
    | .progress n x => pure (.progress n { s with fst := x })
    | .done fin => pure (.done fin)

/-- At a kernel that returns what a domain returns, the step of the pair is
`stepC`. -/
theorem step_eq {R : Type} [Answer R] [DecidableEq R] (D : Domain R) (K : Kernel R Cost)
    (hK : K.Refines D) (P : Program) (f : X → Cost (StepOf (Ans D P) X))
    (g : Y → Cost (StepOf (Ans D P) Y)) (s : State X Y) :
    @step R Rel (Ans D P) Cost (DerivationKernel.over D K hK P) X Y f g s = stepC f g s := by
  at_cost K hK
  rfl

/-- At a kernel that returns what a domain returns, the first state of the
pair is the first state of each engine, built one after the other. -/
theorem init_eq {R : Type} [Answer R] [DecidableEq R] (D : Domain R) (K : Kernel R Cost)
    (hK : K.Refines D) (P : Program) (i : Cost X) (j : Cost Y) :
    @init R Rel (Ans D P) Cost (DerivationKernel.over D K hK P) X Y i j =
      (i >>= fun x => j >>= fun y => pure ⟨x, some y, 0, 0, 0, 0⟩) := by
  at_cost K hK
  rfl

/-! ## Runs of a step function -/

/-- The state a step goes on from, if it goes on. -/
def next : StepOf A X → Option X
  | .emit _ x => some x
  | .progress _ x => some x
  | .done _ => none

/-- The answers a step emits and goes on. -/
def outs : StepOf A X → List A
  | .emit as _ => as
  | .progress _ _ => []
  | .done _ => []

section Runs

variable (f : X → Cost (StepOf A X))

/-- The state after `n` steps; nothing if a step reported that it is done. -/
def after : X → Nat → Option X
  | x, 0 => some x
  | x, n + 1 =>
    match next (f x).val with
    | some x' => after x' n
    | none => none

/-- The answers emitted in `n` steps. -/
def emits : X → Nat → List A
  | _, 0 => []
  | x, n + 1 =>
    outs (f x).val ++ match next (f x).val with
      | some x' => emits x' n
      | none => []

/-- What `n` steps cost, with one tick more for each answer shown. -/
def cost : X → Nat → Nat
  | _, 0 => 0
  | x, n + 1 =>
    (f x).ticks + shown (f x).val + match next (f x).val with
      | some x' => cost x' n
      | none => 0

theorem after_succ_some {x x' : X} (h : next (f x).val = some x') (n : Nat) :
    after f x (n + 1) = after f x' n := by simp only [after, h]

theorem after_succ_none {x : X} (h : next (f x).val = none) (n : Nat) :
    after f x (n + 1) = none := by simp only [after, h]

theorem emits_succ_some {x x' : X} (h : next (f x).val = some x') (n : Nat) :
    emits f x (n + 1) = outs (f x).val ++ emits f x' n := by simp only [emits, h]

theorem cost_succ_some {x x' : X} (h : next (f x).val = some x') (n : Nat) :
    cost f x (n + 1) = (f x).ticks + shown (f x).val + cost f x' n := by simp only [cost, h]

theorem cost_succ_none {x : X} (h : next (f x).val = none) (n : Nat) :
    cost f x (n + 1) = (f x).ticks + shown (f x).val := by simp only [cost, h, Nat.add_zero]

/-- A run that reaches a state goes on from it. -/
theorem after_add : ∀ (m : Nat) (x x' : X), after f x m = some x' →
    ∀ n, after f x (m + n) = after f x' n
  | 0, x, x', h, n => by
    simp only [after, Option.some.injEq] at h
    rw [h, Nat.zero_add]
  | m + 1, x, x', h, n => by
    rw [Nat.add_right_comm]
    cases hn : next (f x).val with
    | none => rw [after_succ_none f hn] at h; cases h
    | some x1 =>
      rw [after_succ_some f hn] at h ⊢
      exact after_add m x1 x' h n

theorem emits_add : ∀ (m : Nat) (x x' : X), after f x m = some x' →
    ∀ n, emits f x (m + n) = emits f x m ++ emits f x' n
  | 0, x, x', h, n => by
    simp only [after, Option.some.injEq] at h
    rw [h, Nat.zero_add]; rfl
  | m + 1, x, x', h, n => by
    rw [Nat.add_right_comm]
    cases hn : next (f x).val with
    | none => rw [after_succ_none f hn] at h; cases h
    | some x1 =>
      rw [after_succ_some f hn] at h
      rw [emits_succ_some f hn, emits_succ_some f hn, emits_add m x1 x' h n, List.append_assoc]

theorem cost_add : ∀ (m : Nat) (x x' : X), after f x m = some x' →
    ∀ n, cost f x (m + n) = cost f x m + cost f x' n
  | 0, x, x', h, n => by
    simp only [after, Option.some.injEq] at h
    rw [h, Nat.zero_add]; simp [cost]
  | m + 1, x, x', h, n => by
    rw [Nat.add_right_comm]
    cases hn : next (f x).val with
    | none => rw [after_succ_none f hn] at h; cases h
    | some x1 =>
      rw [after_succ_some f hn] at h
      rw [cost_succ_some f hn, cost_succ_some f hn, cost_add m x1 x' h n]
      omega

end Runs

/-! ## The step of the pair, case by case -/

section Cases

variable (f : X → Cost (StepOf A X)) (g : Y → Cost (StepOf A Y))

/-- What a step costs under a budget: its ticks and one for each answer it
shows. -/
def price (x : X) : Nat := (f x).ticks + shown (f x).val

@[simp] theorem countedC_val (m : Cost (StepOf A X)) : (countedC m).val = m.val := rfl

@[simp] theorem countedC_ticks (m : Cost (StepOf A X)) :
    (countedC m).ticks = m.ticks + shown m.val := by
  simp [countedC]

theorem tried_fail {x : X} {b : Nat} (hb : b < price f x) :
    (Cost.metered (Cost.within b (countedC (f x)))).val = (none, b) ∧
      (Cost.metered (Cost.within b (countedC (f x)))).ticks = b := by
  have hw : ¬ (f x).ticks + shown (f x).val ≤ b := Nat.not_le.2 hb
  simp only [Cost.metered_val, Cost.metered_ticks, Cost.within, countedC_ticks, hw, ↓reduceIte,
    and_self]

theorem tried_fit {x : X} {b : Nat} (hb : price f x ≤ b) :
    (Cost.metered (Cost.within b (countedC (f x)))).val = (some (f x).val, price f x) ∧
      (Cost.metered (Cost.within b (countedC (f x)))).ticks = price f x := by
  have hw : (f x).ticks + shown (f x).val ≤ b := hb
  simp only [Cost.metered_val, Cost.metered_ticks, Cost.within, countedC_ticks, hw, ↓reduceIte,
    countedC_val, price, and_self]

/-- The first engine's turn, and its step does not fit the budget. -/
theorem fst_fail {s : State X Y} {y : Y} (hy : s.snd = some y) (ht : s.paidFst ≤ s.paidSnd)
    (hb : budget s.gaveFst < price f s.fst) :
    (stepC f g s).val = .emit [] { s with paidFst := s.paidFst + budget s.gaveFst,
                                          gaveFst := budget s.gaveFst } ∧
      (stepC f g s).ticks = budget s.gaveFst := by
  obtain ⟨h1, h2⟩ := tried_fail f hb
  simp only [stepC, hy, ht, ↓reduceIte, Cost.bind_val, Cost.bind_ticks, h1, h2, Cost.pure_val,
    Cost.pure_ticks, Nat.add_zero, and_self]

/-- The first engine's turn, and its step fits the budget. -/
theorem fst_fit {s : State X Y} {y : Y} (hy : s.snd = some y) (ht : s.paidFst ≤ s.paidSnd)
    (hb : price f s.fst ≤ budget s.gaveFst) :
    (stepC f g s).val =
        (match (f s.fst).val with
          | .emit as x => .emit as { s with fst := x, paidFst := s.paidFst + price f s.fst + 1,
                                            gaveFst := 0 }
          | .progress n x =>
            .progress n { s with fst := x, paidFst := s.paidFst + price f s.fst + 1, gaveFst := 0 }
          | .done fin => .done fin) ∧
      (stepC f g s).ticks = price f s.fst := by
  obtain ⟨h1, h2⟩ := tried_fit f hb
  simp only [stepC, hy, ht, ↓reduceIte, Cost.bind_val, Cost.bind_ticks, h1, h2]
  cases (f s.fst).val <;> simp

/-- The second engine's turn, and its step does not fit the budget. -/
theorem snd_fail {s : State X Y} {y : Y} (hy : s.snd = some y) (ht : ¬ s.paidFst ≤ s.paidSnd)
    (hb : budget s.gaveSnd < price g y) :
    (stepC f g s).val = .emit [] { s with paidSnd := s.paidSnd + budget s.gaveSnd,
                                          gaveSnd := budget s.gaveSnd } ∧
      (stepC f g s).ticks = budget s.gaveSnd := by
  obtain ⟨h1, h2⟩ := tried_fail g hb
  simp only [stepC, hy, ht, ↓reduceIte, Cost.bind_val, Cost.bind_ticks, h1, h2, Cost.pure_val,
    Cost.pure_ticks, Nat.add_zero, and_self]

/-- The second engine's turn, and its step fits the budget. -/
theorem snd_fit {s : State X Y} {y : Y} (hy : s.snd = some y) (ht : ¬ s.paidFst ≤ s.paidSnd)
    (hb : price g y ≤ budget s.gaveSnd) :
    (stepC f g s).val =
        .emit (match (g y).val with
          | .emit as _ => as
          | .progress _ _ => []
          | .done fin => fin)
          { s with snd := next (g y).val, paidSnd := s.paidSnd + price g y + 1, gaveSnd := 0 } ∧
      (stepC f g s).ticks = price g y := by
  obtain ⟨h1, h2⟩ := tried_fit g hb
  simp only [stepC, hy, ht, ↓reduceIte, Cost.bind_val, Cost.bind_ticks, h1, h2]
  cases (g y).val <;> simp [next]

/-- The second engine is done: the step of the pair is the first engine's. -/
theorem alone {s : State X Y} (hy : s.snd = none) :
    (stepC f g s).val =
        (match (f s.fst).val with
          | .emit as x => .emit as { s with fst := x }
          | .progress n x => .progress n { s with fst := x }
          | .done fin => .done fin) ∧
      (stepC f g s).ticks = (f s.fst).ticks := by
  simp only [stepC, hy, Cost.bind_val, Cost.bind_ticks]
  cases (f s.fst).val <;> simp

end Cases

/-! ## Every step of the first engine is taken -/

section First

variable (f : X → Cost (StepOf A X)) (g : Y → Cost (StepOf A Y))

theorem budget_pos (n : Nat) : 1 ≤ budget n := le_max_left _ _

theorem budget_le (n : Nat) : budget n ≤ 2 * n + 1 := by unfold budget; omega

theorem budget_budget (n : Nat) : budget (budget n) = 2 * budget n := by unfold budget; omega

/-- Within `m` steps the pair has taken the next step of its first engine:
it has emitted what that step emits and holds the state after it, or, if
that step reports that the engine is done, the pair has reported that it is
done. -/
def Took (s : State X Y) (m : Nat) : Prop :=
  match next (f s.fst).val with
  | some x' => ∃ s', after (stepC f g) s m = some s' ∧ s'.fst = x' ∧
      ∀ a ∈ outs (f s.fst).val, a ∈ emits (stepC f g) s m
  | none => after (stepC f g) s m = none

/-- A step of the pair that leaves the first engine where it was puts off
the first engine's next step by one. -/
theorem Took.later {s s1 : State X Y} {m : Nat} (h1 : next (stepC f g s).val = some s1)
    (hf : s1.fst = s.fst) (h : Took f g s1 m) : Took f g s (m + 1) := by
  unfold Took at h ⊢
  rw [hf] at h
  cases hn : next (f s.fst).val with
  | none =>
    rw [hn] at h
    simp only [after_succ_some _ h1, h]
  | some x' =>
    rw [hn] at h
    obtain ⟨s', h2, h3, h4⟩ := h
    refine ⟨s', by rw [after_succ_some _ h1, h2], h3, fun a ha => ?_⟩
    rw [emits_succ_some _ h1]
    exact List.mem_append_right _ (h4 a ha)

/-- A step of the pair that is the first engine's next step. -/
theorem Took.now {s : State X Y}
    (h : (∀ fin, (f s.fst).val = .done fin → next (stepC f g s).val = none) ∧
      (∀ as x, (f s.fst).val = .emit as x → ∃ s', (stepC f g s).val = .emit as s' ∧ s'.fst = x) ∧
      ∀ n x, (f s.fst).val = .progress n x →
        ∃ s', (stepC f g s).val = .progress n s' ∧ s'.fst = x) : Took f g s 1 := by
  unfold Took
  cases hv : (f s.fst).val with
  | done fin =>
    simp only [next]
    exact after_succ_none _ (h.1 fin hv) 0
  | emit as x =>
    obtain ⟨s', h1, h2⟩ := h.2.1 as x hv
    have hn : next (stepC f g s).val = some s' := by rw [h1]; rfl
    simp only [next]
    refine ⟨s', by rw [after_succ_some _ hn]; rfl, h2, fun a ha => ?_⟩
    rw [emits_succ_some _ hn, h1]
    exact List.mem_append_left _ ha
  | progress n x =>
    obtain ⟨s', h1, h2⟩ := h.2.2 n x hv
    have hn : next (stepC f g s).val = some s' := by rw [h1]; rfl
    simp only [next]
    exact ⟨s', by rw [after_succ_some _ hn]; rfl, h2, fun a ha => by simp [outs] at ha⟩

/-- **The pair takes the next step of its first engine**, whatever the
second engine does and whatever either costs. -/
theorem took (s : State X Y) : ∃ m, Took f g s m := by
  generalize hk : price f s.fst - budget s.gaveFst = k
  induction k using Nat.strong_induction_on generalizing s with
  | _ k ihk =>
    generalize hj : s.paidFst - s.paidSnd = j
    induction j using Nat.strong_induction_on generalizing s with
    | _ j ihj =>
      cases hy : s.snd with
      | none =>
        refine ⟨1, Took.now f g ?_⟩
        obtain ⟨hv, -⟩ := alone f g hy
        rw [hv]
        refine ⟨fun fin h => by rw [h]; rfl, fun as x h => ?_, fun n x h => ?_⟩
        · rw [h]; exact ⟨_, rfl, rfl⟩
        · rw [h]; exact ⟨_, rfl, rfl⟩
      | some y =>
        by_cases ht : s.paidFst ≤ s.paidSnd
        · by_cases hb : price f s.fst ≤ budget s.gaveFst
          · refine ⟨1, Took.now f g ?_⟩
            obtain ⟨hv, -⟩ := fst_fit f g hy ht hb
            rw [hv]
            refine ⟨fun fin h => by rw [h]; rfl, fun as x h => ?_, fun n x h => ?_⟩
            · rw [h]; exact ⟨_, rfl, rfl⟩
            · rw [h]; exact ⟨_, rfl, rfl⟩
          · obtain ⟨hv, -⟩ := fst_fail f g hy ht (Nat.lt_of_not_le hb)
            have hn : next (stepC f g s).val = some
                { s with paidFst := s.paidFst + budget s.gaveFst, gaveFst := budget s.gaveFst } := by
              rw [hv]; rfl
            obtain ⟨m, hm⟩ := ihk (price f s.fst - budget (budget s.gaveFst))
              (by rw [← hk, budget_budget]; have := budget_pos s.gaveFst; omega)
              { s with paidFst := s.paidFst + budget s.gaveFst, gaveFst := budget s.gaveFst } rfl
            exact ⟨m + 1, Took.later f g hn rfl hm⟩
        · by_cases hb : price g y ≤ budget s.gaveSnd
          · obtain ⟨hv, -⟩ := snd_fit f g hy ht hb
            have hn : next (stepC f g s).val = some
                { s with snd := next (g y).val, paidSnd := s.paidSnd + price g y + 1,
                         gaveSnd := 0 } := by
              rw [hv]; rfl
            obtain ⟨m, hm⟩ := ihj (s.paidFst - (s.paidSnd + price g y + 1)) (by omega)
              { s with snd := next (g y).val, paidSnd := s.paidSnd + price g y + 1, gaveSnd := 0 }
              hk rfl
            exact ⟨m + 1, Took.later f g hn rfl hm⟩
          · obtain ⟨hv, -⟩ := snd_fail f g hy ht (Nat.lt_of_not_le hb)
            have hn : next (stepC f g s).val = some
                { s with paidSnd := s.paidSnd + budget s.gaveSnd, gaveSnd := budget s.gaveSnd } := by
              rw [hv]; rfl
            obtain ⟨m, hm⟩ := ihj (s.paidFst - (s.paidSnd + budget s.gaveSnd))
              (by have := budget_pos s.gaveSnd; omega)
              { s with paidSnd := s.paidSnd + budget s.gaveSnd, gaveSnd := budget s.gaveSnd } hk rfl
            exact ⟨m + 1, Took.later f g hn rfl hm⟩

theorem outs_of_next_none {r : StepOf A X} (h : next r = none) : outs r = [] := by
  cases r <;> simp_all [next, outs]

/-- **The pair emits everything its first engine emits, and reports that it
is done if that engine does.** -/
theorem fst_run : ∀ (n : Nat) (s : State X Y), ∃ m,
    (∀ a ∈ emits f s.fst n, a ∈ emits (stepC f g) s m) ∧
      (after f s.fst n = none → after (stepC f g) s m = none)
  | 0, s => ⟨0, fun a ha => by simp [emits] at ha, fun h => by simp [after] at h⟩
  | n + 1, s => by
    obtain ⟨m0, h0⟩ := took f g s
    unfold Took at h0
    cases hn : next (f s.fst).val with
    | none =>
      rw [hn] at h0
      refine ⟨m0, fun a ha => ?_, fun _ => h0⟩
      simp [emits, hn, outs_of_next_none hn] at ha
    | some x' =>
      rw [hn] at h0
      obtain ⟨s', h1, h2, h3⟩ := h0
      obtain ⟨m1, h4, h5⟩ := fst_run n s'
      refine ⟨m0 + m1, fun a ha => ?_, fun h => ?_⟩
      · rw [emits_add _ m0 s s' h1]
        rw [emits_succ_some f hn] at ha
        rcases List.mem_append.1 ha with ha | ha
        · exact List.mem_append_left _ (h3 a ha)
        · exact List.mem_append_right _ (h4 a (h2 ▸ ha))
      · rw [after_add _ m0 s s' h1]
        rw [after_succ_some f hn] at h
        exact h5 (h2 ▸ h)

end First

/-! ## The pair is done only when its first engine is -/

section Halting

variable (f : X → Cost (StepOf A X)) (g : Y → Cost (StepOf A Y))

/-- A step of the pair reports that it is done only if the first engine's
step does. -/
theorem done_of_done {s : State X Y} (h : next (stepC f g s).val = none) :
    next (f s.fst).val = none := by
  cases hy : s.snd with
  | none =>
    rw [(alone f g hy).1] at h
    cases hv : (f s.fst).val <;> simp_all [next]
  | some y =>
    by_cases ht : s.paidFst ≤ s.paidSnd
    · by_cases hb : price f s.fst ≤ budget s.gaveFst
      · rw [(fst_fit f g hy ht hb).1] at h
        cases hv : (f s.fst).val <;> simp_all [next]
      · rw [(fst_fail f g hy ht (Nat.lt_of_not_le hb)).1] at h
        simp [next] at h
    · by_cases hb : price g y ≤ budget s.gaveSnd
      · rw [(snd_fit f g hy ht hb).1] at h
        simp [next] at h
      · rw [(snd_fail f g hy ht (Nat.lt_of_not_le hb)).1] at h
        simp [next] at h

/-- A step of the pair leaves the first engine where it was, or is that
engine's step and emits what it emits. -/
theorem fst_of_step {s s1 : State X Y} (h : next (stepC f g s).val = some s1) :
    s1.fst = s.fst ∨ (next (f s.fst).val = some s1.fst ∧
      ∀ a ∈ outs (f s.fst).val, a ∈ outs (stepC f g s).val) := by
  cases hy : s.snd with
  | none =>
    rw [(alone f g hy).1] at h ⊢
    cases hr : (f s.fst).val with
    | emit as x =>
      rw [hr] at h
      simp only [next, Option.some.injEq] at h
      subst h
      exact .inr ⟨rfl, fun a ha => ha⟩
    | progress n x =>
      rw [hr] at h
      simp only [next, Option.some.injEq] at h
      subst h
      exact .inr ⟨rfl, fun a ha => ha⟩
    | done fin => rw [hr] at h; simp [next] at h
  | some y =>
    by_cases ht : s.paidFst ≤ s.paidSnd
    · by_cases hb : price f s.fst ≤ budget s.gaveFst
      · rw [(fst_fit f g hy ht hb).1] at h ⊢
        cases hr : (f s.fst).val with
        | emit as x =>
          rw [hr] at h
          simp only [next, Option.some.injEq] at h
          subst h
          exact .inr ⟨rfl, fun a ha => ha⟩
        | progress n x =>
          rw [hr] at h
          simp only [next, Option.some.injEq] at h
          subst h
          exact .inr ⟨rfl, fun a ha => ha⟩
        | done fin => rw [hr] at h; simp [next] at h
      · rw [(fst_fail f g hy ht (Nat.lt_of_not_le hb)).1] at h
        simp only [next, Option.some.injEq] at h
        subst h; exact .inl rfl
    · by_cases hb : price g y ≤ budget s.gaveSnd
      · rw [(snd_fit f g hy ht hb).1] at h
        simp only [next, Option.some.injEq] at h
        subst h; exact .inl rfl
      · rw [(snd_fail f g hy ht (Nat.lt_of_not_le hb)).1] at h
        simp only [next, Option.some.injEq] at h
        subst h; exact .inl rfl

/-- **The pair reports that it is done only when its first engine does**,
and by then it has emitted everything that engine emitted. -/
theorem halt_fst : ∀ (m : Nat) (s : State X Y), after (stepC f g) s m = none →
    ∃ n, after f s.fst n = none ∧ ∀ a ∈ emits f s.fst n, a ∈ emits (stepC f g) s m
  | 0, s, h => by simp [after] at h
  | m + 1, s, h => by
    cases hn : next (stepC f g s).val with
    | none =>
      have hd := done_of_done f g hn
      refine ⟨1, after_succ_none f hd 0, fun a ha => ?_⟩
      simp [emits, hd, outs_of_next_none hd] at ha
    | some s1 =>
      rw [after_succ_some _ hn] at h
      obtain ⟨n, hn1, hn2⟩ := halt_fst m s1 h
      rcases fst_of_step f g hn with e | ⟨e, he⟩
      · rw [e] at hn1 hn2
        refine ⟨n, hn1, fun a ha => ?_⟩
        rw [emits_succ_some _ hn]
        exact List.mem_append_right _ (hn2 a ha)
      · refine ⟨n + 1, by rw [after_succ_some f e]; exact hn1, fun a ha => ?_⟩
        rw [emits_succ_some f e] at ha
        rw [emits_succ_some _ hn]
        rcases List.mem_append.1 ha with ha | ha
        · exact List.mem_append_left _ (he a ha)
        · exact List.mem_append_right _ (hn2 a ha)

end Halting

/-! ## What the pair has spent when its second engine has taken a step -/

section Second

variable (f : X → Cost (StepOf A X)) (g : Y → Cost (StepOf A Y))

/-- The accounts are in step: the first engine last gave up at no more than
it has been charged, and has been charged at most three times what the
second has, and two ticks. -/
def Inv (s : State X Y) : Prop := s.gaveFst ≤ s.paidFst ∧ s.paidFst ≤ 3 * s.paidSnd + 2

/-- Twice what the two engines have been charged. -/
def pot (s : State X Y) : Nat := 2 * (s.paidFst + s.paidSnd)

theorem shown_le_price (x : X) : shown (f x).val ≤ price f x := Nat.le_add_left _ _

/-- A step of the pair with the second engine at work: it is paid for out of
what the accounts rise by, and the accounts stay in step. A step that
reports the pair done costs at most four times what the first engine has
been charged, and four ticks. -/
theorem step_pot {s : State X Y} {y : Y} (hy : s.snd = some y) (hI : Inv s) :
    (∀ s', next (stepC f g s).val = some s' →
        Inv s' ∧ s.paidSnd ≤ s'.paidSnd ∧ price (stepC f g) s + pot s ≤ pot s') ∧
      (next (stepC f g s).val = none → price (stepC f g) s ≤ 4 * s.paidFst + 4) := by
  obtain ⟨hI1, hI2⟩ := hI
  have hbl := budget_le s.gaveFst
  by_cases ht : s.paidFst ≤ s.paidSnd
  · by_cases hb : price f s.fst ≤ budget s.gaveFst
    · obtain ⟨hv, hk⟩ := fst_fit f g hy ht hb
      have hp : price f s.fst = (f s.fst).ticks + shown (f s.fst).val := rfl
      have hq : price (stepC f g) s = (stepC f g s).ticks + shown (stepC f g s).val := rfl
      rw [hq, hk, hv]
      cases hr : (f s.fst).val with
      | emit as x =>
        have hsh : shown (f s.fst).val = as.length := by rw [hr]; rfl
        refine ⟨fun s' h => ?_, fun h => by simp [next] at h⟩
        simp only [next, Option.some.injEq] at h
        subst h
        simp only [Inv, pot, shown]
        refine ⟨⟨Nat.zero_le _, ?_⟩, le_rfl, ?_⟩ <;> omega
      | progress n x =>
        have hsh : shown (f s.fst).val = 0 := by rw [hr]; rfl
        refine ⟨fun s' h => ?_, fun h => by simp [next] at h⟩
        simp only [next, Option.some.injEq] at h
        subst h
        simp only [Inv, pot, shown]
        refine ⟨⟨Nat.zero_le _, ?_⟩, le_rfl, ?_⟩ <;> omega
      | done fin =>
        have hsh : shown (f s.fst).val = fin.length := by rw [hr]; rfl
        refine ⟨fun s' h => by simp [next] at h, fun _ => ?_⟩
        simp only [shown]
        omega
    · obtain ⟨hv, hk⟩ := fst_fail f g hy ht (Nat.lt_of_not_le hb)
      unfold price
      rw [hk, hv]
      refine ⟨fun s' h => ?_, fun h => by simp [next] at h⟩
      simp only [next, Option.some.injEq] at h
      subst h
      simp only [Inv, pot, shown, List.length_nil]
      refine ⟨⟨?_, ?_⟩, le_rfl, ?_⟩ <;> omega
  · by_cases hb : price g y ≤ budget s.gaveSnd
    · obtain ⟨hv, hk⟩ := snd_fit f g hy ht hb
      have hs := shown_le_price g y
      unfold price
      rw [hk, hv]
      refine ⟨fun s' h => ?_, fun h => by simp [next] at h⟩
      simp only [next, Option.some.injEq] at h
      subst h
      have hl : (match (g y).val with
          | .emit as _ => as
          | .progress _ _ => []
          | .done fin => fin : List A).length ≤ shown (g y).val := by
        cases (g y).val <;> simp [shown]
      simp only [Inv, pot, shown]
      refine ⟨⟨hI1, ?_⟩, ?_, ?_⟩ <;> omega
    · obtain ⟨hv, hk⟩ := snd_fail f g hy ht (Nat.lt_of_not_le hb)
      unfold price
      rw [hk, hv]
      refine ⟨fun s' h => ?_, fun h => by simp [next] at h⟩
      simp only [next, Option.some.injEq] at h
      subst h
      simp only [Inv, pot, shown, List.length_nil]
      refine ⟨⟨hI1, ?_⟩, ?_, ?_⟩ <;> omega

/-- The first engine's turn: its step, fitted or given up, leaves the second
engine and its account as they were and raises what the first is charged. -/
theorem fst_turn {s s1 : State X Y} {y : Y} (hy : s.snd = some y) (ht : s.paidFst ≤ s.paidSnd)
    (h : next (stepC f g s).val = some s1) :
    s1.snd = s.snd ∧ s1.paidSnd = s.paidSnd ∧ s1.gaveSnd = s.gaveSnd ∧ s.paidFst < s1.paidFst := by
  by_cases hb : price f s.fst ≤ budget s.gaveFst
  · rw [(fst_fit f g hy ht hb).1] at h
    cases hv : (f s.fst).val with
    | emit as x =>
      rw [hv] at h
      simp only [next, Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl, rfl, by simp only; omega⟩
    | progress n x =>
      rw [hv] at h
      simp only [next, Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl, rfl, by simp only; omega⟩
    | done fin =>
      rw [hv] at h
      simp [next] at h
  · rw [(fst_fail f g hy ht (Nat.lt_of_not_le hb)).1] at h
    simp only [next, Option.some.injEq] at h
    subst h
    have := budget_pos s.gaveFst
    exact ⟨rfl, rfl, rfl, by simp only; omega⟩

/-- Within `m` steps the pair has taken the next step `g y` of its second
engine, or has reported that it is done. In the first case it holds the
state after that step, has emitted what the step emits, and what it has
spent is paid for out of what the accounts rose by; the second engine has
been charged at most three times what the step costs, and a tick. In the
second case what the pair has spent is at most a fixed multiple of what the
second engine was charged and what the step costs. -/
def Got (s : State X Y) (y : Y) (m : Nat) : Prop :=
  (after (stepC f g) s m = none ∧
      cost (stepC f g) s m + pot s ≤
        20 * (s.paidSnd + (2 * price g y - budget s.gaveSnd)) + 16) ∨
    ∃ s', after (stepC f g) s m = some s' ∧ s'.snd = next (g y).val ∧ Inv s' ∧
      s'.paidSnd ≤ s.paidSnd + price g y + 1 + (2 * price g y - budget s.gaveSnd) ∧
      cost (stepC f g) s m + pot s ≤ pot s' ∧
      ∀ a ∈ outs (g y).val, a ∈ emits (stepC f g) s m

/-- A step of the pair that is not the second engine's next step puts that
step off by one. -/
theorem Got.later {s s1 : State X Y} {y : Y} {m : Nat} (h1 : next (stepC f g s).val = some s1)
    (hp : price (stepC f g) s + pot s ≤ pot s1)
    (hb : s1.paidSnd + (2 * price g y - budget s1.gaveSnd) ≤
      s.paidSnd + (2 * price g y - budget s.gaveSnd))
    (h : Got f g s1 y m) : Got f g s y (m + 1) := by
  have hq : price (stepC f g) s = (stepC f g s).ticks + shown (stepC f g s).val := rfl
  rcases h with ⟨h2, h3⟩ | ⟨s', h2, h3, h4, h5, h6, h7⟩
  · refine .inl ⟨by rw [after_succ_some _ h1]; exact h2, ?_⟩
    rw [cost_succ_some _ h1]
    omega
  · refine .inr ⟨s', by rw [after_succ_some _ h1]; exact h2, h3, h4, by omega, ?_, fun a ha => ?_⟩
    · rw [cost_succ_some _ h1]
      omega
    · rw [emits_succ_some _ h1]
      exact List.mem_append_right _ (h7 a ha)

/-- **The pair takes the next step of its second engine or reports that it
is done**, and has spent a fixed multiple of what that engine has been
charged. -/
theorem snd_next (y : Y) (s : State X Y) (hy : s.snd = some y) (hI : Inv s) :
    ∃ m, Got f g s y m := by
  generalize hk : price g y - budget s.gaveSnd = k
  induction k using Nat.strong_induction_on generalizing s with
  | _ k ihk =>
    generalize hj : s.paidSnd + 1 - s.paidFst = j
    induction j using Nat.strong_induction_on generalizing s with
    | _ j ihj =>
      obtain ⟨hstep, hdone⟩ := step_pot f g hy hI
      have hq : price (stepC f g) s = (stepC f g s).ticks + shown (stepC f g s).val := rfl
      by_cases ht : s.paidFst ≤ s.paidSnd
      · cases hn : next (stepC f g s).val with
        | none =>
          refine ⟨1, .inl ⟨after_succ_none _ hn 0, ?_⟩⟩
          have h1 := hdone hn
          have h2 := hI.2
          rw [cost_succ_none _ hn]
          simp only [pot]
          omega
        | some s1 =>
          obtain ⟨hI1, -, hp⟩ := hstep s1 hn
          obtain ⟨e1, e2, e3, e4⟩ := fst_turn f g hy ht hn
          obtain ⟨m, hm⟩ := ihj (s1.paidSnd + 1 - s1.paidFst) (by omega) s1 (e1.trans hy) hI1
            (by rw [e3]; exact hk) rfl
          exact ⟨m + 1, Got.later f g hn hp (by rw [e2, e3]) hm⟩
      · by_cases hb : price g y ≤ budget s.gaveSnd
        · obtain ⟨hv, -⟩ := snd_fit f g hy ht hb
          have hn : next (stepC f g s).val = some
              { s with snd := next (g y).val, paidSnd := s.paidSnd + price g y + 1,
                       gaveSnd := 0 } := by
            rw [hv]; rfl
          obtain ⟨hI1, -, hp⟩ := hstep _ hn
          refine ⟨1, .inr ⟨_, by rw [after_succ_some _ hn]; rfl, rfl, hI1, by simp only; omega,
            ?_, fun a ha => ?_⟩⟩
          · rw [cost_succ_some _ hn]
            simp only [cost, Nat.add_zero]
            omega
          · rw [emits_succ_some _ hn, hv]
            refine List.mem_append_left _ ?_
            cases hr : (g y).val <;> simp_all [outs]
        · have hb' := Nat.lt_of_not_le hb
          obtain ⟨hv, -⟩ := snd_fail f g hy ht hb'
          have hn : next (stepC f g s).val = some
              { s with paidSnd := s.paidSnd + budget s.gaveSnd, gaveSnd := budget s.gaveSnd } := by
            rw [hv]; rfl
          obtain ⟨hI1, -, hp⟩ := hstep _ hn
          have hpos := budget_pos s.gaveSnd
          obtain ⟨m, hm⟩ := ihk (price g y - budget (budget s.gaveSnd))
            (by rw [← hk, budget_budget]; omega)
            { s with paidSnd := s.paidSnd + budget s.gaveSnd, gaveSnd := budget s.gaveSnd }
            hy hI1 rfl
          refine ⟨m + 1, Got.later f g hn hp ?_ hm⟩
          simp only [budget_budget]
          omega

/-- **What the pair has spent when its second engine has taken `n` steps.**
From a state with the accounts in step, the pair comes within some number of
steps to have emitted everything the second engine emits in its first `n`
steps, or to have reported that it is done; and by then it has spent at most
twenty times what it had charged the second engine and three times what
those `n` steps cost, and a fixed number of ticks for each. What the first
engine costs is not in the bound. -/
theorem snd_run : ∀ (n : Nat) (s : State X Y) (y : Y), s.snd = some y → Inv s →
    ∃ m, cost (stepC f g) s m + pot s ≤ 20 * (s.paidSnd + 3 * cost g y n + n) + 16 ∧
      (after (stepC f g) s m = none ∨ ∀ a ∈ emits g y n, a ∈ emits (stepC f g) s m)
  | 0, s, y, _, hI => by
    refine ⟨0, ?_, .inr fun a ha => by simp [emits] at ha⟩
    have := hI.2
    simp only [cost, pot]
    omega
  | n + 1, s, y, hy, hI => by
    obtain ⟨m0, h0⟩ := snd_next f g y s hy hI
    have hc : price g y = (g y).ticks + shown (g y).val := rfl
    rcases h0 with ⟨h1, h2⟩ | ⟨s', h1, h2, h3, h4, h5, h6⟩
    · refine ⟨m0, ?_, .inl h1⟩
      cases hn : next (g y).val with
      | none => rw [cost_succ_none g hn]; omega
      | some y' => rw [cost_succ_some g hn]; omega
    · cases hn : next (g y).val with
      | none =>
        refine ⟨m0, ?_, .inr fun a ha => ?_⟩
        · have := h3.2
          rw [cost_succ_none g hn]
          simp only [pot] at h5 ⊢
          omega
        · simp only [emits, hn, List.append_nil] at ha
          exact h6 a ha
      | some y' =>
        obtain ⟨m1, h7, h8⟩ := snd_run n s' y' (h2.trans hn) h3
        refine ⟨m0 + m1, ?_, ?_⟩
        · rw [cost_add _ m0 s s' h1, cost_succ_some g hn]
          omega
        · rw [after_add _ m0 s s' h1, emits_add _ m0 s s' h1]
          refine h8.imp id fun h a ha => ?_
          rw [emits_succ_some g hn] at ha
          rcases List.mem_append.1 ha with ha | ha
          · exact List.mem_append_left _ (h6 a ha)
          · exact List.mem_append_right _ (h a ha)

end Second

end Beside

end RwLog
