/-
# What the mirrored machine costs, from below

`Mirror.cost step x n` is what the first `n` steps from `x` cost. Started
with the leader at `x` and the other run at `y`, `g` steps behind, the first
`n` steps of the mirrored machine cost at least the cheaper of `n` steps from
`x` and `g + n` steps from `y` (`cost_ge`): every step either run takes is
the winner of a race, and a race costs at least its winner
(`Cost.winner_le_raceCost`).

For an engine this is `Mirror.paid_ge_min`: what the mirrored engine has paid
by its `n`-th step is at least the cheaper of `n` steps of the engine from
the root node and from its converse. It is the lemma a lower bound on a
mirrored machine starts from. It does not depend on what the runs emit.

The only facts about charges used are that a race costs at least its winner
and that `bind` adds ticks.
-/
import RwLog.Rungs.Mirror.Trace
import RwLog.Rungs.Framework.RaceWinner
import RwLog.Rungs.Framework.Derivation

namespace RwLog

namespace Mirror

open Traverse

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program} {σ : Type}

/-- What the first `n` steps from a state cost. A finished run costs nothing
more. -/
def cost {A τ : Type} (step : τ → Cost (StepOf A τ)) : τ → Nat → Nat
  | _, 0 => 0
  | s, n + 1 =>
    (step s).ticks + match after (step s).val with
      | some s' => cost step s' n
      | none => 0

theorem cost_succ {A τ : Type} (step : τ → Cost (StepOf A τ)) (s : τ) (n : Nat) :
    cost step s (n + 1) = (step s).ticks + match after (step s).val with
      | some s' => cost step s' n
      | none => 0 := by
  rw [cost]

theorem cost_succ_some {A τ : Type} {step : τ → Cost (StepOf A τ)} {s s' : τ} (n : Nat)
    (h : after (step s).val = some s') :
    cost step s (n + 1) = (step s).ticks + cost step s' n := by
  rw [cost, h]

theorem cost_succ_none {A τ : Type} {step : τ → Cost (StepOf A τ)} {s : τ} (n : Nat)
    (h : after (step s).val = none) : cost step s (n + 1) = (step s).ticks := by
  rw [cost, h]; rfl

omit [DecidableEq R] in
theorem after_shownV (f : Bool) (next : σ → StOf σ) (s : StepOf (Ans D P) σ) :
    after (shownV f next s) = (after s).map next := by
  cases s <;> rfl

variable (K : Kernel R Cost) (hK : K.Refines D) (step : σ → Cost (StepOf (Ans D P) σ))

/-- A step of the mirrored machine. -/
abbrev mstep (m : StOf σ) : Cost (StepOf (Ans D P) (StOf σ)) :=
  go (K := DerivationKernel.over D K hK P) step m.gap m.fwd m.lead m.lag

omit [DecidableEq R] in
/-- The race of a step of `x` before a step of `y`: which step it returns. -/
theorem race_inl_inr (x y : σ) :
    (Cost.race (Sum.inl <$> step x) (Sum.inr <$> step y) :
        Cost (StepOf (Ans D P) σ ⊕ StepOf (Ans D P) σ)).val =
      if Cost.firstWins (step x).ticks (step y).ticks then .inl (step x).val
      else .inr (step y).val := by
  rw [Cost.race_val_eq]; rfl

omit [DecidableEq R] in
theorem race_inr_inl (x y : σ) :
    (Cost.race (Sum.inr <$> step y) (Sum.inl <$> step x) :
        Cost (StepOf (Ans D P) σ ⊕ StepOf (Ans D P) σ)).val =
      if Cost.firstWins (step y).ticks (step x).ticks then .inr (step y).val
      else .inl (step x).val := by
  rw [Cost.race_val_eq]; rfl

/-- From level runs the machine pays for both races. -/
theorem go_zero_ticks (f : Bool) (x y : σ) :
    Cost.raceCost (step x).ticks (step y).ticks + Cost.raceCost (step y).ticks (step x).ticks ≤
      (go (K := DerivationKernel.over D K hK P) step 0 f x y).ticks := by
  have h₁ := Cost.race_ticks_eq (Sum.inl <$> step x : Cost (StepOf (Ans D P) σ ⊕ _))
    (Sum.inr <$> step y)
  have h₂ := Cost.race_ticks_eq (Sum.inr <$> step y : Cost (StepOf (Ans D P) σ ⊕ _))
    (Sum.inl <$> step x)
  simp only [Cost.map_ticks] at h₁ h₂
  rw [← h₁, ← h₂]
  at_cost K hK
  simp only [go, Cost.bind_ticks]
  show _ ≤ _ + ((Cost.race (Sum.inl <$> step x) (Sum.inr <$> step y)).ticks +
    ((Cost.race (Sum.inr <$> step y) (Sum.inl <$> step x)).ticks + _))
  omega

/-- From a gap the machine pays for the race, and for what it does next. -/
theorem go_succ_ticks (g : Nat) (f : Bool) (x y : σ) :
    (go (K := DerivationKernel.over D K hK P) step (g + 1) f x y).ticks =
      1 + Cost.raceCost (step x).ticks (step y).ticks +
      (match (Cost.race (Sum.inl <$> step x) (Sum.inr <$> step y)).val with
        | .inl sx => shown (K := DerivationKernel.over D K hK P) f (fun x' => ⟨x', y, f, g + 2⟩) sx
        | .inr sy =>
          match after sy with
          | some y' => go (K := DerivationKernel.over D K hK P) step g f x y'
          | none => shown (K := DerivationKernel.over D K hK P) (!f)
              (fun y' => ⟨y', x, !f, 0⟩) sy).ticks := by
  have h₁ := Cost.race_ticks_eq (Sum.inl <$> step x : Cost (StepOf (Ans D P) σ ⊕ _))
    (Sum.inr <$> step y)
  simp only [Cost.map_ticks] at h₁
  rw [← h₁]
  at_cost K hK
  simp only [go, Cost.bind_ticks]
  rw [show ∀ (α : Type) (a b : Cost α), _ = Cost.race a b from hK.race]
  generalize (Cost.race (Sum.inl <$> step x) (Sum.inr <$> step y)) = w
  show 1 + (w.ticks + _) = _
  rw [Nat.add_assoc]
  congr 2
  rcases w with ⟨v, t, _, _, _⟩
  cases v with
  | inl sx => rfl
  | inr sy => cases after sy <;> rfl

/-- The statement of `cost_ge` for one number of steps. -/
def CostGe (n g : Nat) (f : Bool) (x y : σ) : Prop :=
  min (cost step x n) (cost step y (g + n)) ≤ cost (mstep K hK step) ⟨x, y, f, g⟩ n

theorem cost_ge_level {n : Nat} (ih : ∀ g f x y, CostGe K hK step n g f x y)
    (f : Bool) (x y : σ) : CostGe K hK step (n + 1) 0 f x y := by
  unfold CostGe
  rw [Nat.zero_add]
  have ht := go_zero_ticks K hK step f x y
  have hv := go_zero_val K hK step f x y
  rw [race_inl_inr, race_inr_inl] at hv
  have w₁ := Cost.winner_le_raceCost (step x).ticks (step y).ticks
  have w₂ := Cost.winner_le_raceCost (step y).ticks (step x).ticks
  -- what the machine has spent, by the state it goes to
  have hsome : ∀ m, after (go (K := DerivationKernel.over D K hK P) step 0 f x y).val = some m →
      cost (mstep K hK step) ⟨x, y, f, 0⟩ (n + 1) =
        (go (K := DerivationKernel.over D K hK P) step 0 f x y).ticks +
          cost (mstep K hK step) m n := fun m hm => cost_succ_some n hm
  have hle : (go (K := DerivationKernel.over D K hK P) step 0 f x y).ticks ≤
      cost (mstep K hK step) ⟨x, y, f, 0⟩ (n + 1) := by
    show _ ≤ (go (K := DerivationKernel.over D K hK P) step 0 f x y).ticks + _
    omega
  have hx : ∀ x', after (step x).val = some x' →
      cost step x (n + 1) = (step x).ticks + cost step x' n := fun _ h => cost_succ_some n h
  have hy : ∀ y', after (step y).val = some y' →
      cost step y (n + 1) = (step y).ticks + cost step y' n := fun _ h => cost_succ_some n h
  have hxn : after (step x).val = none → cost step x (n + 1) = (step x).ticks :=
    cost_succ_none n
  have hyn : after (step y).val = none → cost step y (n + 1) = (step y).ticks :=
    cost_succ_none n
  cases h₁ : Cost.firstWins (step x).ticks (step y).ticks <;>
    cases h₂ : Cost.firstWins (step y).ticks (step x).ticks <;>
    simp only [h₁, h₂, ite_true, ite_false, Bool.false_eq_true] at hv w₁ w₂
  · -- each race is won by the second: both runs step
    have hv' : (go (K := DerivationKernel.over D K hK P) step 0 f x y).val =
        (match after (step y).val with
          | some y' => shown (K := DerivationKernel.over D K hK P) f (fun x' => ⟨x', y', f, 0⟩)
              (step x).val
          | none =>
            match after (step x).val with
            | some _ => shown (K := DerivationKernel.over D K hK P) (!f)
                (fun y' => ⟨y', x, !f, 0⟩) (step y).val
            | none => shown (K := DerivationKernel.over D K hK P) f (fun x' => ⟨x', y, f, 0⟩)
                (step x).val).val := hv
    cases ey : after (step y).val with
    | none => rw [hyn ey]; omega
    | some y' =>
      rw [ey] at hv'
      simp only [shown_val] at hv'
      cases ex : after (step x).val with
      | none => rw [hxn ex]; omega
      | some x' =>
        have ha : after (go (K := DerivationKernel.over D K hK P) step 0 f x y).val =
            some ⟨x', y', f, 0⟩ := by rw [hv', after_shownV, ex]; rfl
        have h1 := ih 0 f x' y'
        unfold CostGe at h1
        rw [Nat.zero_add] at h1
        rw [hsome _ ha, hx _ ex, hy _ ey]
        omega
  · -- the other run wins both
    have hv' : (go (K := DerivationKernel.over D K hK P) step 0 f x y).val =
        (shown (K := DerivationKernel.over D K hK P) (!f) (fun y' => ⟨y', x, !f, 1⟩)
          (step y).val).val := hv
    rw [shown_val] at hv'
    cases ey : after (step y).val with
    | none => rw [hyn ey]; omega
    | some y' =>
      have ha : after (go (K := DerivationKernel.over D K hK P) step 0 f x y).val =
          some ⟨y', x, !f, 1⟩ := by rw [hv', after_shownV, ey]; rfl
      have h1 := ih 1 (!f) y' x
      unfold CostGe at h1
      rw [show 1 + n = n + 1 by omega] at h1
      rw [hsome _ ha, hy _ ey]
      omega
  · -- the leader wins both
    have hv' : (go (K := DerivationKernel.over D K hK P) step 0 f x y).val =
        (shown (K := DerivationKernel.over D K hK P) f (fun x' => ⟨x', y, f, 1⟩)
          (step x).val).val := hv
    rw [shown_val] at hv'
    cases ex : after (step x).val with
    | none => rw [hxn ex]; omega
    | some x' =>
      have ha : after (go (K := DerivationKernel.over D K hK P) step 0 f x y).val =
          some ⟨x', y, f, 1⟩ := by rw [hv', after_shownV, ex]; rfl
      have h1 := ih 1 f x' y
      unfold CostGe at h1
      rw [show 1 + n = n + 1 by omega] at h1
      rw [hsome _ ha, hx _ ex]
      omega
  · -- each race is won by the first: both runs step
    have hv' : (go (K := DerivationKernel.over D K hK P) step 0 f x y).val =
        (match after (step y).val with
          | some y' => shown (K := DerivationKernel.over D K hK P) f (fun x' => ⟨x', y', f, 0⟩)
              (step x).val
          | none =>
            match after (step x).val with
            | some _ => shown (K := DerivationKernel.over D K hK P) (!f)
                (fun y' => ⟨y', x, !f, 0⟩) (step y).val
            | none => shown (K := DerivationKernel.over D K hK P) f (fun x' => ⟨x', y, f, 0⟩)
                (step x).val).val := hv
    cases ey : after (step y).val with
    | none => rw [hyn ey]; omega
    | some y' =>
      rw [ey] at hv'
      simp only [shown_val] at hv'
      cases ex : after (step x).val with
      | none => rw [hxn ex]; omega
      | some x' =>
        have ha : after (go (K := DerivationKernel.over D K hK P) step 0 f x y).val =
            some ⟨x', y', f, 0⟩ := by rw [hv', after_shownV, ex]; rfl
        have h1 := ih 0 f x' y'
        unfold CostGe at h1
        rw [Nat.zero_add] at h1
        rw [hsome _ ha, hx _ ex, hy _ ey]
        omega

theorem cost_ge_behind {n : Nat} (ih : ∀ g f x y, CostGe K hK step n g f x y)
    (g : Nat) (f : Bool) (x y : σ)
    (hc : ∀ y', after (step y).val = some y' → CostGe K hK step (n + 1) g f x y') :
    CostGe K hK step (n + 1) (g + 1) f x y := by
  unfold CostGe
  have ht := go_succ_ticks K hK step g f x y
  have hv := go_succ_val K hK step g f x y
  rw [race_inl_inr] at hv ht
  have w₁ := Cost.winner_le_raceCost (step x).ticks (step y).ticks
  cases h₁ : Cost.firstWins (step x).ticks (step y).ticks <;>
    simp only [h₁, ite_true, ite_false, Bool.false_eq_true] at hv ht w₁
  · -- the other run catches up by a step
    cases ey : after (step y).val with
    | none =>
      rw [show g + 1 + (n + 1) = (g + 1 + n) + 1 by omega, cost_succ_none _ ey]
      have : (go (K := DerivationKernel.over D K hK P) step (g + 1) f x y).ticks ≤
          cost (mstep K hK step) ⟨x, y, f, g + 1⟩ (n + 1) := by
        show _ ≤ (go (K := DerivationKernel.over D K hK P) step (g + 1) f x y).ticks + _
        omega
      omega
    | some y' =>
      simp only [ey] at hv ht
      have h1 := hc y' ey
      unfold CostGe at h1
      have hm : cost (mstep K hK step) ⟨x, y, f, g + 1⟩ (n + 1) =
          1 + Cost.raceCost (step x).ticks (step y).ticks +
            cost (mstep K hK step) ⟨x, y', f, g⟩ (n + 1) := by
        rw [cost_succ, cost_succ,
          show mstep K hK step ⟨x, y, f, g + 1⟩ =
            go (K := DerivationKernel.over D K hK P) step (g + 1) f x y from rfl,
          show mstep K hK step ⟨x, y', f, g⟩ =
            go (K := DerivationKernel.over D K hK P) step g f x y' from rfl]
        rw [ht, hv]; omega
      rw [hm, show g + 1 + (n + 1) = (g + (n + 1)) + 1 by omega, cost_succ_some _ ey]
      omega
  · -- the leader steps
    have hv' : (go (K := DerivationKernel.over D K hK P) step (g + 1) f x y).val =
        (shown (K := DerivationKernel.over D K hK P) f (fun x' => ⟨x', y, f, g + 2⟩)
          (step x).val).val := hv
    rw [shown_val] at hv'
    have hle : (go (K := DerivationKernel.over D K hK P) step (g + 1) f x y).ticks ≤
        cost (mstep K hK step) ⟨x, y, f, g + 1⟩ (n + 1) := by
      show _ ≤ (go (K := DerivationKernel.over D K hK P) step (g + 1) f x y).ticks + _
      omega
    cases ex : after (step x).val with
    | none => rw [cost_succ_none _ ex]; omega
    | some x' =>
      have ha : after (go (K := DerivationKernel.over D K hK P) step (g + 1) f x y).val =
          some ⟨x', y, f, g + 2⟩ := by rw [hv', after_shownV, ex]; rfl
      have h1 := ih (g + 2) f x' y
      unfold CostGe at h1
      rw [show g + 2 + n = g + 1 + (n + 1) by omega] at h1
      have hm : cost (mstep K hK step) ⟨x, y, f, g + 1⟩ (n + 1) =
          (go (K := DerivationKernel.over D K hK P) step (g + 1) f x y).ticks +
            cost (mstep K hK step) ⟨x', y, f, g + 2⟩ n := cost_succ_some n ha
      rw [hm, cost_succ_some _ ex]
      omega

/-- **The first `n` steps of the mirrored machine cost at least the cheaper
of `n` steps of the leader and `g + n` steps of the other run.** -/
theorem cost_ge : ∀ (n g : Nat) (f : Bool) (x y : σ), CostGe K hK step n g f x y := by
  intro n
  induction n with
  | zero => intro g f x y; exact Nat.le_trans (Nat.min_le_left _ _) (Nat.le_refl 0)
  | succ n ih =>
    intro g
    induction g with
    | zero => intro f x y; exact cost_ge_level K hK step ih f x y
    | succ g ihg =>
      intro f x y
      exact cost_ge_behind K hK step ih g f x y fun y' _ => ihg f x y'

end Mirror

/-! ## For an engine -/

section engine

variable (E : Engine) {R : Sorts → Type} [∀ S, Answer (R S)] [∀ S, DecidableEq (R S)]
  (dom : ∀ S, Domain (R S)) (K : ∀ S, Kernel (R S) Cost) (hK : ∀ S, (K S).Refines (dom S))

/-- A step of the engine on a program, before its answers are reported. -/
abbrev Engine.stepAt (P : Program) (s : E.State (R P.sorts) Rel (Ans (dom P.sorts) P)) :
    Cost (StepOf (Ans (dom P.sorts) P) (E.State (R P.sorts) Rel (Ans (dom P.sorts) P))) :=
  @Engine.step E (R P.sorts) Rel (Ans (dom P.sorts) P) Cost
    (DerivationKernel.over (dom P.sorts) (K P.sorts) (hK P.sorts) P) s

/-- The state the engine starts in on a node. -/
abbrev Engine.startAt (P : Program) (root : Rel) : E.State (R P.sorts) Rel (Ans (dom P.sorts) P) :=
  (@Engine.init E (R P.sorts) Rel (Ans (dom P.sorts) P) Cost
    (DerivationKernel.over (dom P.sorts) (K P.sorts) (hK P.sorts) P) root).val

/-- The machine of an engine spends at least what the steps of the engine
cost: reporting the answers is paid on top. -/
theorem Engine.cost_le_spent (P : Program) (root : Rel) :
    ∀ (n : Nat) (st : E.State (R P.sorts) Rel (Ans (dom P.sorts) P)),
      Mirror.cost (E.stepAt dom K hK P) st n ≤
        (E.costedAt dom K hK).spent (⟨P, root, st⟩ : E.StateAt dom) n
  | 0, _ => Nat.le_refl 0
  | n + 1, st => by
    have hv := Engine.costedAt_step_val (E := E) (dom := dom) (K := K) (hK := hK)
      (⟨P, root, st⟩ : E.StateAt dom)
    have ht : (E.stepAt dom K hK P st).ticks ≤
        ((E.costedAt dom K hK).step (⟨P, root, st⟩ : E.StateAt dom)).ticks := by
      show _ ≤ (E.stepAt dom K hK P st >>= E.report dom P root).ticks
      rw [Cost.bind_ticks]; omega
    rw [Mirror.cost_succ]
    dsimp only at hv
    cases hs : (E.stepAt dom K hK P st).val with
    | emit as st' =>
      have := Engine.cost_le_spent P root n st'
      rw [hs] at hv
      rw [(E.costedAt dom K hK).spent_succ_emit hv]
      simp only [Mirror.after]
      omega
    | progress k st' =>
      have := Engine.cost_le_spent P root n st'
      rw [hs] at hv
      rw [(E.costedAt dom K hK).spent_succ_progress hv]
      simp only [Mirror.after]
      omega
    | done fin =>
      rw [hs] at hv
      rw [(E.costedAt dom K hK).spent_succ_done hv]
      simp only [Mirror.after]
      omega

theorem Engine.mirrored_init_val {R : Type} [Answer R] [DecidableEq R] {D : Domain R}
    (K : Kernel R Cost) (hK : K.Refines D) (P : Program) (root : Rel) :
    (@Engine.init E.mirrored R Rel (Ans D P) Cost (DerivationKernel.over D K hK P) root).val =
      ⟨(@Engine.init E R Rel (Ans D P) Cost (DerivationKernel.over D K hK P) root).val,
        (@Engine.init E R Rel (Ans D P) Cost (DerivationKernel.over D K hK P) root.normConv).val,
        true, 0⟩ := by
  at_cost K hK
  rfl

/-- The first state of the mirrored engine: the two first states of the
engine, on the node and on its converse. -/
theorem Engine.mirrored_startAt (P : Program) (root : Rel) :
    E.mirrored.startAt dom K hK P root =
      ⟨E.startAt dom K hK P root, E.startAt dom K hK P root.normConv, true, 0⟩ :=
  E.mirrored_init_val (K P.sorts) (hK P.sorts) P root

/-- **The mirrored engine pays at least the cheaper of the two runs.** What
it has paid on `q` by its `n`-th step is at least the cheaper of the first
`n` steps of the engine from the node of `q` and from its converse. -/
theorem Mirror.paid_ge_min (P : Program) (q : Rel) (n : Nat) :
    min (Mirror.cost (E.stepAt dom K hK P) (E.startAt dom K hK P q.norm) n)
        (Mirror.cost (E.stepAt dom K hK P) (E.startAt dom K hK P q.norm.normConv) n) ≤
      (E.mirrored.costedAt dom K hK).paid P q n := by
  have h := Mirror.cost_ge (K P.sorts) (hK P.sorts) (E.stepAt dom K hK P) n 0 true
    (E.startAt dom K hK P q.norm) (E.startAt dom K hK P q.norm.normConv)
  unfold Mirror.CostGe at h
  rw [Nat.zero_add] at h
  have h₂ := Engine.cost_le_spent E.mirrored dom K hK P q.norm n
    (E.mirrored.startAt dom K hK P q.norm)
  rw [Engine.mirrored_startAt] at h₂
  have h₃ : (E.mirrored.costedAt dom K hK).start P q =
      ⟨P, q.norm, E.mirrored.startAt dom K hK P q.norm⟩ := rfl
  have h₄ : (E.mirrored.costedAt dom K hK).spent ((E.mirrored.costedAt dom K hK).start P q) n ≤
      (E.mirrored.costedAt dom K hK).paid P q n := Nat.le_add_left _ _
  rw [h₃, Engine.mirrored_startAt] at h₄
  exact Nat.le_trans h (Nat.le_trans h₂ h₄)

end engine

end RwLog
