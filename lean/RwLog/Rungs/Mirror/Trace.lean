/-
# What a step of the mirrored machine shows

The mirrored machine (`Rungs/Mirror/Machine.lean`) keeps two runs and races
their steps. Here the two runs are given as two sequences of states,
`run true` for the run on the root node and `run false` for the run on its
converse, each state the one its predecessor steps to, such that the two
runs are done after the same number of steps (`Runs`).

`go_val`: with the leader at step `r` of its run and the other run some
steps behind, a step of the mirrored machine shows what step `r` of one of
the two runs shows, with the answers of the run on the converse conversed,
and leaves one run at step `r + 1` and the other not ahead of it (`At`).
Which of the two it is depends on what the steps cost; nothing else does.
-/
import RwLog.Rungs.Mirror.Machine
import RwLog.Rungs.Framework.Race
import RwLog.Rungs.Framework.TraverseStd
import RwLog.Rungs.Framework.Cost
import RwLog.Rungs.Framework.KernelAt

namespace RwLog

namespace Mirror

open Traverse

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program} {σ : Type}

/-- The answers of a run as answers of the root goal, as a value. -/
def orientV (f : Bool) (as : List (Ans D P)) : List (Ans D P) :=
  if f then as else as.map fun a => (Ans.swapA D P a).val

/-- What a step of one run shows, as a value. -/
def shownV (f : Bool) (next : σ → StOf σ) : StepOf (Ans D P) σ → StepOf (Ans D P) (StOf σ)
  | .emit as s => .emit (orientV f as) (next s)
  | .progress n s => .progress n (next s)
  | .done fin => .done (orientV f fin)

section vals

variable (K : Kernel R Cost) (hK : K.Refines D)

theorem orient_val (f : Bool) (as : List (Ans D P)) :
    (orient (K := DerivationKernel.over D K hK P) f as).val = orientV f as := by
  at_cost K hK
  cases f
  · simp only [orient, orientV, Bool.false_eq_true, ite_false, mapL_std, Cost.mapL_val]
    rfl
  · simp only [orient, orientV, ite_true, Cost.pure_val]

theorem shown_val (f : Bool) (next : σ → StOf σ) (s : StepOf (Ans D P) σ) :
    (shown (K := DerivationKernel.over D K hK P) f next s).val = shownV f next s := by
  have ho := fun as => orient_val (P := P) K hK f as
  at_cost K hK
  cases s <;> simp only [shown, shownV, Cost.bind_val, Cost.pure_val, ho]

end vals

/-- The two runs: each state steps to the next, and the two are done after
the same number of steps. -/
structure Runs (sv : σ → StepOf (Ans D P) σ) (run : Bool → Nat → σ) : Prop where
  next : ∀ d r s, after (sv (run d r)) = some s → s = run d (r + 1)
  together : ∀ r, (after (sv (run true r))).isSome = (after (sv (run false r))).isSome

/-- The state of the mirrored machine after `r` steps: the leader is at step
`r` of its run, the other run is `gap` steps behind, and neither run was done
before. -/
structure At (sv : σ → StepOf (Ans D P) σ) (run : Bool → Nat → σ) (r : Nat) (m : StOf σ) : Prop where
  gap : m.gap ≤ r
  lead : m.lead = run m.fwd r
  lag : m.lag = run (!m.fwd) (r - m.gap)
  past : ∀ r' < r, ∀ d, (after (sv (run d r'))).isSome = true

variable {sv : σ → StepOf (Ans D P) σ} {run : Bool → Nat → σ}

omit [DecidableEq R] in
theorem Runs.live (h : Runs sv run) {e : Bool} {r : Nat} {s : σ}
    (hs : after (sv (run e r)) = some s) (d : Bool) : (after (sv (run d r))).isSome = true := by
  have he : (after (sv (run e r))).isSome = true := by rw [hs]; rfl
  have := h.together r
  cases e <;> cases d <;> simp_all

omit [DecidableEq R] in
theorem Runs.past_succ (h : Runs sv run) {e : Bool} {r : Nat} {s : σ}
    (hp : ∀ r' < r, ∀ d, (after (sv (run d r'))).isSome = true)
    (hs : after (sv (run e r)) = some s) :
    ∀ r' < r + 1, ∀ d, (after (sv (run d r'))).isSome = true := fun r' hr d => by
  rcases Nat.lt_succ_iff_lt_or_eq.1 hr with hr | rfl
  · exact hp r' hr d
  · exact h.live hs d

variable (K : Kernel R Cost) (hK : K.Refines D) (step : σ → Cost (StepOf (Ans D P) σ))

theorem go_zero_val (f : Bool) (x y : σ) :
    (go (K := DerivationKernel.over D K hK P) step 0 f x y).val =
      (level (K := DerivationKernel.over D K hK P) f x y
        (Cost.race (Sum.inl <$> step x) (Sum.inr <$> step y)).val
        (Cost.race (Sum.inr <$> step y) (Sum.inl <$> step x)).val).val := by
  at_cost K hK
  simp only [go, Cost.bind_val]
  rfl

theorem go_succ_val (g : Nat) (f : Bool) (x y : σ) :
    (go (K := DerivationKernel.over D K hK P) step (g + 1) f x y).val =
      (match (Cost.race (Sum.inl <$> step x) (Sum.inr <$> step y)).val with
        | .inl sx => shown (K := DerivationKernel.over D K hK P) f (fun x' => ⟨x', y, f, g + 2⟩) sx
        | .inr sy =>
          match after sy with
          | some y' => go (K := DerivationKernel.over D K hK P) step g f x y'
          | none => shown (K := DerivationKernel.over D K hK P) (!f)
              (fun y' => ⟨y', x, !f, 0⟩) sy).val := by
  at_cost K hK
  simp only [go, Cost.bind_val]
  rw [show ∀ (α : Type) (a b : Cost α), _ = Cost.race a b from hK.race]
  generalize (Cost.race (Sum.inl <$> step x) (Sum.inr <$> step y)).val = w
  cases w with
  | inl sx => rfl
  | inr sy => cases after sy <;> rfl

/-- **A step of the mirrored machine shows step `r` of one of the two
runs.** -/
theorem go_val (h : Runs (fun s => (step s).val) run) :
    ∀ (g : Nat) (f : Bool) (x y : σ) (r : Nat), g ≤ r → x = run f r → y = run (!f) (r - g) →
      (∀ r' < r, ∀ d, (after (step (run d r')).val).isSome = true) →
      ∃ (e : Bool) (next : σ → StOf σ),
        (go (K := DerivationKernel.over D K hK P) step g f x y).val = shownV e next (step (run e r)).val ∧
        ∀ s, after (step (run e r)).val = some s → At (fun s => (step s).val) run (r + 1) (next s)
  | 0, f, x, y, r, _, hx, hy, hp => by
    subst hx
    rw [Nat.sub_zero] at hy
    subst hy
    have h₁ := Cost.race_val (Sum.inl <$> step (run f r)) (Sum.inr <$> step (run (!f) r))
    have h₂ := Cost.race_val (Sum.inr <$> step (run (!f) r)) (Sum.inl <$> step (run f r))
    simp only [Cost.map_val] at h₁ h₂
    have hv := go_zero_val K hK step f (run f r) (run (!f) r)
    rw [hv]
    -- the leader's step, shown with the other run where it was
    have lead1 : ∃ (e : Bool) (next : σ → StOf σ),
        (shown (K := DerivationKernel.over D K hK P) f (fun x' => ⟨x', run (!f) r, f, 1⟩) (step (run f r)).val).val =
          shownV e next (step (run e r)).val ∧
        ∀ s, after (step (run e r)).val = some s →
          At (fun s => (step s).val) run (r + 1) (next s) :=
      ⟨f, _, shown_val K hK _ _ _, fun s hs =>
        ⟨Nat.succ_le_succ (Nat.zero_le r), h.next f r s hs, by simp, h.past_succ hp hs⟩⟩
    have lag1 : ∃ (e : Bool) (next : σ → StOf σ),
        (shown (K := DerivationKernel.over D K hK P) (!f) (fun y' => ⟨y', run f r, !f, 1⟩) (step (run (!f) r)).val).val =
          shownV e next (step (run e r)).val ∧
        ∀ s, after (step (run e r)).val = some s →
          At (fun s => (step s).val) run (r + 1) (next s) :=
      ⟨!f, _, shown_val K hK _ _ _, fun s hs =>
        ⟨Nat.succ_le_succ (Nat.zero_le r), h.next (!f) r s hs, by simp, h.past_succ hp hs⟩⟩
    have both : ∃ (e : Bool) (next : σ → StOf σ),
        (match after (step (run (!f) r)).val with
          | some y' => shown (K := DerivationKernel.over D K hK P) f (fun x' => ⟨x', y', f, 0⟩) (step (run f r)).val
          | none =>
            match after (step (run f r)).val with
            | some _ => shown (K := DerivationKernel.over D K hK P) (!f) (fun y' => ⟨y', run f r, !f, 0⟩)
                (step (run (!f) r)).val
            | none => shown (K := DerivationKernel.over D K hK P) f (fun x' => ⟨x', run (!f) r, f, 0⟩)
                (step (run f r)).val).val =
          shownV e next (step (run e r)).val ∧
        ∀ s, after (step (run e r)).val = some s →
          At (fun s => (step s).val) run (r + 1) (next s) := by
      cases hy : after (step (run (!f) r)).val with
      | some y' =>
        exact ⟨f, _, shown_val K hK _ _ _, fun s hs =>
          ⟨Nat.zero_le _, h.next f r s hs, h.next (!f) r y' hy, h.past_succ hp hs⟩⟩
      | none =>
        cases hx : after (step (run f r)).val with
        | some x' =>
          exact ⟨!f, _, shown_val K hK _ _ _, fun s hs => by rw [hy] at hs; cases hs⟩
        | none =>
          exact ⟨f, _, shown_val K hK _ _ _, fun s hs => by rw [hx] at hs; cases hs⟩
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;> rw [h₁, h₂] <;>
      first | exact lead1 | exact lag1 | exact both
  | g + 1, f, x, y, r, hg, hx, hy, hp => by
    have h₁ := Cost.race_val (Sum.inl <$> step x) (Sum.inr <$> step y)
    simp only [Cost.map_val] at h₁
    have hv := go_succ_val K hK step g f x y
    rw [hv]
    rcases h₁ with h₁ | h₁ <;> rw [h₁]
    · subst hx
      exact ⟨f, _, shown_val K hK _ _ _, fun s hs =>
        ⟨by show g + 2 ≤ r + 1; omega, h.next f r s hs,
          by show y = run (!f) (r + 1 - (g + 2)); rw [hy]; congr 1; omega, h.past_succ hp hs⟩⟩
    · have hlive := hp (r - (g + 1)) (by omega) (!f)
      rw [← hy] at hlive
      cases hy' : after (step y).val with
      | none => rw [hy'] at hlive; cases hlive
      | some y' =>
        simp only [hy']
        refine go_val h g f x y' r (by omega) hx ?_ hp
        have := h.next (!f) (r - (g + 1)) y' (by rw [← hy]; exact hy')
        rw [this]; congr 1; omega

end Mirror

end RwLog
