/-
# Two engines side by side on a root that is its own converse

A machine shows its own converse from a state (`Runtime.ShowsSelf`) when
every step of the run from it shows a list of answers that agrees with the
list of their converses. If the machines of two engines show their own
converse on a root that is its own converse, so does the machine of the pair
(`Engine.beside_selfConverse`): each step of the pair shows what a step of
one of its engines shows, or nothing.
-/
import RwLog.Rungs.Framework.BesideLaws
import RwLog.Rungs.Framework.Oriented

namespace RwLog

namespace Runtime

variable (R : Runtime) (M : Interp)

/-- Every step of the run from `s` shows a list of answers that agrees with
the list of their converses. -/
def ShowsSelf (s : R.State) : Prop :=
  ∀ n, TraceEquiv M (R.trace s n) ((R.trace s n).map Shown.swap)

variable {R M}

theorem ShowsSelf.emit {s s' : R.State} {as : List R.Ans} (h : R.step s = .emit as s')
    (hs : R.ShowsSelf M s) : StepEquiv M as (as.map Answer.swap) ∧ R.ShowsSelf M s' := by
  refine ⟨?_, fun n => ?_⟩
  · have := hs 1
    rw [R.trace_succ_emit h] at this
    exact (List.forall₂_cons.1 this).1
  · have := hs (n + 1)
    rw [R.trace_succ_emit h] at this
    exact (List.forall₂_cons.1 this).2

theorem ShowsSelf.done {s : R.State} {fin : List R.Ans} (h : R.step s = .done fin)
    (hs : R.ShowsSelf M s) : StepEquiv M fin (fin.map Answer.swap) := by
  have := hs 1
  rw [R.trace_succ_done h] at this
  exact (List.forall₂_cons.1 this).1

end Runtime

namespace Beside

variable {A X Y : Type} (f : X → Cost (StepOf A X)) (g : Y → Cost (StepOf A Y))

/-- A step of the pair gives a step up and shows nothing, or is the next
step of its first engine, or shows what the next step of its second engine
shows. -/
theorem stepC_cases (s : State X Y) :
    (∃ s', (stepC f g s).val = .emit [] s' ∧ s'.fst = s.fst ∧ s'.snd = s.snd) ∨
    (match (f s.fst).val with
      | .emit as x => ∃ s', (stepC f g s).val = .emit as s' ∧ s'.fst = x ∧ s'.snd = s.snd
      | .done fin => (stepC f g s).val = .done fin) ∨
    (∃ y s', s.snd = some y ∧ s'.fst = s.fst ∧
      match (g y).val with
      | .emit as y' => (stepC f g s).val = .emit as s' ∧ s'.snd = some y'
      | .done fin => (stepC f g s).val = .emit fin s' ∧ s'.snd = none) := by
  cases hy : s.snd with
  | none =>
    refine .inr (.inl ?_)
    rw [(alone f g hy).1]
    cases (f s.fst).val with
    | emit as x => exact ⟨_, rfl, rfl, hy⟩
    | done fin => rfl
  | some y =>
    by_cases ht : s.paidFst ≤ s.paidSnd
    · by_cases hb : price f s.fst ≤ budget s.gaveFst
      · refine .inr (.inl ?_)
        rw [(fst_fit f g hy ht hb).1]
        cases (f s.fst).val with
        | emit as x => exact ⟨_, rfl, rfl, hy⟩
        | done fin => rfl
      · exact .inl ⟨_, (fst_fail f g hy ht (Nat.not_le.1 hb)).1, rfl, hy⟩
    · by_cases hb : price g y ≤ budget s.gaveSnd
      · refine .inr (.inr ⟨y,
          ⟨s.fst, next (g y).val, s.paidFst, s.paidSnd + price g y + 1, s.gaveFst, 0⟩, rfl, rfl, ?_⟩)
        rw [(snd_fit f g hy ht hb).1]
        cases (g y).val with
        | emit as y' => exact ⟨rfl, rfl⟩
        | done fin => exact ⟨rfl, rfl⟩
      · exact .inl ⟨_, (snd_fail f g hy ht (Nat.not_le.1 hb)).1, rfl, hy⟩

end Beside

namespace Engine

open Beside

variable (E F : Engine) {R : Sorts → Type} [∀ S, Answer (R S)] [∀ S, DecidableEq (R S)]
  (dom : ∀ S, Domain (R S)) (K : ∀ S, Kernel (R S) Cost) (hK : ∀ S, (K S).Refines (dom S))
  (cells : ∀ S, R S → Nat)

/-- **The machine of the pair shows its own converse from a state from which
the machines of its two engines do.** -/
theorem beside_showsSelf (M : Interp) : ∀ (m : Nat) (s : (E.beside F).StateAt dom),
    (E.costedAt dom K hK cells).runtime.ShowsSelf M (fstAt E F dom s) →
    (∀ y, s.st.snd = some y → (F.costedAt dom K hK cells).runtime.ShowsSelf M ⟨s.P, s.root, y⟩) →
    TraceEquiv M (((E.beside F).costedAt dom K hK cells).runtime.trace s m)
      ((((E.beside F).costedAt dom K hK cells).runtime.trace s m).map Shown.swap)
  | 0, _, _, _ => List.Forall₂.nil
  | m + 1, s, h1, h2 => by
    have hv := machine_step (E.beside F) dom K hK cells s
    rw [beside_stepAt] at hv
    have hE := machine_step E dom K hK cells ⟨s.P, s.root, s.st.fst⟩
    rcases stepC_cases (E.stepAt dom K hK s.P) (F.stepAt dom K hK s.P) s.st with
      ⟨s', hs, hf, hy⟩ | hc | ⟨y, s', hy, hf, hc⟩
    · rw [hs] at hv
      have hs' : ((E.beside F).costedAt dom K hK cells).runtime.step s =
          .emit (shownAt dom s.P s.root []) ⟨s.P, s.root, s'⟩ := hv
      rw [Runtime.trace_succ_emit _ hs']
      refine List.Forall₂.cons (StepEquiv.refl _) (beside_showsSelf M m _ ?_ ?_)
      · show (E.costedAt dom K hK cells).runtime.ShowsSelf M ⟨s.P, s.root, s'.fst⟩
        rw [hf]; exact h1
      · intro y hy'
        exact h2 y (by rw [← hy]; exact hy')
    · cases hr : (E.stepAt dom K hK s.P s.st.fst).val with
      | emit as x =>
        rw [hr] at hc hE
        obtain ⟨s', hs, hf, hy⟩ := hc
        have hE' : (E.costedAt dom K hK cells).runtime.step (fstAt E F dom s) =
            .emit (shownAt dom s.P s.root as) ⟨s.P, s.root, x⟩ := hE
        obtain ⟨e1, e2⟩ := h1.emit hE'
        rw [hs] at hv
        have hs' : ((E.beside F).costedAt dom K hK cells).runtime.step s =
            .emit (shownAt dom s.P s.root as) ⟨s.P, s.root, s'⟩ := hv
        rw [Runtime.trace_succ_emit _ hs']
        refine List.Forall₂.cons e1 (beside_showsSelf M m _ ?_ ?_)
        · show (E.costedAt dom K hK cells).runtime.ShowsSelf M ⟨s.P, s.root, s'.fst⟩
          rw [hf]; exact e2
        · intro y hy'
          exact h2 y (by rw [← hy]; exact hy')
      | done fin =>
        rw [hr] at hc hE
        have hE' : (E.costedAt dom K hK cells).runtime.step (fstAt E F dom s) =
            .done (shownAt dom s.P s.root fin) := hE
        have e1 := h1.done hE'
        rw [hc] at hv
        have hs' : ((E.beside F).costedAt dom K hK cells).runtime.step s =
            .done (shownAt dom s.P s.root fin) := hv
        rw [Runtime.trace_succ_done _ hs']
        exact List.Forall₂.cons e1 .nil
    · have hF := machine_step F dom K hK cells ⟨s.P, s.root, y⟩
      have h2y := h2 y hy
      have hfst : (E.costedAt dom K hK cells).runtime.ShowsSelf M ⟨s.P, s.root, s'.fst⟩ := by
        rw [hf]; exact h1
      cases hr : (F.stepAt dom K hK s.P y).val with
      | emit as y' =>
        rw [hr] at hc hF
        obtain ⟨hs, hy'⟩ := hc
        have hF' : (F.costedAt dom K hK cells).runtime.step ⟨s.P, s.root, y⟩ =
            .emit (shownAt dom s.P s.root as) ⟨s.P, s.root, y'⟩ := hF
        obtain ⟨e1, e2⟩ := h2y.emit hF'
        rw [hs] at hv
        have hs' : ((E.beside F).costedAt dom K hK cells).runtime.step s =
            .emit (shownAt dom s.P s.root as) ⟨s.P, s.root, s'⟩ := hv
        rw [Runtime.trace_succ_emit _ hs']
        refine List.Forall₂.cons e1 (beside_showsSelf M m _ hfst ?_)
        intro z hz
        have : z = y' := Option.some.inj (hz.symm.trans hy')
        rw [this]; exact e2
      | done fin =>
        rw [hr] at hc hF
        obtain ⟨hs, hy'⟩ := hc
        have hF' : (F.costedAt dom K hK cells).runtime.step ⟨s.P, s.root, y⟩ =
            .done (shownAt dom s.P s.root fin) := hF
        have e1 := h2y.done hF'
        rw [hs] at hv
        have hs' : ((E.beside F).costedAt dom K hK cells).runtime.step s =
            .emit (shownAt dom s.P s.root fin) ⟨s.P, s.root, s'⟩ := hv
        rw [Runtime.trace_succ_emit _ hs']
        refine List.Forall₂.cons e1 (beside_showsSelf M m _ hfst ?_)
        intro z hz
        rw [hy'] at hz
        cases hz

/-- **On a root that is its own converse the machine of the pair shows its
own converse, if the machines of its two engines do.** -/
theorem beside_selfConverse (hE : (E.costedAt dom K hK cells).SelfConverse)
    (hF : (F.costedAt dom K hK cells).SelfConverse) :
    ((E.beside F).costedAt dom K hK cells).SelfConverse := by
  intro P root hwf hP hN hfo hself n
  refine beside_showsSelf E F dom K hK cells _ n _ ?_ ?_
  · rw [beside_start_fst]
    exact hE P root hwf hP hN hfo hself
  · rw [beside_start]
    intro y hy
    obtain rfl := Option.some.inj hy
    exact hF P root hwf hP hN hfo hself

end Engine

end RwLog
