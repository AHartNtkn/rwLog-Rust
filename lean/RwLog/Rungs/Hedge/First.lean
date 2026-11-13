/-
# The hedge is never much slower than its first machine

Whatever `B` does, `Hedge.machine A B` has taken `n` steps of `A` after
spending at most `Hedge.bound`, a polynomial in what `A` spends on those
steps (`bound_le`), and by then it has emitted an answer covering each answer
of `A`, and has halted if `A` has (`follows_first`).

Why it is bounded. While `A`'s next step costs `o` and `A` carries the
handicap `p`, `B` can only win a race it finishes in less than `p + o`, and
each win raises `B`'s own handicap by one: after at most `2 (p + o) + 1` wins
`A` wins. Each of those races costs at most 7 times `B`'s side, so less than
`14 (p + o)`, and the answers `B` emits in them have sizes adding up to less
than `p + o` each time, so comparing `A`'s answers with them stays cheap.
-/
import RwLog.Rungs.Hedge.Steps
import RwLog.Rungs.Framework.Runtime
import Mathlib.Tactic.Ring

namespace RwLog

open Cost

namespace Hedge

variable (A B : CostedRuntime)

/-- What the hedge may spend to take `n` steps of `A` from the state `a`,
when `A` carries the handicap `p`, `B` can win at most `c` more races before
`A`'s next step, and the answers of `B` emitted so far have sizes adding up to
`σ`. -/
def bound : Nat → A.State → Nat → Nat → Nat → Nat
  | 0, _, _, _, _ => 0
  | n + 1, a, p, c, σ =>
    14 * c * (p + (A.step a).ticks) + 7 * (p + (A.step a).ticks) +
      2 * (A.step a).ticks * (σ + 2 * c * (p + (A.step a).ticks)) +
      match (A.step a).val with
      | .emit _ a' => bound n a' (p + 1) (2 * (p + 1 + (A.step a').ticks) + 1)
          (σ + 2 * c * (p + (A.step a).ticks))
      | .done => 0

theorem bound_succ_c (n : Nat) (a : A.State) (p c σ : Nat) :
    bound A (n + 1) a p (c + 1) σ =
      14 * (p + (A.step a).ticks) + bound A (n + 1) a p c (σ + 2 * (p + (A.step a).ticks)) := by
  have e : σ + 2 * (c + 1) * (p + (A.step a).ticks) =
      σ + 2 * (p + (A.step a).ticks) + 2 * c * (p + (A.step a).ticks) := by ring
  simp only [bound, e]
  ring

variable {A B}

/-- The claim, for one state: `n` steps of `A` are taken within the bound. -/
def Follows (n c : Nat) (st : State A.State B.State) (p σ : Nat) : Prop :=
  Inv A B st →
  (st.live = true → padA A B st ≤ p ∧
    2 * (padA A B st + (A.step st.a).ticks) + 1 ≤ c + padB A B st) →
  sizes st.seenB ≤ σ →
  ∃ m, (machine A B).spent st m ≤ bound A n st.a p c σ ∧
    (∀ x ∈ A.runtime.emitted st.a n,
      ∃ y ∈ st.seen ++ (machine A B).runtime.emitted st m, y.Covers x) ∧
    (A.runtime.Halts st.a n → (machine A B).runtime.Halts st m)

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
  ⟨h.plain, fun t ht => List.mem_append_left _ (h.sub t ht)⟩

/-- What the comparison of `A`'s answers with `B`'s costs. -/
theorem afterA_ticks_le {st : State A.State B.State} (h : Inv A B st) {as : List Span} {o σ : Nat}
    (ho : sizes as ≤ o) (hσ : sizes st.seenB ≤ σ) :
    (dropCovered st.seenB as).ticks ≤ 2 * o * σ := by
  have h1 := dropCovered_ticks h.plain as
  have h2 := length_le_sizes as
  have h3 := length_le_sizes st.seenB
  have h4 : as.length * sizes st.seenB ≤ o * σ := Nat.mul_le_mul (le_trans h2 ho) hσ
  have h5 : st.seenB.length * sizes as ≤ σ * o := Nat.mul_le_mul (le_trans h3 hσ) ho
  have h6 : 2 * o * σ = o * σ + σ * o := by ring
  omega

variable (hA : ∀ (s : A.State) (as : List Span) (s' : A.State),
  (A.step s).val = .emit as s' → sizes as ≤ (A.step s).ticks)

include hA in
/-- A step of the hedge that is a step of `A`. -/
theorem follows_take {n : Nat} (ihn : ∀ c (st : State A.State B.State) p σ, Follows n c st p σ)
    {c : Nat} {st : State A.State B.State} {p σ : Nat} (hinv : Inv A B st)
    (hp : st.live = true → padA A B st ≤ p) (hσ : sizes st.seenB ≤ σ)
    (hv : (step A B st).val = (afterA A B st (A.step st.a).val).val)
    (ht : (step A B st).ticks ≤ 7 * (p + (A.step st.a).ticks) +
      (afterA A B st (A.step st.a).val).ticks) :
    ∃ m, (machine A B).spent st m ≤ bound A (n + 1) st.a p c σ ∧
      (∀ x ∈ A.runtime.emitted st.a (n + 1),
        ∃ y ∈ st.seen ++ (machine A B).runtime.emitted st m, y.Covers x) ∧
      (A.runtime.Halts st.a (n + 1) → (machine A B).runtime.Halts st m) := by
  cases hr : (A.step st.a).val with
  | done =>
    rw [hr] at hv ht
    have hd : ((machine A B).step st).val = .done := hv
    have hd' : (machine A B).runtime.step st = .done := hd
    have hda : A.runtime.step st.a = .done := hr
    refine ⟨1, ?_, ?_, fun _ => ?_⟩
    · rw [(machine A B).spent_succ_done hd]
      have ht' : ((machine A B).step st).ticks ≤ 7 * (p + (A.step st.a).ticks) + 0 := ht
      simp only [bound, hr]
      generalize 14 * c * (p + (A.step st.a).ticks) = X
      generalize 2 * (A.step st.a).ticks * (σ + 2 * c * (p + (A.step st.a).ticks)) = Y
      omega
    · intro x hx
      unfold Runtime.emitted at hx
      rw [A.runtime.run_succ_done hda] at hx
      cases hx
    · unfold Runtime.Halts
      rw [(machine A B).runtime.run_succ_done hd']
  | emit as a' =>
    rw [hr] at hv ht
    obtain ⟨hav, hat⟩ := afterA_emit st as a'
    rw [hav] at hv
    rw [hat] at ht
    have he : ((machine A B).step st).val = .emit (outA st as) (stA st as a') := hv
    have he' : (machine A B).runtime.step st = .emit (outA st as) (stA st as a') := he
    have hea : A.runtime.step st.a = .emit as a' := hr
    have hf := afterA_ticks_le hinv (hA st.a as a' hr) hσ
    have hσ' : sizes (stA st as a').seenB ≤ σ + 2 * c * (p + (A.step st.a).ticks) :=
      le_trans hσ (Nat.le_add_right _ _)
    obtain ⟨m, hm, hcov, hh⟩ := ihn (2 * (p + 1 + (A.step a').ticks) + 1) (stA st as a') (p + 1)
      (σ + 2 * c * (p + (A.step st.a).ticks)) (inv_stA hinv as a') (fun hl => by
        have hl' : st.live = true := hl
        have := hp hl'
        have e1 : padB A B (stA st as a') = 0 := by simp [padB, stA]
        have e2 : padA A B (stA st as a') ≤ padA A B st + 1 := by
          simp only [padA, stA]
          cases st.last <;> simp
        have e3 : (stA st as a').a = a' := rfl
        rw [e1, e3]
        constructor <;> omega) hσ'
    refine ⟨m + 1, ?_, ?_, fun hn => ?_⟩
    · rw [(machine A B).spent_succ_emit he]
      have ht' : ((machine A B).step st).ticks ≤
          7 * (p + (A.step st.a).ticks) + (dropCovered st.seenB as).ticks := ht
      have hm' : (machine A B).spent (stA st as a') m ≤
          bound A n a' (p + 1) (2 * (p + 1 + (A.step a').ticks) + 1)
            (σ + 2 * c * (p + (A.step st.a).ticks)) := hm
      have hmul : 2 * (A.step st.a).ticks * σ ≤
          2 * (A.step st.a).ticks * (σ + 2 * c * (p + (A.step st.a).ticks)) :=
        Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
      simp only [bound, hr]
      generalize 14 * c * (p + (A.step st.a).ticks) = X
      generalize 2 * (A.step st.a).ticks * (σ + 2 * c * (p + (A.step st.a).ticks)) = Y at hmul ⊢
      omega
    · intro x hx
      unfold Runtime.emitted at hx ⊢
      rw [A.runtime.run_succ_emit hea] at hx
      rw [(machine A B).runtime.run_succ_emit he']
      rcases List.mem_append.1 hx with hx | hx
      · by_cases hk : (st.seenB.any fun t => t.covers? x) = true
        · obtain ⟨t, ht1, ht2⟩ := List.any_eq_true.1 hk
          exact ⟨t, List.mem_append_left _ (hinv.sub t ht1), (covers?_iff t x).1 ht2⟩
        · refine ⟨x, List.mem_append_right _ (List.mem_append_left _ ?_), Span.Covers.refl x⟩
          exact List.mem_filter.2 ⟨hx, by simpa using hk⟩
      · obtain ⟨y, hy, hyx⟩ := hcov x hx
        refine ⟨y, ?_, hyx⟩
        have e : (stA st as a').seen = st.seen ++ outA st as := rfl
        rw [e] at hy
        simpa [Runtime.emitted, List.append_assoc] using hy
    · unfold Runtime.Halts at hn ⊢
      rw [A.runtime.run_succ_emit hea] at hn
      rw [(machine A B).runtime.run_succ_emit he']
      exact hh hn

include hA in
/-- Each number of steps of `A`, with any number of races `B` may still win. -/
theorem follows : ∀ (n c : Nat) (st : State A.State B.State) (p σ : Nat), Follows n c st p σ := by
  intro n
  induction n with
  | zero =>
    intro c st p σ _ _ _
    refine ⟨0, Nat.le_refl _, ?_, ?_⟩
    · intro x hx; cases hx
    · intro h; cases h
  | succ n ihn =>
    intro c
    induction c with
    | zero =>
      intro st p σ hinv hl hσ
      by_cases hlive : st.live = true
      · obtain ⟨hp, hc⟩ := hl hlive
        rcases step_live hlive with ⟨hv, ht, -⟩ | ⟨hv, ht, hlt⟩
        · refine follows_take hA ihn hinv (fun _ => hp) hσ hv (le_trans ht ?_)
          omega
        · have := padB_le_sideB st
          omega
      · have hd : st.live = false := by simpa using hlive
        obtain ⟨hv, ht⟩ := step_dead hd
        exact follows_take hA ihn hinv (fun h => absurd h hlive) hσ hv (by omega)
    | succ c ihc =>
      intro st p σ hinv hl hσ
      by_cases hlive : st.live = true
      · obtain ⟨hp, hc⟩ := hl hlive
        rcases step_live hlive with ⟨hv, ht, -⟩ | ⟨hv, ht, hlt⟩
        · refine follows_take hA ihn hinv (fun _ => hp) hσ hv (le_trans ht ?_)
          omega
        · -- `B` won this race
          have hpb := padB_le_sideB st
          cases hres : resB st with
          | none =>
            rw [hres] at hv
            let st' : State A.State B.State := { st with live := false }
            have he : ((machine A B).step st).val = .emit [] st' := hv
            have he' : (machine A B).runtime.step st = .emit [] st' := he
            obtain ⟨m, hm, hcov, hh⟩ := ihc st' p (σ + 2 * (p + (A.step st.a).ticks))
              ⟨hinv.plain, hinv.sub⟩ (fun h => by cases h) (le_trans hσ (Nat.le_add_right _ _))
            refine ⟨m + 1, ?_, ?_, fun hn => ?_⟩
            · rw [(machine A B).spent_succ_emit he, bound_succ_c]
              have ht' : ((machine A B).step st).ticks ≤ 7 * (sideB A B st).ticks := ht
              have hm' : (machine A B).spent st' m ≤
                  bound A (n + 1) st.a p c (σ + 2 * (p + (A.step st.a).ticks)) := hm
              omega
            · intro x hx
              obtain ⟨y, hy, hyx⟩ := hcov x hx
              refine ⟨y, ?_, hyx⟩
              unfold Runtime.emitted
              rw [(machine A B).runtime.run_succ_emit he']
              simpa [Runtime.emitted] using hy
            · unfold Runtime.Halts
              rw [(machine A B).runtime.run_succ_emit he']
              exact hh hn
          | some r =>
            obtain ⟨out, b'⟩ := r
            rw [hres] at hv
            let st' : State A.State B.State :=
              { st with b := b', last := false, streak := if st.last then 1 else st.streak + 1,
                        seen := st.seen ++ out, seenB := st.seenB ++ out }
            have he : ((machine A B).step st).val = .emit out st' := hv
            have he' : (machine A B).runtime.step st = .emit out st' := he
            have hsz := resB_sizes hres
            have hpl := resB_plain hres
            have hinv' : Inv A B st' :=
              ⟨fun t ht => by
                rcases List.mem_append.1 ht with h | h
                · exact hinv.plain t h
                · exact hpl t h,
               fun t ht => by
                rcases List.mem_append.1 ht with h | h
                · exact List.mem_append_left _ (hinv.sub t h)
                · exact List.mem_append_right _ h⟩
            have hσ' : sizes st'.seenB ≤ σ + 2 * (p + (A.step st.a).ticks) := by
              have e : sizes st'.seenB = sizes st.seenB + sizes out := sizes_append _ _
              rw [e]
              omega
            obtain ⟨m, hm, hcov, hh⟩ := ihc st' p (σ + 2 * (p + (A.step st.a).ticks)) hinv'
              (fun _ => by
                have e1 : padA A B st' = 0 := by simp [padA, st']
                have e2 : padB A B st' = padB A B st + 1 := by
                  simp only [padB, st']
                  cases st.last <;> simp
                have e3 : st'.a = st.a := rfl
                rw [e1, e2, e3]
                constructor <;> omega) hσ'
            refine ⟨m + 1, ?_, ?_, fun hn => ?_⟩
            · rw [(machine A B).spent_succ_emit he, bound_succ_c]
              have ht' : ((machine A B).step st).ticks ≤ 7 * (sideB A B st).ticks := ht
              have hm' : (machine A B).spent st' m ≤
                  bound A (n + 1) st.a p c (σ + 2 * (p + (A.step st.a).ticks)) := hm
              omega
            · intro x hx
              obtain ⟨y, hy, hyx⟩ := hcov x hx
              refine ⟨y, ?_, hyx⟩
              unfold Runtime.emitted
              rw [(machine A B).runtime.run_succ_emit he']
              have e : st'.seen = st.seen ++ out := rfl
              rw [e] at hy
              simpa [Runtime.emitted, List.append_assoc] using hy
            · unfold Runtime.Halts
              rw [(machine A B).runtime.run_succ_emit he']
              exact hh hn
      · have hd : st.live = false := by simpa using hlive
        obtain ⟨hv, ht⟩ := step_dead hd
        exact follows_take hA ihn hinv (fun h => absurd h hlive) hσ hv (by omega)

end Hedge

end RwLog
