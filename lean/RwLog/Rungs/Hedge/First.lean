/-
# The hedge is never much slower than its first machine

Whatever `B` does, `Hedge.machine A B` has taken `n` steps of `A` after
spending at most `Hedge.bound`, a polynomial in what `A` spends on those
steps (`bound_le`), and by then it has emitted an answer covering each answer
of `A`, and has halted if `A` has (`follows_first`).

Why it is bounded. While `A`'s next step costs `o` and `A` carries the
handicap `p`, `B` can only win a race it finishes in less than `q = p + o`,
and each win raises `B`'s own handicap by one: after at most `2 q + 1` wins
`A` wins. Each of those races costs at most 7 times `B`'s side, so less than
`7 q`. The answers `B` hands over are no larger than what its step cost, so
less than `q`, and entering them costs their sizes times the sizes of what was
emitted before.
-/
import RwLog.Rungs.Hedge.Steps
import RwLog.Rungs.Framework.Runtime
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace RwLog

open Cost

namespace Hedge

variable (A B : CostedRuntime)

/-- What the hedge may spend to take `n` steps of `A` from the state `a`,
when `A` carries the handicap `p`, `B` can win at most `c` more races before
`A`'s next step, and the answers emitted so far have sizes adding up to
`S`. -/
def bound : Nat → A.State → Nat → Nat → Nat → Nat
  | 0, _, _, _, _ => 0
  | n + 1, a, p, c, S =>
    c * (7 * (p + (A.step a).ticks) + 6 * (p + (A.step a).ticks) * (p + (A.step a).ticks) +
        2 * (p + (A.step a).ticks) * (S + c * (p + (A.step a).ticks))) +
      7 * (p + (A.step a).ticks) +
      2 * (A.step a).ticks * (S + c * (p + (A.step a).ticks)) +
      match (A.step a).val with
      | .emit _ a' => bound n a' (p + 1) (2 * (p + 1 + (A.step a').ticks) + 1)
          (S + c * (p + (A.step a).ticks) + (A.step a).ticks)
      | .done => 0

/-- One more race for `B` to win costs one race, entering its answers, and
what it adds to the sizes. -/
theorem bound_succ_c (n : Nat) (a : A.State) (p c S : Nat) :
    7 * (p + (A.step a).ticks) + 6 * (p + (A.step a).ticks) * (p + (A.step a).ticks) +
        2 * (p + (A.step a).ticks) * S +
        bound A (n + 1) a p c (S + (p + (A.step a).ticks)) ≤
      bound A (n + 1) a p (c + 1) S := by
  have e : S + (p + (A.step a).ticks) + c * (p + (A.step a).ticks) =
      S + (c + 1) * (p + (A.step a).ticks) := by ring
  have h : 2 * (p + (A.step a).ticks) * S ≤
      2 * (p + (A.step a).ticks) * (S + (c + 1) * (p + (A.step a).ticks)) :=
    Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
  simp only [bound, e]
  linarith

variable {A B}

/-- The claim, for one state: `n` steps of `A` are taken within the bound. -/
def Follows (n c : Nat) (st : State A.State B.State) (p S : Nat) : Prop :=
  Inv A B st →
  (st.live = true → padA A B st ≤ p ∧
    2 * (padA A B st + (A.step st.a).ticks) + 1 ≤ c + padB A B st) →
  sizes st.seen ≤ S →
  ∃ m, (machine A B).spent st m ≤ bound A n st.a p c S ∧
    (∀ x ∈ A.runtime.emitted st.a n,
      ∃ y ∈ st.seen ++ (machine A B).runtime.emitted st m, y.Covers x) ∧
    (A.runtime.Halts st.a n → (machine A B).runtime.Halts st m)

variable (hA : ∀ (s : A.State) (as : List Span) (s' : A.State),
  (A.step s).val = .emit as s' → sizes as ≤ (A.step s).ticks)

include hA in
/-- A step of the hedge that is a step of `A`. -/
theorem follows_take {n : Nat} (ihn : ∀ c (st : State A.State B.State) p S, Follows n c st p S)
    {c : Nat} {st : State A.State B.State} {p S : Nat} (hinv : Inv A B st)
    (hp : st.live = true → padA A B st ≤ p) (hS : sizes st.seen ≤ S)
    (hv : (step A B st).val = (afterA A B st (A.step st.a).val).val)
    (ht : (step A B st).ticks ≤ 7 * (p + (A.step st.a).ticks) +
      (afterA A B st (A.step st.a).val).ticks) :
    ∃ m, (machine A B).spent st m ≤ bound A (n + 1) st.a p c S ∧
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
    have hsz := hA st.a as a' hr
    have hf := afterA_ticks_le hinv hsz hS
    have hS' : sizes (stA st as a').seen ≤
        S + c * (p + (A.step st.a).ticks) + (A.step st.a).ticks := by
      have := sizes_stA st as a'
      omega
    obtain ⟨m, hm, hcov, hh⟩ := ihn (2 * (p + 1 + (A.step a').ticks) + 1) (stA st as a') (p + 1)
      (S + c * (p + (A.step st.a).ticks) + (A.step st.a).ticks) (inv_stA hinv as a') (fun hl => by
        have hl' : st.live = true := hl
        have := hp hl'
        have e1 : padB A B (stA st as a') = 0 := by simp [padB, stA]
        have e2 : padA A B (stA st as a') ≤ padA A B st + 1 := by
          simp only [padA, stA]
          cases st.last <;> simp
        have e3 : (stA st as a').a = a' := rfl
        rw [e1, e3]
        constructor <;> omega) hS'
    refine ⟨m + 1, ?_, ?_, fun hn => ?_⟩
    · rw [(machine A B).spent_succ_emit he]
      have ht' : ((machine A B).step st).ticks ≤
          7 * (p + (A.step st.a).ticks) + (dropCovered st.seenB as).ticks := ht
      have hm' : (machine A B).spent (stA st as a') m ≤
          bound A n a' (p + 1) (2 * (p + 1 + (A.step a').ticks) + 1)
            (S + c * (p + (A.step st.a).ticks) + (A.step st.a).ticks) := hm
      have hmul : 2 * (A.step st.a).ticks * S ≤
          2 * (A.step st.a).ticks * (S + c * (p + (A.step st.a).ticks)) :=
        Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
      simp only [bound, hr]
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

variable (hB : ∀ (s : B.State) (bs : List Span) (s' : B.State),
  (B.step s).val = .emit bs s' → sizes bs ≤ (B.step s).ticks)

include hB in
/-- A step of the hedge that is a step of `B`, which `B` won. -/
theorem follows_lose {n c : Nat}
    (ihc : ∀ (st : State A.State B.State) p S, Follows (n + 1) c st p S)
    {st : State A.State B.State} {p S : Nat} (hinv : Inv A B st)
    (hp : padA A B st ≤ p)
    (hc : 2 * (padA A B st + (A.step st.a).ticks) + 1 ≤ c + 1 + padB A B st)
    (hS : sizes st.seen ≤ S)
    (hv : (step A B st).val = (afterB A B st (resB st)).val)
    (ht : (step A B st).ticks ≤ 7 * (sideB A B st).ticks + (afterB A B st (resB st)).ticks)
    (hlt : (sideB A B st).ticks < padA A B st + (A.step st.a).ticks) :
    ∃ m, (machine A B).spent st m ≤ bound A (n + 1) st.a p (c + 1) S ∧
      (∀ x ∈ A.runtime.emitted st.a (n + 1),
        ∃ y ∈ st.seen ++ (machine A B).runtime.emitted st m, y.Covers x) ∧
      (A.runtime.Halts st.a (n + 1) → (machine A B).runtime.Halts st m) := by
  have hb := bound_succ_c A n st.a p c S
  have hq : (sideB A B st).ticks ≤ p + (A.step st.a).ticks := by omega
  cases hres : resB st with
  | none =>
    rw [hres] at hv ht
    let st' : State A.State B.State := { st with live := false }
    have he : ((machine A B).step st).val = .emit [] st' := hv
    have he' : (machine A B).runtime.step st = .emit [] st' := he
    obtain ⟨m, hm, hcov, hh⟩ := ihc st' p (S + (p + (A.step st.a).ticks))
      ⟨hinv.plain, hinv.sub, hinv.le⟩ (fun h => by cases h) (le_trans hS (Nat.le_add_right _ _))
    refine ⟨m + 1, ?_, ?_, fun hn => ?_⟩
    · rw [(machine A B).spent_succ_emit he]
      have ht' : ((machine A B).step st).ticks ≤ 7 * (sideB A B st).ticks + 0 := ht
      have hm' : (machine A B).spent st' m ≤
          bound A (n + 1) st.a p c (S + (p + (A.step st.a).ticks)) := hm
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
    obtain ⟨ps, b'⟩ := r
    rw [hres] at hv ht
    obtain ⟨hbv, hbt⟩ := afterB_some st ps b'
    rw [hbv] at hv
    rw [hbt] at ht
    have he : ((machine A B).step st).val = .emit (outB st ps) (stB st ps b') := hv
    have he' : (machine A B).runtime.step st = .emit (outB st ps) (stB st ps b') := he
    have hsz := resB_sizes hB hres
    have hpl := resB_plain hres
    have hπ : sizes ps ≤ p + (A.step st.a).ticks := le_trans hsz hq
    have hf := afterB_ticks_le st hpl hπ hS
    have hS' : sizes (stB st ps b').seen ≤ S + (p + (A.step st.a).ticks) := by
      have := sizes_stB st ps b'
      omega
    obtain ⟨m, hm, hcov, hh⟩ := ihc (stB st ps b') p (S + (p + (A.step st.a).ticks))
      (inv_stB hinv hpl b') (fun _ => by
        have e1 : padA A B (stB st ps b') = 0 := by simp [padA, stB]
        have e2 : padB A B (stB st ps b') = padB A B st + 1 := by
          simp only [padB, stB]
          cases st.last <;> simp
        have e3 : (stB st ps b').a = st.a := rfl
        rw [e1, e2, e3]
        constructor <;> omega) hS'
    refine ⟨m + 1, ?_, ?_, fun hn => ?_⟩
    · rw [(machine A B).spent_succ_emit he]
      have ht' : ((machine A B).step st).ticks ≤
          7 * (sideB A B st).ticks + (Tabled.fresh st.seen ps).ticks := ht
      have hm' : (machine A B).spent (stB st ps b') m ≤
          bound A (n + 1) st.a p c (S + (p + (A.step st.a).ticks)) := hm
      omega
    · intro x hx
      obtain ⟨y, hy, hyx⟩ := hcov x hx
      refine ⟨y, ?_, hyx⟩
      unfold Runtime.emitted
      rw [(machine A B).runtime.run_succ_emit he']
      have e : (stB st ps b').seen = st.seen ++ outB st ps := rfl
      rw [e] at hy
      simpa [Runtime.emitted, List.append_assoc] using hy
    · unfold Runtime.Halts
      rw [(machine A B).runtime.run_succ_emit he']
      exact hh hn

include hA hB in
/-- Each number of steps of `A`, with any number of races `B` may still win. -/
theorem follows : ∀ (n c : Nat) (st : State A.State B.State) (p S : Nat), Follows n c st p S := by
  intro n
  induction n with
  | zero =>
    intro c st p S _ _ _
    refine ⟨0, Nat.le_refl _, ?_, ?_⟩
    · intro x hx; cases hx
    · intro h; cases h
  | succ n ihn =>
    intro c
    induction c with
    | zero =>
      intro st p S hinv hl hS
      by_cases hlive : st.live = true
      · obtain ⟨hp, hc⟩ := hl hlive
        rcases step_live hlive with ⟨hv, ht, -, -⟩ | ⟨hv, ht, hlt⟩
        · refine follows_take hA ihn hinv (fun _ => hp) hS hv (le_trans ht ?_)
          omega
        · have := padB_le_sideB st
          omega
      · have hd : st.live = false := by simpa using hlive
        obtain ⟨hv, ht⟩ := step_dead hd
        exact follows_take hA ihn hinv (fun h => absurd h hlive) hS hv (by omega)
    | succ c ihc =>
      intro st p S hinv hl hS
      by_cases hlive : st.live = true
      · obtain ⟨hp, hc⟩ := hl hlive
        rcases step_live hlive with ⟨hv, ht, -, -⟩ | ⟨hv, ht, hlt⟩
        · refine follows_take hA ihn hinv (fun _ => hp) hS hv (le_trans ht ?_)
          omega
        · exact follows_lose hB ihc hinv hp hc hS hv ht hlt
      · have hd : st.live = false := by simpa using hlive
        obtain ⟨hv, ht⟩ := step_dead hd
        exact follows_take hA ihn hinv (fun h => absurd h hlive) hS hv (by omega)

end Hedge

end RwLog
