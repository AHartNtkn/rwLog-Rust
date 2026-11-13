/-
# The hedge follows its first machine within a polynomial

`Hedge.bound` is at most `Hedge.cap n T`, for `n` steps of `A` that cost `T`
(`bound_le`), and so the hedge has paid at most that, and what the two
machines pay to start, by the time it has taken `n` steps of `A`
(`follows_first`).
-/
import RwLog.Rungs.Hedge.First

namespace RwLog

open Cost

namespace Hedge

/-- What following `n` steps that cost `T` may cost. With `Q = n + T` and
`C = 2 Q + 1` (how many races the other machine can win before a step), the
sizes of the answers emitted stay below `M = n C Q + T`; each step is at most
`C` races and entries of answers and one race of its own, and comparing its
answers costs `2 M` for each tick it spent. -/
def cap (n T : Nat) : Nat :=
  n * ((2 * (n + T) + 1) * (7 * (n + T) + 6 * (n + T) * (n + T) +
      2 * (n + T) * (n * (2 * (n + T) + 1) * (n + T) + T)) + 7 * (n + T)) +
    2 * T * (n * (2 * (n + T) + 1) * (n + T) + T)

theorem cap_mono {n T T' : Nat} (h : T ≤ T') : cap n T ≤ cap n T' := by
  unfold cap
  gcongr

theorem bound_le (A : CostedRuntime) (Q M : Nat) : ∀ (n : Nat) (a : A.State) (p S : Nat),
    p + n + A.spent a n ≤ Q → S + n * ((2 * Q + 1) * Q) + A.spent a n ≤ M →
    bound A n a p (2 * (p + (A.step a).ticks) + 1) S ≤
      n * ((2 * Q + 1) * (7 * Q + 6 * Q * Q + 2 * Q * M) + 7 * Q) + 2 * A.spent a n * M
  | 0, _, _, _, _, _ => Nat.zero_le _
  | n + 1, a, p, S, hQ, hM => by
    have ho : (A.step a).ticks ≤ A.spent a (n + 1) := by
      cases hr : (A.step a).val with
      | done => rw [A.spent_succ_done hr]
      | emit as a' => rw [A.spent_succ_emit hr]; omega
    have hq : p + (A.step a).ticks ≤ Q := by omega
    have hc : 2 * (p + (A.step a).ticks) + 1 ≤ 2 * Q + 1 := by omega
    have hcq : (2 * (p + (A.step a).ticks) + 1) * (p + (A.step a).ticks) ≤ (2 * Q + 1) * Q :=
      Nat.mul_le_mul hc hq
    have hn : (n + 1) * ((2 * Q + 1) * Q) = n * ((2 * Q + 1) * Q) + (2 * Q + 1) * Q := by ring
    have hSc : S + (2 * (p + (A.step a).ticks) + 1) * (p + (A.step a).ticks) ≤ M := by omega
    have h1 : (2 * (p + (A.step a).ticks) + 1) *
        (7 * (p + (A.step a).ticks) + 6 * (p + (A.step a).ticks) * (p + (A.step a).ticks) +
          2 * (p + (A.step a).ticks) *
            (S + (2 * (p + (A.step a).ticks) + 1) * (p + (A.step a).ticks))) ≤
        (2 * Q + 1) * (7 * Q + 6 * Q * Q + 2 * Q * M) := by
      gcongr
    have h3 : 2 * (A.step a).ticks *
        (S + (2 * (p + (A.step a).ticks) + 1) * (p + (A.step a).ticks)) ≤
        2 * (A.step a).ticks * M := Nat.mul_le_mul_left _ hSc
    cases hr : (A.step a).val with
    | done =>
      rw [A.spent_succ_done hr]
      simp only [bound, hr]
      have e : (n + 1) * ((2 * Q + 1) * (7 * Q + 6 * Q * Q + 2 * Q * M) + 7 * Q) =
          (2 * Q + 1) * (7 * Q + 6 * Q * Q + 2 * Q * M) + 7 * Q +
            n * ((2 * Q + 1) * (7 * Q + 6 * Q * Q + 2 * Q * M) + 7 * Q) := by ring
      rw [e]
      omega
    | emit as a' =>
      have hs := A.spent_succ_emit hr n
      have ih := bound_le A Q M n a' (p + 1)
        (S + (2 * (p + (A.step a).ticks) + 1) * (p + (A.step a).ticks) + (A.step a).ticks)
        (by omega) (by omega)
      rw [hs]
      simp only [bound, hr]
      linarith

variable {A B : CostedRuntime}

/-- The hedge follows its first machine: for every number of steps of `A`
there is a number of steps of the hedge by which it has paid at most what `A`
paid, what `B` paid to start, and `cap`; has emitted an answer covering each
answer of `A`; and has halted if `A` has. -/
theorem follows_first (hA : ∀ (s : A.State) (as : List Span) (s' : A.State),
      (A.step s).val = .emit as s' → sizes as ≤ (A.step s).ticks)
    (hB : ∀ (s : B.State) (bs : List Span) (s' : B.State),
      (B.step s).val = .emit bs s' → sizes bs ≤ (B.step s).ticks)
    (P : Program) (q : Rel) (n : Nat) :
    ∃ m, (machine A B).paid P q m ≤ A.paid P q n + (B.init P q).ticks + cap n (A.paid P q n) ∧
      (∀ x ∈ A.runtime.emitted (A.start P q) n,
        ∃ y ∈ (machine A B).runtime.emitted ((machine A B).start P q) m, y.Covers x) ∧
      (A.runtime.Halts (A.start P q) n →
        (machine A B).runtime.Halts ((machine A B).start P q) m) := by
  let st0 : State A.State B.State := ⟨A.start P q, B.start P q, true, true, 0, [], []⟩
  have hst : (machine A B).start P q = st0 := rfl
  have hin : ((machine A B).init P q).ticks = (A.init P q).ticks + (B.init P q).ticks := by
    show (init A B P q).ticks = _
    simp [init]
  obtain ⟨m, hm, hcov, hh⟩ := follows hA hB n (2 * (0 + (A.step st0.a).ticks) + 1) st0 0 0
    (Inv.mk (fun t ht => nomatch ht) (fun t ht => nomatch ht) (Nat.le_refl _))
    (fun _ => ⟨Nat.le_refl _, Nat.le_refl _⟩) (Nat.le_refl _)
  refine ⟨m, ?_, ?_, ?_⟩
  · have hb := bound_le A (n + A.spent (A.start P q) n)
      (n * ((2 * (n + A.spent (A.start P q) n) + 1) * (n + A.spent (A.start P q) n)) +
        A.spent (A.start P q) n) n (A.start P q) 0 0 (by omega) (by omega)
    have hm' : (machine A B).spent st0 m ≤
        bound A n (A.start P q) 0 (2 * (0 + (A.step (A.start P q)).ticks) + 1) 0 := hm
    have hT : A.spent (A.start P q) n ≤ A.paid P q n := Nat.le_add_left _ _
    have hcap : n * ((2 * (n + A.spent (A.start P q) n) + 1) *
          (7 * (n + A.spent (A.start P q) n) +
            6 * (n + A.spent (A.start P q) n) * (n + A.spent (A.start P q) n) +
            2 * (n + A.spent (A.start P q) n) *
              (n * ((2 * (n + A.spent (A.start P q) n) + 1) * (n + A.spent (A.start P q) n)) +
                A.spent (A.start P q) n)) + 7 * (n + A.spent (A.start P q) n)) +
        2 * A.spent (A.start P q) n *
          (n * ((2 * (n + A.spent (A.start P q) n) + 1) * (n + A.spent (A.start P q) n)) +
            A.spent (A.start P q) n) = cap n (A.spent (A.start P q) n) := by
      unfold cap; ring
    have hmono := cap_mono (n := n) hT
    show ((machine A B).init P q).ticks + (machine A B).spent ((machine A B).start P q) m ≤ _
    rw [hin, hst]
    unfold CostedRuntime.paid at hmono ⊢
    omega
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := hcov x hx
    have hy' : y ∈ ([] : List Span) ++ (machine A B).runtime.emitted st0 m := hy
    exact ⟨y, by simpa [hst] using hy', hyx⟩
  · exact fun h => hh h

end Hedge

end RwLog
