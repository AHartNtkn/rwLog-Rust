/-
# The hedge follows its second machine within a polynomial

`Hedge.boundB` is at most `Hedge.capB n W`, for `n` steps of `B` whose sides
of the races cost `W` (`boundB_le`), and so the hedge has paid at most that,
and what the two machines pay to start, by the time it has taken `n` steps of
`B` or halted (`follows_second`).
-/
import RwLog.Rungs.Hedge.Second

namespace RwLog

open Cost

namespace Hedge

/-- What following `n` steps of the second machine may cost, when its sides
of the races cost `W`. With `Q = n + W` and `C = 2 Q + 1` (how many races the
first machine can win before a step), the sizes of the answers emitted stay
below `M = n (2 C Q + Q)`. -/
def capB (n W : Nat) : Nat :=
  n * ((2 * (n + W) + 1) * (7 * (n + W) + 4 * (n + W) *
        (n * (2 * (2 * (n + W) + 1) * (n + W) + (n + W)))) + 7 * (n + W) +
      2 * (n + W) * (n * (2 * (2 * (n + W) + 1) * (n + W) + (n + W))) +
      6 * (n + W) * (n + W))

theorem capB_mono {n W W' : Nat} (h : W ≤ W') : capB n W ≤ capB n W' := by
  unfold capB
  gcongr

theorem boundB_le (B : CostedRuntime) (Q M : Nat) : ∀ (n : Nat) (b : B.State) (p S : Nat),
    p + n + spentB B b n ≤ Q → S + n * (2 * (2 * Q + 1) * Q + Q) ≤ M →
    boundB B n b p (2 * (p + costB B b) + 1) S ≤
      n * ((2 * Q + 1) * (7 * Q + 4 * Q * M) + 7 * Q + 2 * Q * M + 6 * Q * Q)
  | 0, _, _, _, _, _ => Nat.zero_le _
  | n + 1, b, p, S, hQ, hM => by
    have ho : costB B b ≤ spentB B b (n + 1) := by
      simp only [spentB]; omega
    have hq : p + costB B b ≤ Q := by omega
    have hc : 2 * (p + costB B b) + 1 ≤ 2 * Q + 1 := by omega
    have hcq : 2 * (2 * (p + costB B b) + 1) * (p + costB B b) ≤ 2 * (2 * Q + 1) * Q := by
      gcongr
    have hn : (n + 1) * (2 * (2 * Q + 1) * Q + Q) =
        n * (2 * (2 * Q + 1) * Q + Q) + (2 * (2 * Q + 1) * Q + Q) := by ring
    have hSc : S + 2 * (2 * (p + costB B b) + 1) * (p + costB B b) ≤ M := by omega
    have h1 : (2 * (p + costB B b) + 1) * (7 * (p + costB B b) + 4 * (p + costB B b) *
          (S + 2 * (2 * (p + costB B b) + 1) * (p + costB B b))) ≤
        (2 * Q + 1) * (7 * Q + 4 * Q * M) := by
      gcongr
    have h2 : 2 * (p + costB B b) * (S + 2 * (2 * (p + costB B b) + 1) * (p + costB B b)) ≤
        2 * Q * M := by
      gcongr
    have h3 : 6 * (p + costB B b) * (p + costB B b) ≤ 6 * Q * Q := by
      gcongr
    have e : (n + 1) * ((2 * Q + 1) * (7 * Q + 4 * Q * M) + 7 * Q + 2 * Q * M + 6 * Q * Q) =
        (2 * Q + 1) * (7 * Q + 4 * Q * M) + 7 * Q + 2 * Q * M + 6 * Q * Q +
          n * ((2 * Q + 1) * (7 * Q + 4 * Q * M) + 7 * Q + 2 * Q * M + 6 * Q * Q) := by ring
    cases hr : (B.step b).val with
    | done =>
      simp only [boundB, hr]
      rw [e]
      omega
    | emit bs b' =>
      have hs : spentB B b (n + 1) = costB B b + spentB B b' n := by
        simp only [spentB, hr]
      have ih := boundB_le B Q M n b' (p + 1)
        (S + 2 * (2 * (p + costB B b) + 1) * (p + costB B b) + (p + costB B b))
        (by omega) (by omega)
      simp only [boundB, hr]
      rw [e]
      omega

variable {A B : CostedRuntime}

/-- The hedge follows its second machine: for every number of steps of `B`
there is a number of steps of the hedge by which it has paid at most what the
two machines pay to start and `capB` of what `B`'s sides of the races cost;
and by then it has halted, or has emitted an answer covering each plain
answer of `B`. -/
theorem follows_second (hA : ∀ (s : A.State) (as : List Span) (s' : A.State),
      (A.step s).val = .emit as s' → sizes as ≤ (A.step s).ticks)
    (hB : ∀ (s : B.State) (bs : List Span) (s' : B.State),
      (B.step s).val = .emit bs s' → sizes bs ≤ (B.step s).ticks)
    (P : Program) (q : Rel) (n : Nat) :
    ∃ m, (machine A B).paid P q m ≤
        (A.init P q).ticks + (B.init P q).ticks + capB n (spentB B (B.start P q) n) ∧
      ((machine A B).runtime.Halts ((machine A B).start P q) m ∨
        ∀ x ∈ B.runtime.emitted (B.start P q) n, (plain x).val = true →
          ∃ y ∈ (machine A B).runtime.emitted ((machine A B).start P q) m, y.Covers x) := by
  let st0 : State A.State B.State := ⟨A.start P q, B.start P q, true, true, 0, [], []⟩
  have hst : (machine A B).start P q = st0 := rfl
  have hin : ((machine A B).init P q).ticks = (A.init P q).ticks + (B.init P q).ticks := by
    show (init A B P q).ticks = _
    simp [init]
  obtain ⟨m, hm, hres⟩ := followsB hB hA n (2 * (0 + costB B st0.b) + 1) st0 0 0
    (Inv.mk (fun t ht => nomatch ht) (fun t ht => nomatch ht) (Nat.le_refl _))
    rfl (Nat.le_refl _) (Nat.le_add_right _ _) (Nat.le_refl _)
  refine ⟨m, ?_, ?_⟩
  · have hb := boundB_le B (n + spentB B (B.start P q) n)
      (n * (2 * (2 * (n + spentB B (B.start P q) n) + 1) * (n + spentB B (B.start P q) n) +
        (n + spentB B (B.start P q) n))) n (B.start P q) 0 0 (by omega) (by omega)
    have hm' : (machine A B).spent st0 m ≤
        boundB B n (B.start P q) 0 (2 * (0 + costB B (B.start P q)) + 1) 0 := hm
    show ((machine A B).init P q).ticks + (machine A B).spent ((machine A B).start P q) m ≤ _
    rw [hin, hst]
    unfold capB
    omega
  · rcases hres with hh | hcov
    · exact .inl hh
    · refine .inr fun x hx hxp => ?_
      obtain ⟨y, hy, hyx⟩ := hcov x hx hxp
      have hy' : y ∈ ([] : List Span) ++ (machine A B).runtime.emitted st0 m := hy
      exact ⟨y, by simpa [hst] using hy', hyx⟩

end Hedge

end RwLog
