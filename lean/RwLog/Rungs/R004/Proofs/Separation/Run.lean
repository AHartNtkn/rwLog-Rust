/-
# R004 is separated from R003

On `sepFam k`, R004's first round emits `a -> a` within `1000 (k + 2)` ticks
(`costed_first`), and R003 has emitted nothing before the end of its first
round, which costs at least `2 ^ k` (`Sep.r003_first`).
-/
import RwLog.Rungs.R004.Proofs.Separation.Lower
import RwLog.Rungs.R004.Proofs.Separation.Upper
import RwLog.Rungs.Framework.Latency

namespace RwLog

namespace R004

namespace Sep

open Cost R001

/-- R004's first round emits `a -> a`, within `1000 (k + 2)` ticks. -/
theorem costed_first (k : Nat) :
    (∃ s', (costed.step (st0 k)).val = .emit [aa] s') ∧
      (costed.step (st0 k)).ticks ≤ 1000 * (k + 2) := by
  obtain ⟨hv, ht⟩ := round_st0 k
  obtain ⟨sv, st⟩ := R003.Sep.step_emit (U := unfolder) (st := st0 k) rfl
  rw [hv] at sv
  refine ⟨⟨_, sv⟩, ?_⟩
  have e : (costed.step (st0 k)).ticks = _ := st
  rw [e]
  exact ht

end Sep

/-- On `sepFam k`, R004 has covered `(a, a)` within `1000 (k + 2)` ticks, and
R003 has paid at least `2 ^ k` at any step at which it has covered it. -/
theorem separates : Obligation.separates := by
  intro k
  refine ⟨Sep.wellFormed k, Sep.size_le k, ⟨∅, Sep.model_nil k⟩, ⟨(.sym "a", .sym "a"), rfl⟩, ?_⟩
  intro M _ x hx
  have hx' : x = (.sym "a", .sym "a") := hx
  subst hx'
  refine ⟨?_, ?_⟩
  · obtain ⟨⟨s', hs⟩, ht⟩ := Sep.costed_first k
    have hi : costed.start (sepFam k).1 (sepFam k).2 = Sep.st0 k := Sep.init_eq k unfolder
    refine ⟨1, ⟨Sep.aa, ?_, ⟨fun _ => .sym "", rfl, rfl, by simp⟩⟩, ?_⟩
    · rw [hi]
      have r1 : costed.runtime.step (Sep.st0 k) = .emit [Sep.aa] s' := hs
      show Sep.aa ∈ (costed.runtime.run (Sep.st0 k) 1).1
      rw [costed.runtime.run_succ_emit r1]
      simp
    · have h0 : costed.spent s' 0 = 0 := rfl
      have hp : costed.paid (sepFam k).1 (sepFam k).2 1 =
          costed.spent (costed.start (sepFam k).1 (sepFam k).2) 1 := Tabled.paid_eq unfolder _ _ 1
      rw [hp, hi, costed.spent_succ_emit hs, h0, Nat.add_zero]
      exact ht
  · rintro n ⟨a, ha, -⟩
    have hi : R003.costed.start (sepFam k).1 (sepFam k).2 = Sep.st0 k :=
      Sep.init_eq k R003.unfolder
    have hp : R003.costed.paid (sepFam k).1 (sepFam k).2 n =
        R003.costed.spent (R003.costed.start (sepFam k).1 (sepFam k).2) n :=
      Tabled.paid_eq R003.unfolder _ _ n
    rw [hp]
    rw [hi] at ha ⊢
    exact R003.costed.le_spent_of_covered (N := 0) rfl
      (le_trans (Sep.r003_first k) (R003.Sep.spent_ge_step _ _ 0)) ha

end R004

end RwLog
