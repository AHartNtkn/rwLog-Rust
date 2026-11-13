/-
# R002 advances

The simulation and the separation, with the bounds brought to the form the
statement of the advance asks for (`Improves`, `Trusted/Cost.lean`): a coefficient
and a degree for each polynomial.
-/
import RwLog.Rungs.R002.Proofs.Simulates
import RwLog.Rungs.R002.Proofs.Separation.Run
import RwLog.Rungs.R001.Proofs.Keeps
import RwLog.Rungs.R002.Reading

namespace RwLog

namespace R002

theorem improves : Obligation.improves where
  simulates := by
    refine simulates.mono fun c n => ?_
    show 5 * c ^ 3 * (n + 2) ^ 3 ≤ 40 * (c + n + 1) ^ 6
    have h1 : c ^ 3 ≤ (c + n + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have h2 : (n + 2) ^ 3 ≤ (2 * (c + n + 1)) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    calc 5 * c ^ 3 * (n + 2) ^ 3
        ≤ 5 * (c + n + 1) ^ 3 * (2 * (c + n + 1)) ^ 3 :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 5 h1) h2
      _ = 40 * (c + n + 1) ^ 6 := by ring
  separates := by
    refine separates.mono (fun k => ?_) fun k => ?_
    · show 2 * k + 11 ≤ 11 * (k + 1) ^ 1
      rw [Nat.pow_one]; omega
    · show 500 * (k + 5) ^ 4 ≤ 312500 * (k + 1) ^ 4
      have h : (k + 5) ^ 4 ≤ (5 * (k + 1)) ^ 4 := Nat.pow_le_pow_left (by omega) 4
      calc 500 * (k + 5) ^ 4 ≤ 500 * (5 * (k + 1)) ^ 4 := Nat.mul_le_mul_left 500 h
        _ = 312500 * (k + 1) ^ 4 := by ring

theorem keeps : Obligation.keeps := by
  have h : runtime = R001.runtime := runtime_eq
  unfold Obligation.keeps
  rw [h]
  exact R001.keeps

theorem baseline_engine : Obligation.baseline_engine := baselineEngine_std

theorem costed_engine : Obligation.costed_engine := engine_std

theorem advances : Obligation.advances :=
  Advances.of_id (by rw [baselineEngine_std, engine_std]; exact improves)

end R002

end RwLog
