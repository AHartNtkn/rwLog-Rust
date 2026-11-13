/-
# R003 is admitted

The simulation and the separation, with the bounds brought to the form the
admission statement asks for (`Improves`, `Trusted/Cost.lean`): a coefficient
and a degree for each polynomial.
-/
import RwLog.Rungs.R003.Proofs.Same
import RwLog.Rungs.R003.Proofs.Separation.Run

namespace RwLog

namespace R003

theorem improves : Obligation.improves where
  simulates := by
    refine simulates.mono fun c n => ?_
    show 7 * c ≤ 7 * (c + n + 1) ^ 1
    rw [Nat.pow_one]; omega
  separates := by
    refine separates.mono (fun k => ?_) fun k => ?_
    · show 8 * k + 7 ≤ 8 * (k + 1) ^ 1
      rw [Nat.pow_one]; omega
    · show 2000 * (k + 2) ^ 3 ≤ 16000 * (k + 1) ^ 3
      have h : (k + 2) ^ 3 ≤ (2 * (k + 1)) ^ 3 := Nat.pow_le_pow_left (by omega) 3
      calc 2000 * (k + 2) ^ 3 ≤ 2000 * (2 * (k + 1)) ^ 3 := Nat.mul_le_mul_left 2000 h
        _ = 16000 * (k + 1) ^ 3 := by ring

end R003

end RwLog
