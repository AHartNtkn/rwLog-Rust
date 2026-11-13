/-
# R002 is admitted

The simulation and the separation, with the bounds brought to the form the
admission statement asks for (`Improves`, `Trusted/Cost.lean`): a coefficient
and a degree for each polynomial.
-/
import RwLog.Rungs.R002.Proofs.Simulates
import RwLog.Rungs.R002.Proofs.Separation.Run

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

theorem admits : Obligation.admits := Admits.of_id improves

end R002

end RwLog
