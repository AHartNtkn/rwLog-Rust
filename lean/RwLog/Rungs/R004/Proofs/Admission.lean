/-
# R004 is admitted

The simulation and the separation, with the bounds brought to the form the
admission statement asks for (`Improves`, `Trusted/Cost.lean`): a coefficient
and a degree for each polynomial.
-/
import RwLog.Rungs.R004.Proofs.SameMachine
import RwLog.Rungs.R004.Proofs.Separation.Run
import RwLog.Rungs.R001.Proofs.Keeps

namespace RwLog

namespace R004

theorem improves : Obligation.improves where
  simulates := by
    refine simulates.mono fun c n => ?_
    show 7 * c ≤ 7 * (c + n + 1) ^ 1
    rw [Nat.pow_one]; omega
  separates := by
    refine separates.mono (fun k => ?_) fun k => ?_
    · show 12 * (k + 2) ≤ 24 * (k + 1) ^ 1
      rw [Nat.pow_one]; omega
    · show 1000 * (k + 2) ≤ 2000 * (k + 1) ^ 1
      rw [Nat.pow_one]; omega

theorem keeps : Obligation.keeps := by
  have h : runtime = R001.runtime := runtime_eq
  unfold Obligation.keeps
  rw [h]
  exact R001.keeps

theorem admits : Obligation.admits := Admits.of_id improves

end R004

end RwLog
