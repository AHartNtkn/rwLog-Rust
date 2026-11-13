/-
# R004 advances

The simulation and the separation, with the bounds brought to the form the
statement of the advance asks for (`Improves`, `Trusted/Cost.lean`): a coefficient
and a degree for each polynomial.
-/
import RwLog.Rungs.R004.Proofs.SameMachine
import RwLog.Rungs.R004.Proofs.Separation.Run
import RwLog.Rungs.R001.Proofs.Keeps
import RwLog.Rungs.R004.Reading

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

theorem costed_engine : Obligation.costed_engine := engine_std

theorem advances : Obligation.advances :=
  Advances.of_id (by rw [R003.engine_std, engine_std]; exact improves)

end R004

end RwLog
