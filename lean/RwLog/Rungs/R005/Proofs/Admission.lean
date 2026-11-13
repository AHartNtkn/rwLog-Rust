/-
# R005 is admitted

R005 is the mirrored machine of R004 (`Rungs/Mirror`). Everything here is a
theorem about the mirrored machine of any machine, applied to R004, with what
it asks of R004 supplied: R004 keeps every baseline property (`R004.keeps`),
and the tabled machine goes through flipped states on a converse at the same
cost (`Rungs/Tabled/Direction.lean`).

The separation is the two facts about R004 on `chain k` (`Proofs/Forward.lean`
and `Proofs/Backward.lean`): R004 pays `2 ^ k` from the left, and its first
round on the mirror image is cubic; R005's first step costs at most two races
of that round.
-/
import RwLog.Rungs.R005.Spec
import RwLog.Rungs.R005.Proofs.Forward
import RwLog.Rungs.R005.Proofs.Backward
import RwLog.Rungs.R004.Proofs.Admission
import RwLog.Rungs.Mirror.Keeps
import RwLog.Rungs.Mirror.Reading
import RwLog.Rungs.Tabled.Direction

namespace RwLog

namespace R005

theorem r004_dual : R004.costed.runtime.DualTrace := R004.keeps.dualTrace

theorem init_ticks (P : Program) (q : Rel) : (R004.costed.init P q).ticks = q.size :=
  Tabled.init_ticks R004.unfolder P q

theorem r004_conv : ConvBisim R004.costed fun s s' => s = R001.StateOf.flip s' :=
  Tabled.convBisim R004.unfolder

/-! ## The same answers -/

theorem same_trace : Obligation.same_trace := fun _ _ hP n =>
  RwLog.Mirror.trace_start r004_dual hP n

theorem keeps : Obligation.keeps :=
  RwLog.Mirror.keeps R004.keeps r004_conv (Tabled.start_or_comm R004.unfolder)
    (Tabled.start_or_assoc R004.unfolder)

theorem sound : Obligation.sound := keeps.sound
theorem complete : Obligation.complete := keeps.complete
theorem honest_exhaustion : Obligation.honest_exhaustion := keeps.honest

/-! ## The same cost from both ends -/

theorem mirror_exact : Obligation.mirror_exact := RwLog.Mirror.dualBisim r004_dual

theorem conv_exact : Obligation.conv_exact := ⟨_, RwLog.Mirror.convBisim r004_conv⟩

theorem direction_free : Obligation.direction_free :=
  RwLog.Mirror.directionFree (k := 1) r004_dual r004_conv
    (fun P q => by
      rw [init_ticks, init_ticks, RelOf.size]; omega)
    (fun P q => by
      rw [init_ticks, init_ticks, RelOf.size]; omega)

/-! ## Never much worse -/

theorem simulates : Obligation.simulates :=
  RwLog.Mirror.simulates r004_dual
    (fun P q => by rw [init_ticks]; exact Nat.le_add_left _ _)
    (Tabled.step_pos R004.unfolder)

/-! ## Exponentially better on a family -/

theorem size_chain (k : Nat) : (chain k).size = 12 * k + 15 := by
  rw [← RelOf.size_dual, Mirror.dual_chain, Mirror.size_mir]

theorem calls_chain : ∀ k, (chain k).calls = []
  | 0 => by simp [chain, R004.bit, RelOf.calls]
  | k + 1 => by rw [chain, RelOf.calls, calls_chain k]; simp [R004.bit, RelOf.calls]

theorem wellFormed (k : Nat) : (sepFam k).1.WellFormed (sepFam k).2 := by
  refine ⟨by simp [sepFam], ?_, by simp [sepFam]⟩
  intro n hn
  simp [sepFam, calls_chain] at hn

theorem separates : Obligation.separates := by
  intro k
  have hsize : (sepFam k).1.size = 0 := by simp [sepFam, ProgramOf.size, Theory.size]
  refine ⟨wellFormed k, ?_, ⟨∅, fun ρ h => absurd h List.not_mem_nil⟩,
    ⟨(.sym "z", .sym "c"), rfl⟩, ?_⟩
  · rw [hsize]; show 0 + (chain k).size ≤ 12 * k + 15; rw [size_chain]; omega
  intro M _ x hx
  have hx' : x = (.sym "z", .sym "c") := hx
  subst hx'
  refine ⟨?_, fun n hn => r004_forward k n M _ hn⟩
  obtain ⟨as, s', hs, ⟨a, ha, hden⟩, ht⟩ := r004_mirror k
  refine ⟨1, RwLog.Mirror.covered_first r004_dual (wellFormed k) hs ha (hden M), ?_⟩
  have h := RwLog.Mirror.paid_le_min (C := R004.costed) (sepFam k).1 (sepFam k).2 1
  have h0 : R004.costed.spent s' 0 = 0 := rfl
  have hsp : R004.costed.spent (R004.costed.start (sepFam k).1.dual (sepFam k).2.dual) 1 =
      (R004.costed.step (R004.costed.start (sepFam k).1.dual (sepFam k).2.dual)).ticks := by
    rw [R004.costed.spent_succ_emit hs, h0, Nat.add_zero]
  have hmin := Nat.min_le_right (R004.costed.spent (R004.costed.start (sepFam k).1 (sepFam k).2) 1)
    (R004.costed.spent (R004.costed.start (sepFam k).1.dual (sepFam k).2.dual) 1)
  rw [hsp] at hmin
  have i1 : (R004.costed.init (sepFam k).1 (sepFam k).2).ticks = 12 * k + 15 :=
    (Tabled.init_ticks R004.unfolder _ _).trans (size_chain k)
  have i2 : (R004.costed.init (sepFam k).1.dual (sepFam k).2.dual).ticks = 12 * k + 15 :=
    (Tabled.init_ticks R004.unfolder _ _).trans ((RelOf.size_dual _).trans (size_chain k))
  rw [i1, i2] at h
  have h3 := Nat.mul_le_mul_left 14 (le_trans hmin ht)
  show costed.paid _ _ 1 ≤ 24 * k + 32 + 28 * mirrorFirst k
  have h4 : RwLog.Mirror.machine R004.costed = costed := rfl
  rw [h4] at h
  omega

/-! ## Admission -/

theorem improves : Obligation.improves where
  simulates := by
    refine simulates.mono fun c n => ?_
    show c + n + 2 * (c + 1) * (1 + 14 * c) ≤ 29 * (c + n + 1) ^ 2
    have h1 : 2 * (c + 1) * (1 + 14 * c) ≤ 2 * (c + n + 1) * (14 * (c + n + 1)) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h2 : c + n + 1 ≤ (c + n + 1) ^ 2 := Nat.le_self_pow (by omega) _
    have h3 : 2 * (c + n + 1) * (14 * (c + n + 1)) = 28 * (c + n + 1) ^ 2 := by ring
    omega
  separates := by
    refine separates.mono (fun k => ?_) fun k => ?_
    · show 12 * k + 15 ≤ 15 * (k + 1) ^ 1
      rw [Nat.pow_one]; omega
    · show 24 * k + 32 + 28 * (100000 * (k + 2) ^ 3) ≤ 22400032 * (k + 1) ^ 3
      have h1 : (k + 2) ^ 3 ≤ (2 * (k + 1)) ^ 3 := Nat.pow_le_pow_left (by omega) 3
      have h2 : (2 * (k + 1)) ^ 3 = 8 * (k + 1) ^ 3 := by ring
      have h3 : k + 1 ≤ (k + 1) ^ 3 := Nat.le_self_pow (by omega) _
      omega

theorem costed_engine : Obligation.costed_engine := by
  show R004.engine.mirrored.costed = RwLog.Mirror.machine R004.costed
  rw [RwLog.Mirror.mirrored_costed, R004.costed_engine]

theorem admits : Obligation.admits :=
  Admits.of_id (by rw [R004.costed_engine, costed_engine]; exact improves) (by
    rw [costed_engine]
    refine ⟨direction_free.toMirror.mono ?_, direction_free.ofMirror.mono ?_,
      direction_free.toConv.mono ?_, direction_free.ofConv.mono ?_⟩ <;>
    · intro c n
      show c + 2 ≤ 2 * (c + n + 1) ^ 1
      rw [Nat.pow_one]; omega)

end R005

end RwLog
