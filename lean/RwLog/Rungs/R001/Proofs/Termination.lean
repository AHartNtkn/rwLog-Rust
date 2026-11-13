/-
# Rung R001: termination

The obligations of the termination group.

* `terminates_iff_cert`: the machine halts on a query exactly when the query
  has a termination certificate (`CertHalts.halts_of_cert`,
  `CertOfHalt.cert_of_halts`).
* `terminates_finitelyNormalising`: a query rung zero finishes has the
  one-entry certificate whose goal completes by unfolding.
-/
import RwLog.Rungs.R001.Proofs.CertHalts
import RwLog.Rungs.R001.Proofs.CertOfHalt

namespace RwLog

namespace R001

open Tier0 Exact

/-- The machine's run on a query is its run on the query's goal. -/
theorem terminates_iff_goal (P : Program) (q : Rel) :
    runtime.Terminates P q ↔ GoalTerminates P ⟨none, q, none⟩ := by
  rw [terminates_iff, goalTerminates_iff]

theorem terminates_iff_cert : Obligation.terminates_iff_cert := by
  intro P q hwf
  rw [terminates_iff_goal]
  exact ⟨CertOfHalt.cert_of_halts hwf.2.2 (goodG_root q),
    fun ⟨_, _, hC⟩ => CertHalts.halts_of_cert hwf.2.2 (goodG_root q) hC⟩

/-- A goal that completes by unfolding has a one-entry certificate. -/
theorem cert_of_unfoldFinal {P : Program} (hwf : ∀ ρ ∈ P.theory, ρ.WellFormed) {root : Goal}
    (hroot : GoodG root) {k : Nat} (hf : unfoldFinal P k root.norm.2 = true) :
    Cert.Valid P [⟨root.norm.2, unfoldAnswers P k root.norm.2, 0⟩] k root := by
  have hL := simpLaws_of_wf hwf
  have hg := goodG_norm hroot
  refine ⟨⟨_, List.mem_singleton_self _, Goal.same_refl _⟩, fun e he => ?_⟩
  cases List.mem_singleton.1 he
  refine ⟨CertOfHalt.interfaced_of_goodG hg, fun f hf' => GDerives.unfold hf', fun x hx => ?_,
    .inl hf⟩
  have hA : AnsSub P (certTables [⟨root.norm.2, unfoldAnswers P k root.norm.2, 0⟩]) := by
    refine ansSub_of hL ?_ ?_
    · intro t ht
      cases List.mem_singleton.1 ht
      exact hg
    · intro t ht a ha
      cases List.mem_singleton.1 ht
      exact unfold_sub ha
  obtain ⟨s, hder, hsub⟩ := cands_sub hL hA hg hx
  exact (unfold_xc hL hf hder).cover hsub

theorem terminates_finitelyNormalising : Obligation.terminates_finitelyNormalising := by
  intro P q hwf ⟨k, hk⟩
  show runtime.Terminates P q
  rw [terminates_iff_goal]
  refine CertHalts.halts_of_cert hwf.2.2 (goodG_root q)
    (cert_of_unfoldFinal hwf.2.2 (goodG_root q) (k := k) ?_)
  rw [Unf.unfoldFinal_key, R000.roundFinal_iff]
  exact hk

end R001

end RwLog
