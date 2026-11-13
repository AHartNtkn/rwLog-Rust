/-
# Rung R001: termination

The obligations of the termination group.

* `terminates_iff_cert`: the machine halts on a query exactly when the query
  has a termination certificate (`CertHalts.halts_of_cert`,
  `CertOfHalt.cert_of_halts`).
* `terminates_finitelyNormalising`: a query rung zero finishes has the
  one-entry certificate whose goal completes by unfolding.
* `finite_side_seq_left`, `finite_side_seq_right`, `finite_side_and`,
  `empty_side`: the certificate of the finite side, the certificates of the
  pushes from its answers, and one entry for the query with the push strategy
  make a certificate (`Combine.seqL_cert` and its three variants).
-/
import RwLog.Rungs.R001.Proofs.CertHalts
import RwLog.Rungs.R001.Proofs.CertOfHalt
import RwLog.Rungs.R001.Proofs.CertCombine

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

/-! ## A finite side -/

section FiniteSide

open Combine

variable {P : Program} (hwf : ∀ ρ ∈ P.theory, ρ.WellFormed)
include hwf

theorem cert_of_terminates {a : Rel} (h : runtime.Terminates P a) :
    ∃ C D, Cert.Valid P C D ⟨none, a, none⟩ :=
  CertOfHalt.cert_of_halts hwf (goodG_root a) ((terminates_iff_goal P a).1 h)

theorem terminates_of_cert {q : Rel} (h : ∃ C D, Cert.Valid P C D ⟨none, q, none⟩) :
    runtime.Terminates P q :=
  let ⟨_, _, hC⟩ := h
  (terminates_iff_goal P q).2 (CertHalts.halts_of_cert hwf (goodG_root q) hC)

theorem seq_left_halts {a b : Rel} (ha : runtime.Terminates P a)
    (hx : ∀ x ∈ runtime.Answers P a, GoalTerminates P ⟨bound x.rightIface, b, none⟩) :
    runtime.Terminates P (.seq a b) := by
  obtain ⟨CL, DL, hCL⟩ := cert_of_terminates hwf ha
  exact terminates_of_cert hwf (seqL_cert (simpLaws_of_wf hwf) hCL
    (certs_of_answers hwf hCL (fun x => ⟨bound x.rightIface, b, none⟩)
      (fun x x' hxe => CertHalts.same_mk _ (iface_equiv x x' hxe).1 rfl)
      (fun x => goodG_pushL (goodG_root (.seq a b)) b x) hx))

theorem seq_right_halts {a b : Rel} (hb : runtime.Terminates P b)
    (hy : ∀ y ∈ runtime.Answers P b, GoalTerminates P ⟨none, a, bound y.leftIface⟩) :
    runtime.Terminates P (.seq a b) := by
  obtain ⟨CL, DL, hCL⟩ := cert_of_terminates hwf hb
  exact terminates_of_cert hwf (seqR_cert (simpLaws_of_wf hwf) hCL
    (certs_of_answers hwf hCL (fun y => ⟨none, a, bound y.leftIface⟩)
      (fun x x' hxe => CertHalts.same_mk _ rfl (iface_equiv x x' hxe).2)
      (fun y => goodG_pushR (goodG_root (.seq a b)) a y) hy))

theorem and_halts {a b : Rel} (ha : runtime.Terminates P a)
    (hx : ∀ x ∈ runtime.Answers P a, GoalTerminates P (andPush b x)) :
    runtime.Terminates P (.and a b) ∧ runtime.Terminates P (.and b a) := by
  obtain ⟨CL, DL, hCL⟩ := cert_of_terminates hwf ha
  have hc := certs_of_answers hwf hCL (andPush b)
    (fun x x' hxe => CertHalts.same_mk _ (iface_equiv x x' hxe).2 (iface_equiv x x' hxe).1)
    (fun x => goodG_andPush b x) hx
  exact ⟨terminates_of_cert hwf (andL_cert (simpLaws_of_wf hwf) hCL hc),
    terminates_of_cert hwf (andR_cert (simpLaws_of_wf hwf) hCL hc)⟩

end FiniteSide

theorem finite_side_seq_left : Obligation.finite_side_seq_left :=
  fun _ _ _ hwf ha hx => seq_left_halts hwf.2.2 ha hx

theorem finite_side_seq_right : Obligation.finite_side_seq_right :=
  fun _ _ _ hwf hb hy => seq_right_halts hwf.2.2 hb hy

theorem finite_side_and : Obligation.finite_side_and :=
  fun _ _ _ hwf ha hx => and_halts hwf.2.2 ha hx

theorem empty_side : Obligation.empty_side := by
  intro P a b hwf ha he
  have hno : ∀ (g : Span → Goal), ∀ x ∈ runtime.Answers P a, GoalTerminates P (g x) := by
    intro g x hx
    rw [he] at hx
    exact absurd hx (Set.notMem_empty x)
  exact ⟨seq_left_halts hwf.2.2 ha (hno _), seq_right_halts hwf.2.2 ha (hno _),
    and_halts hwf.2.2 ha (hno _)⟩

end R001

end RwLog
