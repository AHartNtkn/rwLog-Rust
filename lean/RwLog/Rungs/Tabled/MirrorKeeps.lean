/-
# What the mirrored tabled machine keeps

The mirrored tabled machine shows at each step what the tabled machine shows,
up to the order of the answers, and is done when it is
(`Rungs/Tabled/Mirrored.lean`). So it runs like the tabled machine
(`mirror_sameRun`), and with an exact unfolding race that meets its
specification it has every property of `Runtime.Keeps`, with the tabled
machine of any other such race as base (`mirror_keeps`), and its final report
is the maximal emitted answers (`mirror_finalMaximal`).

The properties carry over along the trace (`Runtime.SameTrace.keeps`,
`Rungs/Framework/SameTrace.lean`). The laws of `|` hold of every engine, and
no answer is covered by an earlier one because the answers the tabled machine
shows in one step do not cover each other in either order
(`stepAntichain`), so their order does not matter.

`tabled_keeps` is the same list for the tabled machine itself.
-/
import RwLog.Rungs.Tabled.Mirrored
import RwLog.Rungs.Tabled.EmptySide
import RwLog.Rungs.Framework.SameTrace
import RwLog.Rungs.Framework.Writing

namespace RwLog

/-! ## Traces that agree up to the order of the answers of a step -/

section perm

variable {A : Type}

theorem Shown.Rel.emits_perm {x y : Shown A} (h : Shown.Rel (fun xs ys => xs.Perm ys) x y) :
    x.emits.Perm y.emits := by
  cases x <;> cases y <;> first | exact h | exact List.Perm.refl _ | exact h.elim

theorem perm_emits : ∀ {t t' : List (Shown A)},
    List.Forall₂ (Shown.Rel fun xs ys => xs.Perm ys) t t' →
    (t.flatMap Shown.emits).Perm (t'.flatMap Shown.emits)
  | _, _, .nil => .refl _
  | _, _, .cons h hs => by
    simp only [List.flatMap_cons]
    exact h.emits_perm.append (perm_emits hs)

end perm

namespace Tabled

open Answer Unfold

variable (U U₀ : Unfolder) {R : Sorts → Type} [∀ S, Answer (R S)] [∀ S, DecidableEq (R S)]
  (dom : ∀ S, Domain (R S)) (K : ∀ S, Kernel (R S) Cost) (hK : ∀ S, (K S).Refines (dom S))

/-! ## The answers of one step of the tabled machine -/

section run

variable {U dom K hK} {P : Program} {root : Rel}
variable (hI : ∀ r, Inv (dom P.sorts) P (T @U dom K hK P root r))
  (hL : (dom P.sorts).Lawful P.sorts.interp)
include hI hL

/-- The answers the tabled machine shows in one step do not cover each
other, in either order. -/
theorem trace_step_pairwise : ∀ (n r : Nat),
    ∀ x ∈ (Rt @U dom K hK).trace (stAt @U dom K hK P root r) n,
      x.emits.Pairwise fun a b =>
        ¬ Answer.Covers P.sorts.interp a b ∧ ¬ Answer.Covers P.sorts.interp b a
  | 0, _, x, hx => by simp [Runtime.trace] at hx
  | n + 1, r, x, hx => by
    cases hd : RD @U dom K hK P root r with
    | false =>
      obtain ⟨l, hl, hs⟩ := rt_step_live hI hd
      rw [(Rt @U dom K hK).trace_succ_emit hs] at hx
      rcases List.mem_cons.1 hx with rfl | hx
      · have hl' : l = gainOf (K P.sorts) (hK P.sorts) (UAt @U dom K hK P)
            (T @U dom K hK P root r) r ((T @U dom K hK P root r)[0]'(root_pos r)) :=
          List.append_cancel_left (hl.symm.trans (rootAns_succ r))
        show (l.map (sp @U dom K hK P)).Pairwise _
        rw [List.pairwise_map, hl']
        refine (fresh_pairwise (K P.sorts) (hK P.sorts) _ _).imp fun {y x} h => ?_
        refine ⟨fun hc => ?_, fun hc => ?_⟩
        · have := (covB_iff hL y x).2 hc
          rw [h.1] at this; cases this
        · have := (covB_iff hL x y).2 hc
          rw [h.2] at this; cases this
      · exact trace_step_pairwise n (r + 1) x hx
    | true =>
      rw [(Rt @U dom K hK).trace_succ_done (rt_step_done hI hd)] at hx
      obtain rfl : x = _ := by simpa using hx
      exact List.Pairwise.nil

end run

/-! ## The theorems -/

section theorems

variable {U U₀ dom K hK}
variable (hD : ∀ S : Sorts, S.WellFormed → (dom S).Lawful S.interp)
  (hG : Good @U) (hE : Exact @U)

include hD hG hE in
/-- The tabled machine keeps every property, with the tabled machine of any
other exact race as base. -/
theorem tabled_keeps (hG₀ : Good @U₀) (hE₀ : Exact @U₀) :
    (Rt @U dom K hK).Keeps (Rt @U₀ dom K hK) where
  sound := Engine.sound _ dom K hK hD
  pointComplete := pointComplete hD hG
  honest := honestExhaustion hD hG
  honestProgress := honestProgress hD hG
  derivationGeneral := Engine.derivationGeneral _ dom K hK hD
  terminates := fun _ _ wf ⟨n, hn⟩ => ⟨n, (halts_iff hD hG₀ hG hE₀ hE wf n).1 hn⟩
  orComm := Engine.orComm _ dom K hK
  orAssoc := Engine.orAssoc _ dom K hK
  emptySide := emptySide hD hG hE
  convTrace := convTrace hD hG hE
  dualTrace := dualTrace hD hG hE
  noSubsumed := noSubsumed hD hG
  complete := complete hD hG

include hD hG in
/-- The answers the tabled machine shows in one step do not cover each
other. -/
theorem stepAntichain : (Rt @U dom K hK).StepAntichain := fun P q wf n => by
  rw [init_eq]
  exact trace_step_pairwise (inv_of_wf (K := K) (hK := hK) hD hG wf) (hD _ wf.2.2.1) n 0

include hD hG hE in
/-- The mirrored tabled machine shows at every step what the tabled machine
shows. -/
theorem mirror_sameTrace : Runtime.SameTrace (Mt @U dom K hK) (Rt @U dom K hK) :=
  ⟨fun _ _ wf n => TraceEquiv.of_perm (mirror_trace hD hG hE wf n)⟩

include hD hG hE in
/-- **The mirrored tabled machine runs like the tabled machine.** -/
theorem mirror_sameRun : Runtime.SameRun (Mt @U dom K hK) (Rt @U dom K hK) :=
  (mirror_sameTrace (K := K) (hK := hK) hD hG hE).sameRun

include hD hG hE in
/-- **The mirrored tabled machine keeps every property**, with the tabled
machine of any exact race as base. -/
theorem mirror_keeps (hG₀ : Good @U₀) (hE₀ : Exact @U₀) :
    (Mt @U dom K hK).Keeps (Rt @U₀ dom K hK) :=
  (mirror_sameTrace (K := K) (hK := hK) hD hG hE).keeps (tabled_keeps hD hG hE hG₀ hE₀)
    (stepAntichain hD hG) (Engine.orComm _ dom K hK) (Engine.orAssoc _ dom K hK)

include hD hG in
/-- **The tabled machine emits no progress certificate.** -/
theorem neverCertifies {P : Program} {q : Rel} (wf : P.WellFormed q) (k n : Nat) :
    ¬ (Rt @U dom K hK).Certifies ((Rt @U dom K hK).init P q) k n := fun hc => by
  have hI := inv_of_wf (K := K) (hK := hK) hD hG wf
  rw [init_eq] at hc
  exact absurd rfl (trace_no_level hI (k + 1) 0 _ (List.mem_of_getElem? hc) n)

include hD hG hE in
/-- **The mirrored tabled machine emits no progress certificate.** -/
theorem mirror_neverCertifies {P : Program} {q : Rel} (wf : P.WellFormed q) (k n : Nat) :
    ¬ (Mt @U dom K hK).Certifies ((Mt @U dom K hK).init P q) k n := fun hc =>
  neverCertifies (K := K) (hK := hK) hD hG wf k n
    (((mirror_sameTrace (K := K) (hK := hK) hD hG hE).certifies wf k n).1 hc)

include hD hG hE in
/-- **The final report of the mirrored tabled machine is the maximal emitted
answers.** -/
theorem mirror_finalMaximal : (Mt @U dom K hK).FinalMaximal := fun P q wf n fin hfin => by
  have ht := mirror_trace (K := K) (hK := hK) hD hG hE wf n
  obtain ⟨y, hy, hxy⟩ := forall₂_getLast? ht (((Mt @U dom K hK).final_eq_some_iff n _ fin).1 hfin)
  cases y with
  | level _ => exact hxy.elim
  | answers _ => exact hxy.elim
  | final fin' =>
    have hp : fin.Perm fin' := hxy
    obtain ⟨h₁, h₂, h₃⟩ := finalMaximal (K := K) (hK := hK) hD hG P q wf n fin'
      (((Rt @U dom K hK).final_eq_some_iff n _ fin').2 hy)
    have he : ((Mt @U dom K hK).emitted ((Mt @U dom K hK).init P q) n).Perm
        ((Rt @U dom K hK).emitted ((Rt @U dom K hK).init P q) n) := by
      rw [(Mt @U dom K hK).emitted_eq_flatMap_trace, (Rt @U dom K hK).emitted_eq_flatMap_trace]
      exact perm_emits ht
    refine ⟨fun a ha => he.mem_iff.2 (h₁ a (hp.mem_iff.1 ha)), fun a ha => ?_, ?_⟩
    · obtain ⟨b, hb, hc⟩ := h₂ a (he.mem_iff.1 ha)
      exact ⟨b, hp.mem_iff.2 hb, hc⟩
    · exact (List.Perm.pairwise_iff (fun hab => ⟨hab.2, hab.1⟩) hp).2 h₃

end theorems

end Tabled

end RwLog
