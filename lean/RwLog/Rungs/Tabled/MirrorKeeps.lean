/-
# What the mirrored tabled machine keeps

The mirrored tabled machine shows at each step what the tabled machine shows,
up to the order of the answers, and is done when it is
(`Rungs/Tabled/Mirrored.lean`). So it runs like the tabled machine
(`mirror_sameRun`), and with an exact unfolding race that meets its
specification it has every property of `Runtime.Keeps`, with the tabled
machine of any other such race as base (`mirror_keeps`), and its final report
is the maximal emitted answers (`mirror_finalMaximal`).

* Soundness, generality and the laws of `|` hold of every engine.
* Completeness, honesty and the certificates carry over along the same run.
* It halts where the base halts: the tabled machine with its race does
  (`halts_iff`), and it is done when that machine is.
* A side that halts with no answer, the converse and the mirrored program:
  from the tabled machine (`emptySide`, `convTrace`, `dualTrace`), one run at
  a time.
* No answer is covered by an earlier one: across steps because that holds of
  the tabled machine, within a step because the answers the tabled machine
  shows in one step do not cover each other in either order
  (`trace_step_pairwise`), so their order does not matter.

`tabled_keeps` is the same list for the tabled machine itself.
-/
import RwLog.Rungs.Tabled.Mirrored
import RwLog.Rungs.Tabled.EmptySide
import RwLog.Rungs.Framework.Transfer
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

/-- A relation that holds from each emitted answer to each later one, and in
both orders between the answers of one step, holds from each emitted answer
to each later one in a trace that shows the same steps in another order. -/
theorem pairwise_of_perm_steps {S : A → A → Prop} : ∀ {t t' : List (Shown A)},
    List.Forall₂ (Shown.Rel fun xs ys => xs.Perm ys) t t' →
    (t'.flatMap Shown.emits).Pairwise S →
    (∀ x ∈ t', x.emits.Pairwise fun a b => S a b ∧ S b a) →
    (t.flatMap Shown.emits).Pairwise S
  | _, _, .nil, _, _ => List.Pairwise.nil
  | _, _, @List.Forall₂.cons _ _ _ x y t t' h hs, hp, hstep => by
    simp only [List.flatMap_cons] at hp ⊢
    obtain ⟨-, h₂, h₃⟩ := List.pairwise_append.1 hp
    refine List.pairwise_append.2 ⟨?_,
      pairwise_of_perm_steps hs h₂ fun z hz => hstep z (List.mem_cons_of_mem _ hz),
      fun a ha b hb => ?_⟩
    · have := hstep y List.mem_cons_self
      exact ((List.Perm.pairwise_iff (fun hab => ⟨hab.2, hab.1⟩) h.emits_perm).2 this).imp
        fun h => h.1
    · exact h₃ a (h.emits_perm.mem_iff.1 ha) b ((perm_emits hs).mem_iff.1 hb)

theorem forall₂_getElem? {α β : Type} {E : α → β → Prop} : ∀ {l : List α} {l' : List β},
    List.Forall₂ E l l' → ∀ {k : Nat} {x : α}, l[k]? = some x → ∃ y, l'[k]? = some y ∧ E x y
  | _, _, .nil, _, _, h => by simp at h
  | _, _, .cons hab t, 0, _, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    exact ⟨_, rfl, hab⟩
  | _, _, .cons _ t, k + 1, _, h => by
    simp only [List.getElem?_cons_succ] at h ⊢
    exact forall₂_getElem? t h

theorem forall₂_getLast? {α β : Type} {E : α → β → Prop} {l : List α} {l' : List β}
    (h : List.Forall₂ E l l') {x : α} (hx : l.getLast? = some x) :
    ∃ y, l'.getLast? = some y ∧ E x y := by
  rw [List.getLast?_eq_getElem?] at hx ⊢
  rw [← h.length_eq]
  exact forall₂_getElem? h hx

variable [Answer A] {M : Interp}

theorem traceEquiv_of_perm {t t' : List (Shown A)}
    (h : List.Forall₂ (Shown.Rel fun xs ys => xs.Perm ys) t t') : TraceEquiv M t t' :=
  List.Forall₂.imp (fun x y hxy => by
    cases x <;> cases y <;> first | exact StepEquiv.of_perm hxy | exact hxy) h

theorem TraceEquiv.map_swap {B : Type} [Answer B] {t : List (Shown A)} {t' : List (Shown B)}
    (h : TraceEquiv M t t') : TraceEquiv M (t.map Shown.swap) (t'.map Shown.swap) :=
  List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2
    (List.Forall₂.imp (fun _ _ h => h.swap) h))

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

include hD hG hE in
/-- **The mirrored tabled machine runs like the tabled machine.** -/
theorem mirror_sameRun : Runtime.SameRun (Mt @U dom K hK) (Rt @U dom K hK) where
  emitted P q wf n := by
    rw [(Mt @U dom K hK).emitted_eq_flatMap_trace, (Rt @U dom K hK).emitted_eq_flatMap_trace]
    exact StepEquiv.of_perm (perm_emits (mirror_trace hD hG hE wf n))
  halts P q wf n := mirror_halts hD hG hE wf n

include hD hG hE in
/-- **The mirrored tabled machine keeps every property**, with the tabled
machine of any exact race as base. -/
theorem mirror_keeps (hG₀ : Good @U₀) (hE₀ : Exact @U₀) :
    (Mt @U dom K hK).Keeps (Rt @U₀ dom K hK) := by
  have hS := mirror_sameRun (K := K) (hK := hK) hD hG hE
  have t0 : (Rt @U dom K hK).Tier0 :=
    ⟨Engine.sound _ dom K hK hD, complete hD hG, honestExhaustion hD hG⟩
  have hconv : ∀ {P : Program} {q : Rel}, P.WellFormed q → P.WellFormed (.conv q) :=
    fun wf => wf.of_sub (fun _ h => h) (fun _ h => h)
  refine
    { sound := Engine.sound _ dom K hK hD
      pointComplete := (hS.complete t0.complete).pointwise
      honest := hS.honest t0
      honestProgress := fun P q wf k n hc p hp h₁ h₂ => ?_
      derivationGeneral := Engine.derivationGeneral _ dom K hK hD
      terminates := fun P q wf ⟨n, hn⟩ =>
        ⟨n, (mirror_halts hD hG hE wf n).2 ((halts_iff hD hG₀ hG hE₀ hE wf n).1 hn)⟩
      orComm := Engine.orComm _ dom K hK
      orAssoc := Engine.orAssoc _ dom K hK
      emptySide := fun P a b wf ht he => ?_
      convTrace := fun P q n wf => ?_
      dualTrace := fun P q n wf => ?_
      noSubsumed := fun P q wf n => ?_
      complete := hS.complete t0.complete }
  · -- a certificate of the mirrored machine is one of the tabled machine
    obtain ⟨y, hy, hxy⟩ := forall₂_getElem? (mirror_trace hD hG hE wf (k + 1)) hc
    have hy' : (Rt @U dom K hK).Certifies ((Rt @U dom K hK).init P q) k n := by
      cases y with
      | level m => obtain rfl : n = m := hxy; exact hy
      | answers _ => exact hxy.elim
      | final _ => exact hxy.elim
    obtain ⟨a, ha, hpa⟩ := honestProgress hD hG P q wf k n hy' p hp h₁ h₂
    obtain ⟨a', ha', e⟩ := hS.symm.answer wf ha
    exact ⟨a', ha', e.2 hpa⟩
  · -- the empty side
    have wfa : P.WellFormed a := wf.of_sub (fun _ h => List.mem_append_left _ h)
      (fun _ h => List.mem_append_left _ h)
    have wfba : P.WellFormed (.seq b a) := wf.of_sub
      (fun _ h => (List.mem_append.1 h).elim (List.mem_append_right _) (List.mem_append_left _))
      (fun _ h => (List.mem_append.1 h).elim (List.mem_append_right _) (List.mem_append_left _))
    have wfand : P.WellFormed (.and a b) := wf.of_sub (fun _ h => h) (fun _ h => h)
    have wfand' : P.WellFormed (.and b a) := wfba.of_sub (fun _ h => h) (fun _ h => h)
    have up : ∀ {q : Rel}, P.WellFormed q → (Rt @U dom K hK).Terminates P q →
        (Mt @U dom K hK).Terminates P q :=
      fun wf' ⟨n, hn⟩ => ⟨n, (mirror_halts hD hG hE wf' n).2 hn⟩
    have ht' : (Rt @U dom K hK).Terminates P a := by
      obtain ⟨n, hn⟩ := ht
      exact ⟨n, (mirror_halts hD hG hE wfa n).1 hn⟩
    have he' : (Rt @U dom K hK).Answers P a = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun x ⟨n, hx⟩ => ?_
      obtain ⟨x', hx', -⟩ := hS.symm.answer wfa hx
      have : x' ∈ (Mt @U dom K hK).Answers P a := ⟨n, hx'⟩
      rw [he] at this
      exact this
    obtain ⟨h₁, h₂, h₃, h₄⟩ := emptySide (K := K) (hK := hK) hD hG hE P a b wf ht' he'
    exact ⟨up wf h₁, up wfba h₂, up wfand h₃, up wfand' h₄⟩
  · -- the converse
    exact (traceEquiv_of_perm (mirror_trace hD hG hE (hconv wf) n)).trans
      ((convTrace hD hG hE P q n wf).trans
        (traceEquiv_of_perm (mirror_trace hD hG hE wf n)).symm.map_swap)
  · -- the mirrored program
    exact (traceEquiv_of_perm (M := P.sorts.interp) (mirror_trace hD hG hE wf.dual n)).trans
      ((dualTrace hD hG hE P q n wf).trans
        (traceEquiv_of_perm (mirror_trace hD hG hE wf n)).symm.map_swap)
  · -- no answer is covered by an earlier one
    rw [(Mt @U dom K hK).emitted_eq_flatMap_trace]
    refine pairwise_of_perm_steps (mirror_trace hD hG hE wf n) ?_ ?_
    · have := noSubsumed (K := K) (hK := hK) hD hG P q wf n
      rw [(Rt @U dom K hK).emitted_eq_flatMap_trace] at this
      exact this
    · rw [init_eq]
      exact trace_step_pairwise (inv_of_wf (K := K) (hK := hK) hD hG wf) (hD _ wf.2.2.1) n 0

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
    ¬ (Mt @U dom K hK).Certifies ((Mt @U dom K hK).init P q) k n := fun hc => by
  obtain ⟨y, hy, hxy⟩ := forall₂_getElem? (mirror_trace hD hG hE wf (k + 1)) hc
  refine neverCertifies (K := K) (hK := hK) hD hG wf k n ?_
  cases y with
  | level m => obtain rfl : n = m := hxy; exact hy
  | answers _ => exact hxy.elim
  | final _ => exact hxy.elim

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
