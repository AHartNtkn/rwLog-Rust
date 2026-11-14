/-
# The tabled machine runs the same from either end, and with any exact race

Two runs of the tabled machine whose programs and unfolding races are linked
(`Twin`, `Rungs/Tabled/MapGoal.lean`), one on a node and the other on its
image, show the same thing step for step: what a step of the second shows is
what the step of the first shows, every answer conversed when the image is
the converse, up to the order of the answers of a step (`trace_map`), and
they halt together (`halts_map`).

An unfolding race is `Exact` when at every lawful domain it says what the
unfolding is (`UEx`, `Rungs/Tabled/Unfolding/RacesExact.lean`). The races of
R001 and of R004 are. For exact races that meet their specification:

* `sameRun`, `halts_iff`: two tabled machines that differ in the race show
  the same thing step for step on every well-formed query, and halt
  together. So R004 halts where R001 does.
* `convTrace`: the run on `conv q` is the run on `q` with every answer
  conversed.
* `dualTrace`: so is the run on the mirror image of `q` in the mirrored
  program.
-/
import RwLog.Rungs.Tabled.MapRun
import RwLog.Rungs.Tabled.Correct
import RwLog.Rungs.Tabled.Unfolding.Races
import RwLog.Rungs.Framework.Direction
import RwLog.Rungs.Framework.Trace

namespace RwLog

namespace Tabled

open Answer Unfold

/-- The unfolding race says what the unfolding is, at the derivation kernel
of every lawful domain. -/
def Exact (U : Unfolder) : Prop :=
  ∀ {R : Type} [Answer R] [DecidableEq R] (D : Domain R) (P : Program) (K : Kernel R Cost)
    (hK : K.Refines D), D.Lawful P.sorts.interp → ProgFO P →
      UEx D P (@U R Rel (Ans D P) Cost (DerivationKernel.over D K hK P))

theorem exact_eagerRace : Exact Unfold.eagerRace :=
  fun _ _ K hK hL hP => eagerRace_ex hL K hK hP

theorem exact_raced : Exact Unfold.raced :=
  fun _ _ K hK hL hP => raced_ex hL K hK hP

/-- The second list is the first, every answer conversed when `b`, up to
order. -/
def ShownPerm {A : Type} [Answer A] (b : Bool) (xs ys : List A) : Prop :=
  ys.Perm (xs.map fun a => if b then Answer.swap a else a)

variable (U U' : Unfolder) {R : Sorts → Type} [∀ S, Answer (R S)] [∀ S, DecidableEq (R S)]
  (dom : ∀ S, Domain (R S)) (K : ∀ S, Kernel (R S) Cost) (hK : ∀ S, (K S).Refines (dom S))

section maps

variable (P : Program) (ds : List (Name × Rel)) {b t : Bool} (root : Rel)

/-- The two states after `r` rounds, for some `r`. -/
def Sim (b t : Bool) (s : (Rt @U dom K hK).State) (s' : (Rt @U' dom K hK).State) : Prop :=
  ∃ r, s = stAt @U dom K hK P root r ∧ s' = stAt @U' dom K hK ⟨ds, P.sorts⟩ (nmap b t root) r

omit [∀ S, DecidableEq (R S)] in
theorem shownPerm_of {xs : List (Ans (dom P.sorts) P)}
    {ys : List (Ans (dom P.sorts) (⟨ds, P.sorts⟩ : Program))} (h : SpansPerm b xs ys) :
    ShownPerm (A := (S : Sorts) × R S) b (xs.map fun a => ⟨P.sorts, a.span⟩)
      (ys.map fun a => ⟨P.sorts, a.span⟩) := by
  have h' := h.map (Sigma.mk (β := R) P.sorts)
  rw [List.map_map, List.map_map] at h'
  unfold ShownPerm
  rw [List.map_map]
  refine h'.trans (List.Perm.of_eq (List.map_congr_left fun a _ => ?_))
  cases b <;> rfl

variable {U U' dom K hK P ds root}
variable (hW : Twin (dom P.sorts) P ⟨ds, P.sorts⟩ b t (UAt @U dom K hK P)
    (UAt @U' dom K hK ⟨ds, P.sorts⟩))
  (hroot : GoalOk (dom P.sorts) (⟨none, root, none⟩ : GoalOf (R P.sorts) Rel))
include hW hroot

/-- A step of the two runs. -/
theorem step_map (r : Nat) :
    StepOf.Rel (ShownPerm b) (Sim @U @U' dom K hK P ds root b t)
      ((Rt @U dom K hK).step (stAt @U dom K hK P root r))
      ((Rt @U' dom K hK).step (stAt @U' dom K hK ⟨ds, P.sorts⟩ (nmap b t root) r)) := by
  have hI : ∀ r, Inv (dom P.sorts) P (T @U dom K hK P root r) :=
    fun r => (tied_at (K P.sorts) (hK P.sorts) hW root hroot r).inv
  have hI' : ∀ r, Inv (dom P.sorts) ⟨ds, P.sorts⟩
      (T @U' dom K hK ⟨ds, P.sorts⟩ (nmap b t root) r) :=
    fun r => (tied_at (K P.sorts) (hK P.sorts) hW root hroot r).inv'
  have hdm := rootDone_map (K P.sorts) (hK P.sorts) hW root hroot r
  cases hd : RD @U dom K hK P root r with
  | false =>
    have hd' : RD @U' dom K hK ⟨ds, P.sorts⟩ (nmap b t root) r = false := hdm.trans hd
    obtain ⟨l, hl, hs⟩ := rt_step_live hI hd
    obtain ⟨l', hl', hs'⟩ := rt_step_live hI' hd'
    obtain rfl := List.append_cancel_left (hl.symm.trans (rootAns_succ r))
    obtain rfl := List.append_cancel_left (hl'.symm.trans (rootAns_succ r))
    rw [hs, hs']
    exact ⟨shownPerm_of dom P ds (rootGain_map (K P.sorts) (hK P.sorts) hW root hroot r),
      r + 1, rfl, rfl⟩
  | true =>
    have hd' : RD @U' dom K hK ⟨ds, P.sorts⟩ (nmap b t root) r = true := hdm.trans hd
    rw [rt_step_done hI hd, rt_step_done hI' hd']
    exact shownPerm_of dom P ds (rootMax_map (K P.sorts) (hK P.sorts) hW root hroot r)

theorem sim_step (s : (Rt @U dom K hK).State) (s' : (Rt @U' dom K hK).State)
    (h : Sim @U @U' dom K hK P ds root b t s s') :
    StepOf.Rel (ShownPerm b) (Sim @U @U' dom K hK P ds root b t)
      ((Rt @U dom K hK).step s) ((Rt @U' dom K hK).step s') := by
  obtain ⟨r, rfl, rfl⟩ := h
  exact step_map hW hroot r

/-- **Two linked runs show the same thing step for step**, every answer of
the second the converse of one of the first when the image is the
converse. -/
theorem trace_map (n : Nat) :
    List.Forall₂ (Shown.Rel (ShownPerm b))
      ((Rt @U dom K hK).trace (stAt @U dom K hK P root 0) n)
      ((Rt @U' dom K hK).trace (stAt @U' dom K hK ⟨ds, P.sorts⟩ (nmap b t root) 0) n) :=
  Runtime.trace_of_sim (R := Rt @U dom K hK) (R' := Rt @U' dom K hK) (E := ShownPerm b) (Sim := Sim @U @U' dom K hK P ds root b t)
    (sim_step hW hroot) n (stAt @U dom K hK P root 0)
    (stAt @U' dom K hK ⟨ds, P.sorts⟩ (nmap b t root) 0) ⟨0, rfl, rfl⟩

/-- **Two linked runs halt together.** -/
theorem halts_map (n : Nat) :
    (Rt @U dom K hK).Halts (stAt @U dom K hK P root 0) n ↔
      (Rt @U' dom K hK).Halts (stAt @U' dom K hK ⟨ds, P.sorts⟩ (nmap b t root) 0) n :=
  Runtime.halts_iff_of_sim (R := Rt @U dom K hK) (R' := Rt @U' dom K hK) (E := ShownPerm b) (Sim := Sim @U @U' dom K hK P ds root b t)
    (sim_step hW hroot) n (s := stAt @U dom K hK P root 0)
    (s' := stAt @U' dom K hK ⟨ds, P.sorts⟩ (nmap b t root) 0) ⟨0, rfl, rfl⟩

end maps

omit [∀ S, DecidableEq (R S)] in
/-- Traces related step by step up to order, as traces that agree. -/
theorem traceEquiv_of_shown {M : Interp} {b : Bool} :
    ∀ {t t' : List (Shown ((S : Sorts) × R S))},
      List.Forall₂ (Shown.Rel (ShownPerm b)) t t' →
        TraceEquiv M t' (t.map fun x => if b then x.swap else x)
  | _, _, .nil => .nil
  | _, _, .cons (a := x) (b := y) h hs => by
    refine .cons ?_ (traceEquiv_of_shown hs)
    have key : ∀ {xs ys : List ((S : Sorts) × R S)}, ShownPerm b xs ys →
        StepEquiv M ys (if b then xs.map Answer.swap else xs) := fun {xs ys} h => by
      refine StepEquiv.of_perm (h.trans (List.Perm.of_eq ?_))
      cases b
      · exact List.map_id' _
      · rfl
    cases x <;> cases y <;> cases b <;>
      first | exact key h | exact (h : _ = _).symm | exact h.elim

/-! ## The linked programs -/

section twins

variable {U U' dom K hK}
variable (hG : Good @U) (hG' : Good @U') (hE : Exact @U) (hE' : Exact @U')
include hG hG' hE hE'

/-- A program is linked to itself, with any two exact races. -/
theorem twin_same {P : Program} (hL : (dom P.sorts).Lawful P.sorts.interp) (hP : ProgFO P)
    (b : Bool) :
    Twin (dom P.sorts) P ⟨P.defs, P.sorts⟩ b false (UAt @U dom K hK P) (UAt @U' dom K hK P) :=
  have ex := hE (dom P.sorts) P (K P.sorts) (hK P.sorts) hL hP
  have ex' := hE' (dom P.sorts) P (K P.sorts) (hK P.sorts) hL hP
  ⟨hL, hL, hP, hP, hG (dom P.sorts) P (K P.sorts) (hK P.sorts) hL hP,
    hG' (dom P.sorts) P (K P.sorts) (hK P.sorts) hL hP,
    Link.of_ex hL rfl ex ex' (fun _ he => he.bodyOf_nmap P b false)
      (fun d _ he A B => final_nmap b false d he A B)
      (fun d _ he A B X => closedPart_nmap b false d he A B X),
    Link.of_ex hL rfl ex' ex (fun _ he => he.bodyOf_nmap P b false)
      (fun d _ he A B => final_nmap b false d he A B)
      (fun d _ he A B X => closedPart_nmap b false d he A B X)⟩

/-- A program is linked to the mirrored program, with any two exact
races. -/
theorem twin_dual {P : Program} (hL : (dom P.sorts).Lawful P.sorts.interp) (hP : ProgFO P)
    (hP' : ProgFO P.dual) (b : Bool) :
    Twin (dom P.sorts) P ⟨P.dual.defs, P.sorts⟩ b true (UAt @U dom K hK P)
      (UAt @U' dom K hK P.dual) := by
  have ex := hE (dom P.sorts) P (K P.sorts) (hK P.sorts) hL hP
  have ex' := hE' (dom P.sorts) P.dual (K P.sorts) (hK P.sorts) hL hP'
  refine ⟨hL, hL, hP, hP', hG (dom P.sorts) P (K P.sorts) (hK P.sorts) hL hP,
    hG' (dom P.sorts) P.dual (K P.sorts) (hK P.sorts) hL hP',
    Link.of_ex (P' := P.dual) hL rfl ex ex' (fun _ he => he.bodyOf_nmap P b true)
      (fun d _ he A B => final_nmap b true d he A B)
      (fun d _ he A B X => closedPart_nmap b true d he A B X),
    Link.of_ex (P := P.dual) (P' := P) hL rfl ex' ex (fun e he => ?_) (fun d e he A B => ?_)
      (fun d e he A B X => ?_)⟩
  · have h := he.bodyOf_nmap P.dual b true
    simp only [↓reduceIte, ProgramOf.dual_dual] at h
    exact h
  · have h := final_nmap (P := P.dual) (M := P.sorts.interp) b true d he A B
    simp only [↓reduceIte, ProgramOf.dual_dual] at h
    exact h
  · have h := closedPart_nmap (P := P.dual) (M := P.sorts.interp) b true d he A B X
    simp only [↓reduceIte, ProgramOf.dual_dual] at h
    exact h

end twins

/-! ## The theorems -/

section theorems

variable {U U' dom K hK}
variable (hD : ∀ S : Sorts, S.WellFormed → (dom S).Lawful S.interp)
  (hG : Good @U) (hG' : Good @U') (hE : Exact @U) (hE' : Exact @U')
include hD hG hG' hE hE'

/-- **Two tabled machines that differ in an exact race halt together.** -/
theorem halts_iff {P : Program} {q : Rel} (wf : P.WellFormed q) (n : Nat) :
    (Rt @U dom K hK).Halts ((Rt @U dom K hK).init P q) n ↔
      (Rt @U' dom K hK).Halts ((Rt @U' dom K hK).init P q) n := by
  have h := halts_map (twin_same (K := K) (hK := hK) hG hG' hE hE' (hD _ wf.2.2.1)
    (progFO_of_wf wf) false) (root_ok wf) n
  rw [nmap_ff (normal_norm q)] at h
  rw [init_eq, init_eq]
  exact h

/-- **Two tabled machines that differ in an exact race show the same thing
step for step.** -/
theorem sameRun {P : Program} {q : Rel} (wf : P.WellFormed q) (n : Nat) :
    TraceEquiv P.sorts.interp ((Rt @U' dom K hK).trace ((Rt @U' dom K hK).init P q) n)
      ((Rt @U dom K hK).trace ((Rt @U dom K hK).init P q) n) := by
  have h := trace_map (twin_same (K := K) (hK := hK) hG hG' hE hE' (hD _ wf.2.2.1)
    (progFO_of_wf wf) false) (root_ok wf) n
  rw [nmap_ff (normal_norm q)] at h
  rw [init_eq, init_eq]
  have := traceEquiv_of_shown (M := P.sorts.interp) h
  simp only [Bool.false_eq_true, ↓reduceIte, List.map_id_fun'] at this
  exact this

end theorems

section direction

variable {U dom K hK}
variable (hD : ∀ S : Sorts, S.WellFormed → (dom S).Lawful S.interp)
  (hG : Good @U) (hE : Exact @U)
include hD hG hE

/-- **The run of the tabled machine on a converse is the run with every
answer conversed.** -/
theorem convTrace : (Rt @U dom K hK).ConvTrace := fun P q n wf => by
  have h := trace_map (twin_same (K := K) (hK := hK) hG hG hE hE (hD _ wf.2.2.1)
    (progFO_of_wf wf) true) (root_ok wf) n
  have e : nmap true false q.norm = (RelOf.conv q).norm := normB_normB true false q
  rw [e] at h
  rw [init_eq, init_eq]
  exact traceEquiv_of_shown (M := P.sorts.interp) h

/-- **The run of the tabled machine on the mirror image of a query, in the
mirrored program, is the run with every answer conversed.** -/
theorem dualTrace : (Rt @U dom K hK).DualTrace := fun P q n wf => by
  have h := trace_map (twin_dual (K := K) (hK := hK) hG hG hE hE (hD _ wf.2.2.1)
    (progFO_of_wf wf) (progFO_of_wf wf.dual) true) (root_ok wf) n
  have e : nmap true true q.norm = q.dual.norm :=
    (nmap_normB true true false q).trans (normB_dual false q).symm
  rw [e] at h
  rw [init_eq, init_eq]
  exact traceEquiv_of_shown (M := P.sorts.interp) h

end direction

end Tabled

end RwLog
