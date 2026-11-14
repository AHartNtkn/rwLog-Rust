/-
# The mirrored tabled machine shows what the tabled machine shows

`(Tabled.engine U).mirrored` runs the tabled machine on the root node and on
its converse and shows, at its `k`-th step, the `k`-th step of whichever of
the two gets there first (`Rungs/Mirror/Machine.lean`). With an exact race
the two runs gain corresponding answers round by round and are complete in
the same round (`Rungs/Tabled/MapRun.lean`), so it does not matter which of
them is shown: what the mirrored machine shows at each step is what the
tabled machine shows, up to the order of the answers (`mirror_trace`), and it
is done when the tabled machine is (`mirror_halts`).
-/
import RwLog.Rungs.Tabled.Symmetry
import RwLog.Rungs.Mirror.Trace

namespace RwLog

namespace Tabled

open Answer Unfold

variable (U : Unfolder) {R : Sorts → Type} [∀ S, Answer (R S)] [∀ S, DecidableEq (R S)]
  (dom : ∀ S, Domain (R S)) (K : ∀ S, Kernel (R S) Cost) (hK : ∀ S, (K S).Refines (dom S))
  (P : Program) (root : Rel)

/-- The mirrored machine. -/
abbrev Mt : Runtime := ((engine @U).mirrored.costedAt dom K hK).runtime

/-- The node a run is on: the root node, or its converse. -/
def nodeOf (d : Bool) : Rel := if d then root else root.normConv

theorem nodeOf_true : nodeOf root true = root := rfl

theorem nodeOf_false : nodeOf root false = nmap true false root := rfl

/-- The state of a run after `r` rounds. -/
def runAt (d : Bool) (r : Nat) : StateOf (R P.sorts) Rel (Ans (dom P.sorts) P) :=
  ⟨T @U dom K hK P (nodeOf root d) r, r⟩

/-- What a step of the tabled machine returns. -/
def stepV (s : StateOf (R P.sorts) Rel (Ans (dom P.sorts) P)) :
    StepOf (Ans (dom P.sorts) P) (StateOf (R P.sorts) Rel (Ans (dom P.sorts) P)) :=
  (step (K := DerivationKernel.over (dom P.sorts) (K P.sorts) (hK P.sorts) P)
    (UAt @U dom K hK P) s).val

/-- What a round gains at the root table of a run. -/
abbrev gainAt (d : Bool) (r : Nat) : List (Ans (dom P.sorts) P) :=
  gainOf (K P.sorts) (hK P.sorts) (UAt @U dom K hK P) (T @U dom K hK P (nodeOf root d) r) r
    ((T @U dom K hK P (nodeOf root d) r)[0]'(root_pos r))

theorem stepV_live {d : Bool} {r : Nat} (h : RD @U dom K hK P (nodeOf root d) r = false) :
    stepV @U dom K hK P (runAt @U dom K hK P root d r) =
      .emit (gainAt @U dom K hK P root d r) (runAt @U dom K hK P root d (r + 1)) :=
  step_live h

theorem stepV_done {d : Bool} {r : Nat} (h : RD @U dom K hK P (nodeOf root d) r = true) :
    stepV @U dom K hK P (runAt @U dom K hK P root d r) =
      .done ((RA @U dom K hK P (nodeOf root d) r).maximaBy (covB (dom P.sorts) P)) :=
  step_done h

theorem after_run (d : Bool) (r : Nat) :
    Mirror.after (stepV @U dom K hK P (runAt @U dom K hK P root d r)) =
      if RD @U dom K hK P (nodeOf root d) r then none
      else some (runAt @U dom K hK P root d (r + 1)) := by
  cases h : RD @U dom K hK P (nodeOf root d) r
  · rw [stepV_live @U dom K hK P root h]; rfl
  · rw [stepV_done @U dom K hK P root h]; rfl

section runs

variable {U dom K hK P root}
variable (hG : Good @U) (hE : Exact @U) (hL : (dom P.sorts).Lawful P.sorts.interp)
  (hP : ProgFO P) (hroot : GoalOk (dom P.sorts) (⟨none, root, none⟩ : GoalOf (R P.sorts) Rel))
include hG hE hL hP hroot

/-- The two root tables are complete in the same rounds. -/
theorem done_conv (r : Nat) :
    RD @U dom K hK P (nodeOf root false) r = RD @U dom K hK P (nodeOf root true) r := by
  rw [nodeOf_false, nodeOf_true]
  exact rootDone_map (K P.sorts) (hK P.sorts)
    (twin_same (K := K) (hK := hK) hG hG hE hE hL hP true) root hroot r

theorem runs : Mirror.Runs (stepV @U dom K hK P) (runAt @U dom K hK P root) where
  next d r s hs := by
    rw [after_run] at hs
    cases h : RD @U dom K hK P (nodeOf root d) r <;> rw [h] at hs
    · rw [ite_of_neg Bool.false_ne_true] at hs
      exact (Option.some.inj hs).symm
    · rw [ite_of_pos rfl] at hs
      cases hs
  together r := by
    rw [after_run, after_run, done_conv hG hE hL hP hroot r]
    cases RD @U dom K hK P (nodeOf root true) r
    · rw [ite_of_neg Bool.false_ne_true, ite_of_neg Bool.false_ne_true, Option.isSome_some,
        Option.isSome_some]
    · rw [ite_of_pos rfl, ite_of_pos rfl]

theorem inv_run (d : Bool) (r : Nat) :
    Inv (dom P.sorts) P (T @U dom K hK P (nodeOf root d) r) := by
  have h := tied_at (K P.sorts) (hK P.sorts)
    (twin_same (K := K) (hK := hK) hG hG hE hE hL hP true) root hroot r
  cases d
  · rw [nodeOf_false]; exact h.inv'
  · rw [nodeOf_true]; exact h.inv

omit hG hE hL hP in
/-- The representatives of answers of a run, as the mirrored machine reports
them. -/
theorem shown_spans (e : Bool) {as : List (Ans (dom P.sorts) P)}
    (has : ∀ a ∈ as, a.goal = ⟨none, nodeOf root e, none⟩) :
    (Mirror.orientV e as).filterMap (Ans.rootSpan root) = as.map fun a => smap (!e) a.span := by
  cases e
  · unfold Mirror.orientV
    simp only [Bool.false_eq_true, ite_false, List.filterMap_map]
    rw [← List.filterMap_eq_map]
    refine List.filterMap_congr fun a ha => ?_
    have hg := has a ha
    show Ans.rootSpan root (Ans.swapA (dom P.sorts) P a).val = some (Answer.swap a.span)
    have e₀ : (Ans.swapA (dom P.sorts) P a).val.goal =
        ⟨a.goal.rb, a.goal.node.normConv, a.goal.lb⟩ := rfl
    have e₁ : (Ans.swapA (dom P.sorts) P a).val.goal = ⟨none, root, none⟩ := by
      rw [e₀, hg]
      dsimp only
      rw [show nodeOf root false = root.normConv from rfl, hroot.normal.normConv_normConv]
    unfold Ans.rootSpan
    rw [ite_of_pos e₁]; rfl
  · exact filterMap_root has

/-- What a run gains at its root table in a round, as the mirrored machine
reports it, is what the run on the root node gains, up to order. -/
theorem gain_perm (e : Bool) (r : Nat) :
    ((gainAt @U dom K hK P root e r).map fun a => smap (!e) a.span).Perm
      ((gainAt @U dom K hK P root true r).map (·.span)) := by
  cases e
  · have h := rootGain_map (K P.sorts) (hK P.sorts)
      (twin_same (K := K) (hK := hK) hG hG hE hE hL hP true) root hroot r
    have h' := h.map (Answer.swap)
    rw [List.map_map, List.map_map] at h'
    refine h'.trans (List.Perm.of_eq (List.map_congr_left fun a _ => ?_))
    exact hL.swap_swap _
  · exact List.Perm.refl _

/-- The maximal answers of the root table of a run, as the mirrored machine
reports them, are those of the run on the root node, up to order. -/
theorem max_perm (e : Bool) (r : Nat) :
    (((RA @U dom K hK P (nodeOf root e) r).maximaBy (covB (dom P.sorts) P)).map
        fun a => smap (!e) a.span).Perm
      (((RA @U dom K hK P (nodeOf root true) r).maximaBy (covB (dom P.sorts) P)).map
        (·.span)) := by
  cases e
  · have h := rootMax_map (K P.sorts) (hK P.sorts)
      (twin_same (K := K) (hK := hK) hG hG hE hE hL hP true) root hroot r
    have h' := h.map (Answer.swap)
    rw [List.map_map, List.map_map] at h'
    refine h'.trans (List.Perm.of_eq (List.map_congr_left fun a _ => ?_))
    exact hL.swap_swap _
  · exact List.Perm.refl _

/-- The two machines after `r` steps. -/
def MSim (U : Unfolder) (dom : ∀ S, Domain (R S)) (K : ∀ S, Kernel (R S) Cost)
    (hK : ∀ S, (K S).Refines (dom S)) (P : Program) (root : Rel)
    (m : (Mt @U dom K hK).State) (s : (Rt @U dom K hK).State) : Prop :=
  ∃ (r : Nat) (st : Mirror.StOf (StateOf (R P.sorts) Rel (Ans (dom P.sorts) P))),
    Mirror.At (stepV @U dom K hK P) (runAt @U dom K hK P root) r st ∧
    m = ⟨P, root, st⟩ ∧ s = stAt @U dom K hK P root r

/-- A step of the two machines. -/
theorem msim_step (m : (Mt @U dom K hK).State) (s : (Rt @U dom K hK).State)
    (h : MSim @U dom K hK P root m s) :
    StepOf.Rel (fun xs ys => xs.Perm ys) (MSim @U dom K hK P root)
      ((Mt @U dom K hK).step m) ((Rt @U dom K hK).step s) := by
  obtain ⟨r, st, hat, rfl, rfl⟩ := h
  have hI := fun d r => inv_run (K := K) (hK := hK) hG hE hL hP hroot d r
  have hIt : ∀ r, Inv (dom P.sorts) P (T @U dom K hK P root r) := fun r => hI true r
  have hR := runs (K := K) (hK := hK) hG hE hL hP hroot
  obtain ⟨e, next, hv, hnext⟩ := Mirror.go_val (K P.sorts) (hK P.sorts)
    (fun s => step (K := DerivationKernel.over (dom P.sorts) (K P.sorts) (hK P.sorts) P)
      (UAt @U dom K hK P) s) hR st.gap st.fwd st.lead st.lag r hat.gap hat.lead hat.lag hat.past
  have hstep : (Mt @U dom K hK).step ⟨P, root, st⟩ =
      match Mirror.shownV e next (stepV @U dom K hK P (runAt @U dom K hK P root e r)) with
      | .emit as st' =>
        .emit ((as.filterMap (Ans.rootSpan root)).map (Sigma.mk P.sorts)) ⟨P, root, st'⟩
      | .progress k st' => .progress k ⟨P, root, st'⟩
      | .done fin => .done ((fin.filterMap (Ans.rootSpan root)).map (Sigma.mk P.sorts)) := by
    have hv' : (@Engine.step (engine @U).mirrored (R P.sorts) Rel (Ans (dom P.sorts) P) Cost
        (DerivationKernel.over (dom P.sorts) (K P.sorts) (hK P.sorts) P) st).val =
        Mirror.shownV e next (stepV @U dom K hK P (runAt @U dom K hK P root e r)) := hv
    show (((engine @U).mirrored.costedAt dom K hK).step ⟨P, root, st⟩).val = _
    rw [Engine.costedAt_step_val]
    dsimp only
    rw [hv']
    generalize Mirror.shownV e next (stepV @U dom K hK P (runAt @U dom K hK P root e r)) = w
    cases w <;> rfl
  rw [hstep]
  have hde : RD @U dom K hK P (nodeOf root e) r = RD @U dom K hK P root r := by
    cases e
    · exact done_conv hG hE hL hP hroot r
    · rfl
  cases hd : RD @U dom K hK P root r with
  | false =>
    have hd' := hde.trans hd
    obtain ⟨l, hl, hs⟩ := rt_step_live hIt hd
    obtain rfl := List.append_cancel_left (hl.symm.trans (rootAns_succ r))
    rw [hs, stepV_live @U dom K hK P root hd']
    refine ⟨?_, r + 1, _, hnext _ (by
      show Mirror.after (stepV @U dom K hK P (runAt @U dom K hK P root e r)) = _
      rw [stepV_live @U dom K hK P root hd']; rfl), rfl, rfl⟩
    show (((Mirror.orientV e (gainAt @U dom K hK P root e r)).filterMap
      (Ans.rootSpan root)).map (Sigma.mk P.sorts)).Perm _
    rw [shown_spans hroot e (fun a ha => rootAns_goal (hI e) (r := r + 1)
      (by rw [RA, rootAns_succ]; exact List.mem_append_right _ ha)), ← map_sp]
    exact (gain_perm hG hE hL hP hroot e r).map _
  | true =>
    have hd' := hde.trans hd
    rw [rt_step_done hIt hd, stepV_done @U dom K hK P root hd']
    show (((Mirror.orientV e ((RA @U dom K hK P (nodeOf root e) r).maximaBy
      (covB (dom P.sorts) P))).filterMap (Ans.rootSpan root)).map (Sigma.mk P.sorts)).Perm _
    rw [shown_spans hroot e (fun a ha => rootAns_goal (hI e)
      (List.mem_maximaBy ha)), ← map_sp]
    exact (max_perm hG hE hL hP hroot e r).map _

end runs

/-! ## The first state -/

theorem mirrored_init_val {R : Type} [Answer R] [DecidableEq R] {D : Domain R} (K : Kernel R Cost)
    (hK : K.Refines D) (P : Program) (root : Rel) :
    (@Engine.init (engine @U).mirrored R Rel (Ans D P) Cost
      (DerivationKernel.over D K hK P) root).val =
      ⟨⟨[⟨⟨none, root, none⟩, [], false⟩], 0⟩,
        ⟨[⟨⟨none, root.normConv, none⟩, [], false⟩], 0⟩, true, 0⟩ := by
  at_cost K hK
  rfl

theorem mirrored_init_eq (q : Rel) :
    (Mt @U dom K hK).init P q =
      ⟨P, q.norm, ⟨runAt @U dom K hK P q.norm true 0, runAt @U dom K hK P q.norm false 0,
        true, 0⟩⟩ :=
  congrArg (fun st => (⟨P, q.norm, st⟩ : (engine @U).mirrored.StateAt dom))
    (mirrored_init_val @U (K P.sorts) (hK P.sorts) P q.norm)

/-! ## The theorems -/

section theorems

variable {U dom K hK}
variable (hD : ∀ S : Sorts, S.WellFormed → (dom S).Lawful S.interp)
  (hG : Good @U) (hE : Exact @U)
include hD hG hE

omit hD hG hE in
theorem msim_init {P : Program} {q : Rel} :
    MSim @U dom K hK P q.norm ((Mt @U dom K hK).init P q) ((Rt @U dom K hK).init P q) := by
  rw [mirrored_init_eq, init_eq]
  exact ⟨0, _, ⟨Nat.le_refl 0, rfl, rfl, fun r' hr => absurd hr (Nat.not_lt_zero r')⟩, rfl, rfl⟩

/-- **The mirrored tabled machine shows at each step what the tabled machine
shows**, up to the order of the answers. -/
theorem mirror_trace {P : Program} {q : Rel} (wf : P.WellFormed q) (n : Nat) :
    List.Forall₂ (Shown.Rel fun xs ys => xs.Perm ys)
      ((Mt @U dom K hK).trace ((Mt @U dom K hK).init P q) n)
      ((Rt @U dom K hK).trace ((Rt @U dom K hK).init P q) n) :=
  Runtime.trace_of_sim (R := Mt @U dom K hK) (R' := Rt @U dom K hK)
    (E := fun xs ys => xs.Perm ys) (Sim := MSim @U dom K hK P q.norm)
    (msim_step hG hE (hD _ wf.2.2.1) (progFO_of_wf wf) (root_ok wf)) n _ _
    msim_init

/-- **The mirrored tabled machine is done when the tabled machine is.** -/
theorem mirror_halts {P : Program} {q : Rel} (wf : P.WellFormed q) (n : Nat) :
    (Mt @U dom K hK).Halts ((Mt @U dom K hK).init P q) n ↔
      (Rt @U dom K hK).Halts ((Rt @U dom K hK).init P q) n :=
  Runtime.halts_iff_of_sim (R := Mt @U dom K hK) (R' := Rt @U dom K hK)
    (E := fun xs ys => xs.Perm ys) (Sim := MSim @U dom K hK P q.norm)
    (msim_step hG hE (hD _ wf.2.2.1) (progFO_of_wf wf) (root_ok wf)) n
    msim_init

end theorems

end Tabled

end RwLog
