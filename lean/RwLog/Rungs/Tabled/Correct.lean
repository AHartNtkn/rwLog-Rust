/-
# The tabled machine is correct with any unfolding race that meets its specification

`Tabled.Good U`: the unfolding race `U` meets its specification (`UOk`) at
the derivation kernel of every lawful domain.

For such a race, and a domain that is lawful at well-formed sorts, the tabled
machine `(Tabled.engine U).costedAt dom K hK` is

* complete span by span and pair by pair (`complete`, `pointComplete`);
* honest when it reports that it is done (`honestExhaustion`), and it emits
  no progress certificate (`honestProgress`);
* free of answers covered by an earlier one (`noSubsumed`);
* and its final report is the maximal emitted answers (`finalMaximal`).

Soundness and derivation-generality hold of every engine
(`Rungs/Framework/Derivation.lean`).
-/
import RwLog.Rungs.Tabled.Run
import RwLog.Rungs.Framework.Derivation
import RwLog.Rungs.Framework.Runtime

namespace RwLog

namespace Tabled

open Answer

/-- The unfolding race meets its specification at the derivation kernel of
every lawful domain. -/
def Good (U : Unfolder) : Prop :=
  ∀ {R : Type} [Answer R] [DecidableEq R] (D : Domain R) (P : Program) (K : Kernel R Cost)
    (hK : K.Refines D), D.Lawful P.sorts.interp → ProgFO P →
      UOk D P (@U R Rel (Ans D P) Cost (DerivationKernel.over D K hK P))

theorem filterMap_root {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}
    {root : Rel} : ∀ {l : List (Ans D P)}, (∀ a ∈ l, a.goal = ⟨none, root, none⟩) →
      l.filterMap (Ans.rootSpan root) = l.map (·.span)
  | [], _ => rfl
  | a :: l, h => by
    have ha := h a List.mem_cons_self
    simp only [List.filterMap_cons, List.map_cons, Ans.rootSpan, ha, ite_true]
    exact congrArg _ (filterMap_root fun b hb => h b (List.mem_cons_of_mem _ hb))

variable (U : Unfolder) {R : Sorts → Type} [∀ S, Answer (R S)] [∀ S, DecidableEq (R S)]
  (dom : ∀ S, Domain (R S)) (K : ∀ S, Kernel (R S) Cost) (hK : ∀ S, (K S).Refines (dom S))
  (P : Program) (root : Rel)

/-- The machine. -/
abbrev Rt : Runtime := ((engine @U).costedAt dom K hK).runtime

/-- The unfolding race at the kernel of the program. -/
abbrev UAt : GOracle (R P.sorts) Rel (Ans (dom P.sorts) P) Cost :=
  @U (R P.sorts) Rel (Ans (dom P.sorts) P) Cost
    (DerivationKernel.over (dom P.sorts) (K P.sorts) (hK P.sorts) P)

/-- The tables after `r` rounds. -/
abbrev T (r : Nat) : List (TableOf (R P.sorts) Rel (Ans (dom P.sorts) P)) :=
  tablesAt (K P.sorts) (hK P.sorts) (UAt @U dom K hK P) root r

/-- The state of the machine after `r` rounds. -/
abbrev stAt (r : Nat) : (engine @U).StateAt dom := ⟨P, root, ⟨T @U dom K hK P root r, r⟩⟩

/-- An answer as the machine reports it. -/
def sp (a : Ans (dom P.sorts) P) : (Rt @U dom K hK).Ans :=
  (⟨P.sorts, a.span⟩ : (S : Sorts) × R S)

/-- The answers of the root table after `r` rounds. -/
abbrev RA (r : Nat) : List (Ans (dom P.sorts) P) :=
  rootAns (K P.sorts) (hK P.sorts) (UAt @U dom K hK P) root r

/-- The root table is complete after `r` rounds. -/
abbrev RD (r : Nat) : Bool := rootDone (K P.sorts) (hK P.sorts) (UAt @U dom K hK P) root r

theorem init_val {R : Type} [Answer R] [DecidableEq R] {D : Domain R} (K : Kernel R Cost)
    (hK : K.Refines D) (P : Program) (root : Rel) :
    (@Engine.init (engine @U) R Rel (Ans D P) Cost (DerivationKernel.over D K hK P) root).val =
      ⟨[⟨⟨none, root, none⟩, [], false⟩], 0⟩ := by
  at_cost K hK
  rfl

theorem init_eq (q : Rel) : (Rt @U dom K hK).init P q = stAt @U dom K hK P q.norm 0 :=
  congrArg (fun st => (⟨P, q.norm, st⟩ : (engine @U).StateAt dom))
    (init_val @U (K P.sorts) (hK P.sorts) P q.norm)

theorem map_sp (l : List (Ans (dom P.sorts) P)) :
    (l.map (·.span)).map (Sigma.mk P.sorts) = l.map (sp @U dom K hK P) :=
  List.map_map

section run

variable {U dom K hK P root}
variable (hI : ∀ r, Inv (dom P.sorts) P (T @U dom K hK P root r))
include hI

/-- The answers of the root table are answers of the root goal. -/
theorem rootAns_goal {r : Nat} {a : Ans (dom P.sorts) P} (ha : a ∈ RA @U dom K hK P root r) :
    a.goal = ⟨none, root, none⟩ := by
  rw [RA, rootAns_eq] at ha
  have := ((hI r).ok _ (List.getElem_mem (root_pos r))).2 a ha
  rw [this, root_goal]; rfl

/-- A step while the root table is incomplete. -/
theorem rt_step_live {r : Nat} (h : RD @U dom K hK P root r = false) :
    ∃ l, RA @U dom K hK P root (r + 1) = RA @U dom K hK P root r ++ l ∧
      (Rt @U dom K hK).step (stAt @U dom K hK P root r) =
        .emit (l.map (sp @U dom K hK P)) (stAt @U dom K hK P root (r + 1)) := by
  refine ⟨_, rootAns_succ r, ?_⟩
  have e2 := step_live (K := K P.sorts) (hK := hK P.sorts) (U := UAt @U dom K hK P) (root := root) h
  show (((engine @U).costedAt dom K hK).step (stAt @U dom K hK P root r)).val = _
  rw [Engine.costedAt_step_val]
  dsimp only [stAt, engine]
  rw [e2]
  dsimp only
  rw [filterMap_root (fun a ha => rootAns_goal hI (r := r + 1)
    (by rw [RA, rootAns_succ]; exact List.mem_append_right _ ha))]
  exact congrArg (fun x => (StepOf.emit x (stAt @U dom K hK P root (r + 1)) :
    StepOf ((S : Sorts) × R S) ((engine @U).StateAt dom))) (map_sp @U dom K hK P _)

/-- The step when the root table is complete. -/
theorem rt_step_done {r : Nat} (h : RD @U dom K hK P root r = true) :
    (Rt @U dom K hK).step (stAt @U dom K hK P root r) =
      .done (((RA @U dom K hK P root r).maximaBy (covB (dom P.sorts) P)).map (sp @U dom K hK P)) := by
  have e2 := step_done (K := K P.sorts) (hK := hK P.sorts) (U := UAt @U dom K hK P) (root := root) h
  show (((engine @U).costedAt dom K hK).step (stAt @U dom K hK P root r)).val = _
  rw [Engine.costedAt_step_val]
  dsimp only [stAt, engine]
  rw [e2]
  dsimp only
  rw [filterMap_root (fun a ha => rootAns_goal hI (List.mem_maximaBy ha))]
  exact congrArg (fun x => (StepOf.done x :
    StepOf ((S : Sorts) × R S) ((engine @U).StateAt dom))) (map_sp @U dom K hK P _)

/-- A run while the root table is incomplete emits what the root table
gains. -/
theorem run_live : ∀ (j r m : Nat), (∀ i < j, RD @U dom K hK P root (r + i) = false) →
    ∃ l, RA @U dom K hK P root (r + j) = RA @U dom K hK P root r ++ l ∧
      (Rt @U dom K hK).run (stAt @U dom K hK P root r) (j + m) =
        ((l.map (sp @U dom K hK P) : List (Rt @U dom K hK).Ans) ++
            ((Rt @U dom K hK).run (stAt @U dom K hK P root (r + j)) m).1,
          ((Rt @U dom K hK).run (stAt @U dom K hK P root (r + j)) m).2)
  | 0, r, m, _ => ⟨[], by simp, by rw [Nat.zero_add]; rfl⟩
  | j + 1, r, m, h => by
    have h0' := h 0 (Nat.succ_pos j)
    rw [Nat.add_zero] at h0'
    obtain ⟨l₁, h₁, hs⟩ := rt_step_live hI h0'
    obtain ⟨l₂, h₂, hr⟩ := run_live j (r + 1) m fun i hi => by
      have := h (i + 1) (Nat.succ_lt_succ hi)
      rwa [show r + (i + 1) = r + 1 + i by omega] at this
    refine ⟨l₁ ++ l₂, ?_, ?_⟩
    · rw [show r + (j + 1) = r + 1 + j by omega, h₂, h₁, List.append_assoc]
    · rw [show j + 1 + m = (j + m) + 1 by omega, (Rt @U dom K hK).run_succ_emit hs, hr,
        show r + (j + 1) = r + 1 + j by omega]
      refine Prod.ext ?_ rfl
      show _ ++ (_ ++ _) = _
      rw [List.map_append, List.append_assoc]

/-- A run from the first state: while the root table is incomplete it has
emitted the answers of the root table; once the root table is complete it has
emitted them and reported the maximal ones. -/
theorem run_cases (n : Nat) :
    ((∀ j < n, RD @U dom K hK P root j = false) ∧
      (Rt @U dom K hK).run (stAt @U dom K hK P root 0) n =
        ((RA @U dom K hK P root n).map (sp @U dom K hK P), none)) ∨
    ∃ j < n, RD @U dom K hK P root j = true ∧
      (Rt @U dom K hK).run (stAt @U dom K hK P root 0) n =
        ((RA @U dom K hK P root j).map (sp @U dom K hK P),
          some (((RA @U dom K hK P root j).maximaBy (covB (dom P.sorts) P)).map (sp @U dom K hK P))) := by
  have h0 : RA @U dom K hK P root 0 = [] := rfl
  by_cases h : ∃ j, j < n ∧ RD @U dom K hK P root j = true
  · right
    classical
    obtain ⟨j, hj, hmin'⟩ : ∃ j, (j < n ∧ RD @U dom K hK P root j = true) ∧
        ∀ i < j, ¬(i < n ∧ RD @U dom K hK P root i = true) :=
      ⟨Nat.find h, Nat.find_spec h, fun i hi => Nat.find_min h hi⟩
    have hmin : ∀ i < j, RD @U dom K hK P root (0 + i) = false := fun i hi => by
      rw [Nat.zero_add]
      cases hd : RD @U dom K hK P root i with
      | false => rfl
      | true => exact absurd ⟨Nat.lt_trans hi hj.1, hd⟩ (hmin' i hi)
    obtain ⟨m, hm⟩ : ∃ m, n = j + (m + 1) := ⟨n - j - 1, by omega⟩
    subst hm
    obtain ⟨l, hl, hr⟩ := run_live hI j 0 (m + 1) hmin
    rw [Nat.zero_add] at hl hr
    rw [h0, List.nil_append] at hl
    refine ⟨j, hj.1, hj.2, ?_⟩
    rw [hr, (Rt @U dom K hK).run_succ_done (rt_step_done hI hj.2), hl]
    simp
  · left
    have hall : ∀ j < n, RD @U dom K hK P root j = false := fun j hj => by
      cases hd : RD @U dom K hK P root j with
      | false => rfl
      | true => exact absurd ⟨j, hj, hd⟩ h
    refine ⟨hall, ?_⟩
    obtain ⟨l, hl, hr⟩ := run_live hI n 0 0 fun i hi => by rw [Nat.zero_add]; exact hall i hi
    rw [Nat.zero_add, Nat.add_zero] at hr
    rw [Nat.zero_add, h0, List.nil_append] at hl
    rw [hr, hl]
    simp [Runtime.run]

/-- The machine emits no progress certificate. -/
theorem trace_no_level : ∀ (n r : Nat), ∀ x ∈ (Rt @U dom K hK).trace (stAt @U dom K hK P root r) n,
    ∀ k, x ≠ .level k
  | 0, _, x, hx, _ => by simp [Runtime.trace] at hx
  | n + 1, r, x, hx, k => by
    cases hd : RD @U dom K hK P root r with
    | false =>
      obtain ⟨l, -, hs⟩ := rt_step_live hI hd
      rw [(Rt @U dom K hK).trace_succ_emit hs] at hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact fun h => by cases h
      · exact trace_no_level n (r + 1) x hx k
    | true =>
      rw [(Rt @U dom K hK).trace_succ_done (rt_step_done hI hd)] at hx
      obtain rfl : x = _ := by simpa using hx
      exact fun h => by cases h

end run

/-! ## The theorems -/

/-- Every pair a query relates is a pair of a derivation of its normal form,
at some depth of unfolding. -/
theorem pairs_gdn {P : Program} {q : Rel} {p : GTerm × GTerm} (hp : p ∈ P.pairs q) :
    ∃ k G, G ∈ GDn P k q.norm ∧ p ∈ G.at P.sorts.interp := by
  unfold ProgramOf.pairs at hp
  rw [ProgramOf.semAt_eq, sem_eq_sUnion_gd] at hp
  obtain ⟨S, ⟨G, hG, hmem⟩, hM⟩ := hp
  rw [← gd_norm] at hG
  obtain ⟨k, hk⟩ := mem_gd_iff.1 hG
  exact ⟨k, G, hk, S, hmem, hM⟩

section theorems

variable {U dom K hK}
variable (hD : ∀ S : Sorts, S.WellFormed → (dom S).Lawful S.interp) (hU : Good @U)

omit [∀ S, Answer (R S)] [∀ S, DecidableEq (R S)] in
theorem root_ok {P : Program} {q : Rel} (wf : P.WellFormed q) :
    GoalOk (dom P.sorts) (⟨none, q.norm, none⟩ : GoalOf (R P.sorts) Rel) :=
  ⟨isBound_none _, isBound_none _, normal_norm q,
    RelOf.FO.norm fun s hs => wf.2.2.2 s (List.mem_append_left _ hs)⟩

theorem progFO_of_wf {P : Program} {q : Rel} (wf : P.WellFormed q) : ProgFO P :=
  fun s hs => wf.2.2.2 s (List.mem_append_right _ hs)

include hD hU in
theorem inv_of_wf {P : Program} {q : Rel} (wf : P.WellFormed q) (r : Nat) :
    Inv (dom P.sorts) P (T @U dom K hK P q.norm r) :=
  inv_at (hD _ wf.2.2.1) (progFO_of_wf wf)
    (hU (dom P.sorts) P (K P.sorts) (hK P.sorts) (hD _ wf.2.2.1) (progFO_of_wf wf)) (root_ok wf) r

include hD hU in
/-- A derivation of the query is covered by one emitted answer. -/
theorem emitted_cov {P : Program} {q : Rel} (wf : P.WellFormed q) {k : Nat} {G : GRel}
    (hG : G ∈ GDn P k q.norm) (hne : (G.at P.sorts.interp).Nonempty) :
    ∃ n, ∃ b ∈ (Rt @U dom K hK).emitted ((Rt @U dom K hK).init P q) n,
      G.at P.sorts.interp ⊆ den P.sorts.interp b := by
  have hI := inv_of_wf (K := K) (hK := hK) hD hU wf
  have hL := hD _ wf.2.2.1
  have hUk := hU (dom P.sorts) P (K P.sorts) (hK P.sorts) hL (progFO_of_wf wf)
  have e : ∀ r, pairsOf P ((T @U dom K hK P q.norm r)[0]'(root_pos r)).goal G =
      G.at P.sorts.interp := fun r => by rw [root_goal]; exact wrapAt_none _
  obtain ⟨r', -, hi', a, ha, hsub⟩ := eventually (K := K P.sorts) (hK := hK P.sorts)
    (U := UAt @U dom K hK P) (root := q.norm) hL (progFO_of_wf wf) hUk (root_ok wf) k _ 0 0
    (root_pos 0) rfl G (by rw [root_goal]; exact hG) (by rw [e]; exact hne)
  rw [e] at hsub
  rw [init_eq]
  rcases run_cases hI r' with ⟨-, hr⟩ | ⟨j, hj, hd, hr⟩
  · refine ⟨r', sp @U dom K hK P a, ?_, hsub⟩
    rw [show (Rt @U dom K hK).emitted (stAt @U dom K hK P q.norm 0) r' = _ from
      congrArg Prod.fst hr]
    exact List.mem_map_of_mem (by rw [RA, rootAns_eq]; exact ha)
  · rw [RD, rootDone_eq] at hd
    obtain ⟨a', ha', hsub'⟩ := (hI j).full _ (List.getElem_mem (root_pos j)) hd k G
      (by rw [root_goal]; exact hG) (by rw [e]; exact hne)
    rw [e] at hsub'
    refine ⟨r', sp @U dom K hK P a', ?_, hsub'⟩
    rw [show (Rt @U dom K hK).emitted (stAt @U dom K hK P q.norm 0) r' = _ from
      congrArg Prod.fst hr]
    exact List.mem_map_of_mem (by rw [RA, rootAns_eq]; exact ha')

include hD hU in
/-- **The tabled machine is complete**: every derivable span that relates a
pair is covered by one emitted answer. -/
theorem complete : (Rt @U dom K hK).Complete := fun P q wf s hs => by
  by_cases hne : (s.denAt P.sorts.interp).Nonempty
  · right
    have hG : s.den ∈ GD P q.norm := by
      rw [gd_norm]; exact (derives_iff_derivesG.1 ⟨s, hs, rfl⟩).1
    obtain ⟨k, hk⟩ := mem_gd_iff.1 hG
    rw [Span.denAt_eq] at hne
    obtain ⟨n, b, hb, hsub⟩ := emitted_cov (K := K) (hK := hK) hD hU wf hk hne
    exact ⟨n, b, hb, by
      show s.denAt P.sorts.interp ⊆ _
      rw [Span.denAt_eq]; exact hsub⟩
  · exact .inl (Set.not_nonempty_iff_eq_empty.1 hne)

include hD hU in
/-- **The tabled machine is complete pair by pair.** -/
theorem pointComplete : (Rt @U dom K hK).PointComplete := fun P q wf p hp => by
  obtain ⟨k, G, hG, hpG⟩ := pairs_gdn hp
  obtain ⟨n, b, hb, hsub⟩ := emitted_cov (K := K) (hK := hK) hD hU wf hG ⟨p, hpG⟩
  exact ⟨n, b, hb, hsub hpG⟩

include hD hU in
/-- **When the tabled machine reports that it is done, its answers relate
every pair the query relates.** -/
theorem honestExhaustion : (Rt @U dom K hK).HonestExhaustion := fun P q wf n hn => by
  have hI := inv_of_wf (K := K) (hK := hK) hD hU wf
  apply Set.Subset.antisymm
  · intro p hp
    obtain ⟨k, G, hG, hpG⟩ := pairs_gdn hp
    rw [init_eq] at hn ⊢
    rcases run_cases hI n with ⟨-, hr⟩ | ⟨j, hj, hd, hr⟩
    · simp [Runtime.Halts, Runtime.final, hr] at hn
    · rw [RD, rootDone_eq] at hd
      have e : pairsOf P ((T @U dom K hK P q.norm j)[0]'(root_pos j)).goal G =
          G.at P.sorts.interp := by rw [root_goal]; exact wrapAt_none _
      obtain ⟨a, ha, hsub⟩ := (hI j).full _ (List.getElem_mem (root_pos j)) hd k G
        (by rw [root_goal]; exact hG) (by rw [e]; exact ⟨p, hpG⟩)
      rw [e] at hsub
      refine Set.mem_iUnion₂.2 ⟨sp @U dom K hK P a, ?_, hsub hpG⟩
      rw [show (Rt @U dom K hK).emitted (stAt @U dom K hK P q.norm 0) n = _ from
        congrArg Prod.fst hr]
      exact List.mem_map_of_mem (by rw [RA, rootAns_eq]; exact ha)
  · intro p hp
    obtain ⟨a, ha, hpa⟩ := Set.mem_iUnion₂.1 hp
    exact Engine.sound (engine @U) dom K hK hD P q wf n a ha hpa

include hD hU in
/-- **The tabled machine emits no progress certificate**, so every one it
emits is true. -/
theorem honestProgress : (Rt @U dom K hK).HonestProgress := fun P q wf k n hc => by
  have hI := inv_of_wf (K := K) (hK := hK) hD hU wf
  rw [init_eq] at hc
  exact absurd rfl (trace_no_level hI (k + 1) 0 _ (List.mem_of_getElem? hc) n)

include hD hU in
/-- What a run has emitted is the answers of the root table in some round. -/
theorem emitted_eq {P : Program} {q : Rel} (wf : P.WellFormed q) (n : Nat) :
    ∃ j, (Rt @U dom K hK).emitted ((Rt @U dom K hK).init P q) n =
      (RA @U dom K hK P q.norm j).map (sp @U dom K hK P) := by
  have hI := inv_of_wf (K := K) (hK := hK) hD hU wf
  rw [init_eq]
  rcases run_cases hI n with ⟨-, hr⟩ | ⟨j, -, -, hr⟩
  · exact ⟨n, congrArg Prod.fst hr⟩
  · exact ⟨j, congrArg Prod.fst hr⟩

theorem nocov_at (P : Program) (root : Rel) :
    ∀ r, NoCov (dom P.sorts) P (T @U dom K hK P root r)
  | 0 => fun t ht => by
    obtain rfl : t = ⟨⟨none, root, none⟩, [], false⟩ := by simpa [T, tablesAt] using ht
    exact List.Pairwise.nil
  | r + 1 => nocov_next _ _ r (nocov_at P root r)

include hD hU in
/-- **No answer the tabled machine emits is covered by an earlier one.** -/
theorem noSubsumed : (Rt @U dom K hK).NoSubsumed := fun P q wf n => by
  obtain ⟨j, hj⟩ := emitted_eq (K := K) (hK := hK) hD hU wf n
  rw [hj, List.pairwise_map]
  have := nocov_at (U := @U) (dom := dom) (K := K) (hK := hK) P q.norm j _
    (List.getElem_mem (root_pos j))
  rw [← rootAns_eq] at this
  refine this.imp fun {y x} h hc => ?_
  have := (covB_iff (hD _ wf.2.2.1) y x).2 hc
  rw [h] at this; cases this

include hD hU in
/-- **The final report of the tabled machine is the maximal emitted
answers.** -/
theorem finalMaximal : (Rt @U dom K hK).FinalMaximal := fun P q wf n fin hfin => by
  have hI := inv_of_wf (K := K) (hK := hK) hD hU wf
  have hL := hD _ wf.2.2.1
  rw [init_eq] at hfin ⊢
  rcases run_cases hI n with ⟨-, hr⟩ | ⟨j, -, -, hr⟩
  · rw [show (Rt @U dom K hK).final (stAt @U dom K hK P q.norm 0) n = _ from
      congrArg Prod.snd hr] at hfin
    cases hfin
  · rw [show (Rt @U dom K hK).final (stAt @U dom K hK P q.norm 0) n = _ from
      congrArg Prod.snd hr] at hfin
    obtain rfl := Option.some.inj hfin
    rw [show (Rt @U dom K hK).emitted (stAt @U dom K hK P q.norm 0) n = _ from
      congrArg Prod.fst hr]
    refine ⟨fun a ha => ?_, fun a ha => ?_, ?_⟩
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
      exact List.mem_map_of_mem (List.mem_maximaBy hx)
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
      obtain ⟨z, hz, hzx⟩ := List.maximaBy_covers (covB_refl hL) (covB_trans hL) hx
      exact ⟨_, List.mem_map_of_mem hz, (covB_iff hL z x).1 hzx⟩
    · rw [List.pairwise_map]
      refine (List.maximaBy_pairwise (cov := covB (dom P.sorts) P) _).imp fun {y x} h => ?_
      refine ⟨fun hc => ?_, fun hc => ?_⟩
      · have := (covB_iff hL y x).2 hc
        rw [h.1] at this; cases this
      · have := (covB_iff hL x y).2 hc
        rw [h.2] at this; cases this

end theorems

end Tabled

end RwLog
