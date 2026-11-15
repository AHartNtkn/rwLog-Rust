/-
# The engine halts on an input exactly when it halts on the input chosen

A machine run on one orientation of its input (`CostedRuntime.oriented`)
runs on the program with its bodies in normal form or on the mirrored
program, and on the query, its converse, its mirror image, or the union of a
node with its converse (`orient`, `Trusted/Cost.lean`). The symmetric engine
halts on the input exactly when it halts on the input chosen (`sameHalt`).

Each of the choices is a link of two programs (`Mirror`,
`Rungs/Symmetric/Mirror.lean`), along which a root that completes has an
image that completes:

* the same program, for the converse (`mirror_same`);
* the mirrored program, for the mirror image (`mirror_dual`);
* the program with its bodies in normal form, which reads the same bodies
  (`mirror_normed`).

The union of a node with its converse is another matter: its members are the
members of the node and of the converse. A goal completes when its members
as a union complete (`completes_of_members`), and the members of a goal of a
certificate are goals of the certificate (`FCert.member`); so a root
completes if each of its members is a member of a root that completes
(`done_members`).
-/
import RwLog.Rungs.Symmetric.Mirror
import RwLog.Rungs.Tabled.Symmetry
import RwLog.Rungs.Framework.OrientedKeeps

namespace RwLog

namespace Symmetric

open Answer Saturation Goals Unfold
open Tabled (gmap smap)

/-! ## A goal and its members -/

section members

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}
  {U : GOracle R Rel (Ans D P) Cost}
  {C : GoalOf R Rel → Prop} {ρ : GoalOf R Rel → Nat} {A : GoalOf R Rel → List (Ans D P)}

/-- **The members of a goal of a certificate, read as a union, are goals of
the certificate.** -/
theorem FCert.member (h : FCert U C ρ A) {g : GoalOf R Rel} (hg : C g) {x : Rel}
    (hx : x ∈ g.node.unionParts) : C ⟨g.lb, x, g.rb⟩ := by
  obtain ⟨lb, n, rb⟩ := g
  have one : n.unionParts = [n] → C ⟨lb, x, rb⟩ := fun e => by
    rw [e] at hx
    obtain rfl := List.mem_singleton.1 hx
    exact hg
  cases n with
  | zero => cases hx
  | span _ => exact one rfl
  | call _ => exact one rfl
  | seq _ _ => exact one rfl
  | and _ _ => exact one rfl
  | conv _ => exact one rfl
  | or a c =>
    rcases h.why _ hg with ⟨hh, -⟩ | hw
    · simp [hasRace, RelOf.view, NodeView.forget] at hh
    cases hw with
    | span hs =>
      obtain ⟨s, hs⟩ := hs
      cases hs
    | copy c' h1 h2 hs =>
      cases c' with
      | true =>
        obtain ⟨bd, hbd⟩ := h1 rfl
        simp [Charged.bodyOf] at hbd
      | false => exact (hs x hx).1
    | join k L Rg hsp _ _ =>
      cases k with
      | seq =>
        obtain ⟨xs, i, l, r, hv, -⟩ := hsp
        simp [RelOf.view] at hv
      | and =>
        obtain ⟨xs, i, l, r, hv, -⟩ := hsp
        simp [RelOf.view] at hv
    | push k L Rg left hsp _ _ =>
      cases k with
      | seq =>
        obtain ⟨xs, i, l, r, hv, -⟩ := hsp
        simp [RelOf.view] at hv
      | and =>
        obtain ⟨xs, i, l, r, hv, -⟩ := hsp
        simp [RelOf.view] at hv
    | check L Rg hsp _ _ _ _ =>
      obtain ⟨xs, i, l, r, hv, -⟩ := hsp
      simp [RelOf.view] at hv

variable (hL : D.Lawful P.sorts.interp)
include hL

/-- **A goal completes when its members as a union complete**, each with
answers that cover every answer of it. -/
theorem completes_of_members {g : GoalOf R Rel} (hg : GoalOk D g)
    (hmem : ∀ x ∈ g.node.unionParts, ∃ Ax : List (Ans D P),
      Completes U ⟨g.lb, x, g.rb⟩ ∧ (∀ a ∈ Ax, a.goal = toGoal ⟨g.lb, x, g.rb⟩) ∧
      ∀ y : Ans D P, y.goal = toGoal ⟨g.lb, x, g.rb⟩ → ∃ f ∈ Ax, covB D P f y = true) :
    Completes U g := by
  classical
  by_cases hu : ∃ xs, g.node.view = .union xs
  swap
  · have self : g.node.unionParts = [g.node] → Completes U g := fun e => by
      obtain ⟨Ax, hc, -⟩ := hmem g.node (by rw [e]; exact List.mem_singleton_self _)
      exact hc
    obtain ⟨lb, n, rb⟩ := g
    cases n with
    | zero => exact absurd ⟨_, rfl⟩ hu
    | or a c => exact absurd ⟨_, rfl⟩ hu
    | span _ => exact self rfl
    | call _ => exact self rfl
    | seq _ _ => exact self rfl
    | and _ _ => exact self rfl
    | conv _ => exact self rfl
  have hmem' : ∀ x, ∃ Ax : List (Ans D P), x ∈ g.node.unionParts →
      Completes U ⟨g.lb, x, g.rb⟩ ∧ (∀ a ∈ Ax, a.goal = toGoal ⟨g.lb, x, g.rb⟩) ∧
      ∀ y : Ans D P, y.goal = toGoal ⟨g.lb, x, g.rb⟩ → ∃ f ∈ Ax, covB D P f y = true := by
    intro x
    by_cases hx : x ∈ g.node.unionParts
    · obtain ⟨Ax, h⟩ := hmem x hx
      exact ⟨Ax, fun _ => h⟩
    · exact ⟨[], fun h => absurd h hx⟩
  choose Af hAf using hmem'
  let Cg : GoalOf R Rel → Prop := fun h => h = g ∨ ∃ x ∈ g.node.unionParts, h = ⟨g.lb, x, g.rb⟩
  let ρg : GoalOf R Rel → Nat := fun h => if h = g then 1 else 0
  let Ag : GoalOf R Rel → List (Ans D P) := fun h =>
    if h = g then g.node.unionParts.flatMap fun x => (Af x).filterMap (amap P false g)
    else Af h.node
  have hAg : Ag g = g.node.unionParts.flatMap fun x => (Af x).filterMap (amap P false g) := by
    simp only [Ag, ↓reduceIte]
  have hAm : ∀ h, h ≠ g → Ag h = Af h.node := fun h hne => by simp only [Ag, hne, ↓reduceIte]
  have hC : Cert U Cg ρg Ag := by
    refine ⟨⟨g :: g.node.unionParts.map fun x => ⟨g.lb, x, g.rb⟩, ?_⟩, ?_, ?_, ?_⟩
    · rintro h (rfl | ⟨x, hx, rfl⟩)
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (List.mem_map.2 ⟨x, hx, rfl⟩)
    · intro h hh a ha
      by_cases e : h = g
      · subst e
        rw [hAg] at ha
        obtain ⟨x, -, ha⟩ := List.mem_flatMap.1 ha
        obtain ⟨a0, -, ea⟩ := List.mem_filterMap.1 ha
        exact (amap_spec ea).1
      · rw [hAm h e] at ha
        rcases hh with rfl | ⟨x, hx, rfl⟩
        · exact absurd rfl e
        · exact (hAf x hx).2.1 a ha
    · intro h hh y hy
      by_cases e : h = g
      · subst e
        have hv : Valid D P (toGoal h) y.span := hy ▸ y.valid
        obtain ⟨s, hs, hden⟩ := hv.2 hL
        have hG : s.den ∈ ⋃ x ∈ h.node.unionParts, GD P x := by
          rw [gd_unionParts]
          exact hs.derivesG
        obtain ⟨x, hx, hGx⟩ := Set.mem_iUnion₂.1 hG
        obtain ⟨s', hs', es⟩ := derives_iff_derivesG.2 ⟨hGx, s.den_nonempty⟩
        have hvx : Valid D P (toGoal ⟨h.lb, x, h.rb⟩) y.span :=
          ⟨hv.1, fun _ => ⟨s', hs', by rw [es]; exact hden⟩⟩
        obtain ⟨f, hf, hfy⟩ := (hAf x hx).2.2 ⟨_, _, hvx⟩ rfl
        have hfg := (hAf x hx).2.1 f hf
        have hv0 : Valid D P (toGoal ⟨h.lb, x, h.rb⟩) f.span := by
          rw [← hfg]
          exact f.valid
        have hfv : Valid D P (toGoal h) (smap false f.span) :=
          Valid.inj (lb := h.lb) (rb := h.rb) hv0 hx
        refine ⟨⟨toGoal h, smap false f.span, hfv⟩, ?_, hfy⟩
        rw [hAg]
        exact List.mem_flatMap.2 ⟨x, hx, List.mem_filterMap.2
          ⟨f, hf, by unfold amap; simp only [hfv, ↓reduceDIte]⟩⟩
      · rw [hAm h e]
        rcases hh with rfl | ⟨x, hx, rfl⟩
        · exact absurd rfl e
        · exact (hAf x hx).2.2 y hy
    · intro h hh
      by_cases e : h = g
      · subst e
        refine .inr (.copy false (fun hc => by cases hc) (fun _ => hu) fun x hx => ?_)
        refine ⟨.inr ⟨x, hx, rfl⟩, ?_⟩
        show (if _ then 1 else 0) ≤ (if h = h then 1 else 0)
        simp only [↓reduceIte]
        split <;> omega
      · rcases hh with rfl | ⟨x, hx, rfl⟩
        · exact absurd rfl e
        · exact .inl (hAf x hx).1
  exact hC.completes hL (.inl rfl)

variable {K : Kernel R Cost} {hK : K.Refines D}

/-- **A root completes if each of its members, as a union, is a member of a
root that completes.** -/
theorem done_members (hP : ProgFO P) (hU : UOk D P U) {roots : List Rel} {root : Rel}
    (hroots : ∀ c ∈ roots, Normal c ∧ c.FO ∧ EvDone (stateAt K hK P c U) 0)
    (hn : Normal root) (hfo : root.FO)
    (hsub : ∀ x ∈ root.unionParts, ∃ c ∈ roots, x ∈ c.unionParts) :
    EvDone (stateAt K hK P root U) 0 := by
  have hτ := isRun (K := K) (hK := hK) hL hP hU hn hfo
  have hg : GoalOk D (⟨none, root, none⟩ : GoalOf R Rel) :=
    ⟨isBound_none D, isBound_none D, hn, hfo⟩
  refine completes_of_members hL hg (fun x hx => ?_) _ hτ (fun r j => nocov_stateAt r j) 0 0
    root_goal0
    (hτ.opened_of_settled root_goal0 fun r' => ⟨r', Nat.le_refl _, (hτ.req.req r').root⟩)
  obtain ⟨c, hc, hxc⟩ := hsub x hx
  obtain ⟨hcn, hcfo, r, hr⟩ := hroots c hc
  have hσ := isRun (K := K) (hK := hK) hL hP hU hcn hcfo
  obtain ⟨ρ, A, hC⟩ := hσ.fcert hL r
  have hx' := hC.member (g := ⟨none, c, none⟩) ⟨0, hσ.goal_le (Nat.zero_le r) root_goal0, hr⟩ hxc
  exact ⟨A _, hC.cert.completes hL hx', hC.goal _ hx', hC.full _ hx'⟩

end members

/-- The members of the normal form of a union of two nodes are the members
of the two. -/
theorem mem_unionParts_or {a c z : Rel} (ha : Normal a) (hc : Normal c) :
    z ∈ (RelOf.or a c).norm.unionParts ↔ z ∈ a.unionParts ∨ z ∈ c.unionParts := by
  rw [(normal_norm _).mem_unionParts, ha.mem_unionParts, hc.mem_unionParts]
  constructor
  · rintro ⟨h, hz⟩
    have := (mem_orBranches_normB_or false hz).1 h
    rw [ha.normB_false, hc.normB_false] at this
    exact this.imp (fun h => ⟨h, hz⟩) fun h => ⟨h, hz⟩
  · rintro (⟨h, hz⟩ | ⟨h, hz⟩)
    · exact ⟨(mem_orBranches_normB_or false hz).2 (.inl (by rw [ha.normB_false]; exact h)), hz⟩
    · exact ⟨(mem_orBranches_normB_or false hz).2 (.inr (by rw [hc.normB_false]; exact h)), hz⟩

/-! ## The three links -/

variable {U : Unfolder} {R : Sorts → Type} [∀ S, Answer (R S)] [∀ S, DecidableEq (R S)]
  {dom : ∀ S, Domain (R S)} {K : ∀ S, Kernel (R S) Cost} {hK : ∀ S, (K S).Refines (dom S)}

/-- The program with its bodies in normal form reads the bodies the program
reads. -/
theorem bodyOf_normed (P : Program) (e : Rel) :
    Charged.bodyOf P.normed e = Charged.bodyOf P e := by
  unfold Charged.bodyOf
  split
  · rw [ProgramOf.normed_body, norm_norm]
  · rw [ProgramOf.normed_body, normConv_norm]
  · rfl

/-- So its unfoldings are the unfoldings of the program. -/
theorem se_normed (P : Program) (M : Interp) : ∀ (d : Nat) (A : Set GTerm) (e : Rel)
    (B : Set GTerm), SE P.normed M d A e B = SE P M d A e B := by
  intro d
  induction d with
  | zero => intro A e B; rfl
  | succ d ih =>
    intro A e B
    simp only [SE, bodyOf_normed, ih]

section links

variable (hG : RwLog.Good @U) (hE : Exact @U)
include hG hE

/-- A program is linked to itself, for the converse of every node or for
every node as it is. -/
theorem mirror_same {P : Program} (hL : (dom P.sorts).Lawful P.sorts.interp) (hP : ProgFO P)
    (b : Bool) :
    Mirror (dom P.sorts) P P b false (UAt @U dom K hK P) (UAt @U dom K hK P) :=
  ⟨Tabled.twin_same (K := K) (hK := hK) hG hG hE hE hL hP b, rfl, fun e _ => gd_normB P b e⟩

/-- A program is linked to the mirrored program, for the mirror image of
every node or its converse. -/
theorem mirror_dual {P : Program} (hL : (dom P.sorts).Lawful P.sorts.interp) (hP : ProgFO P)
    (hP' : ProgFO P.dual) (b : Bool) :
    Mirror (dom P.sorts) P P.dual b true (UAt @U dom K hK P) (UAt @U dom K hK P.dual) := by
  refine ⟨Tabled.twin_dual (K := K) (hK := hK) hG hG hE hE hL hP hP' b, rfl, fun e _ => ?_⟩
  have e1 : nmap b true e = normB (!b) e.dual := by
    rw [normB_dual, Bool.not_not]
    rfl
  rw [e1, gd_normB, gd_dual]
  cases b <;> simp [inv_image_inv_image]

/-- A program is linked to the program with its bodies in normal form, for
every node as it is. -/
theorem mirror_normed {P : Program} (hL : (dom P.sorts).Lawful P.sorts.interp) (hP : ProgFO P) :
    Mirror (dom P.sorts) P P.normed false false (UAt @U dom K hK P)
      (UAt @U dom K hK P.normed) := by
  have hPn := hP.normed
  have ex := hE (dom P.sorts) P (K P.sorts) (hK P.sorts) hL hP
  have ex' := hE (dom P.sorts) P.normed (K P.sorts) (hK P.sorts) hL hPn
  have hmap : ∀ (Q : Program) (e : Rel),
      (Charged.bodyOf Q e).map (nmap false false) = Charged.bodyOf Q e := by
    intro Q e
    cases h : Charged.bodyOf Q e with
    | none => rfl
    | some bd => exact congrArg some (nmap_ff (bodyOf_normal h))
  refine ⟨⟨hL, hL, hP, hPn, hG (dom P.sorts) P (K P.sorts) (hK P.sorts) hL hP,
    hG (dom P.sorts) P.normed (K P.sorts) (hK P.sorts) hL hPn,
    Tabled.Link.of_ex hL rfl ex ex' (fun e he => ?_) (fun d e he A B => ?_)
      (fun d e he A B X => ?_),
    Tabled.Link.of_ex (P := P.normed) (P' := P) hL rfl ex' ex (fun e he => ?_)
      (fun d e he A B => ?_) (fun d e he A B X => ?_)⟩, rfl, fun e he => ?_⟩
  · rw [nmap_ff he, bodyOf_normed, hmap]
  · simp only [nmap_ff he, Final, se_normed, Bool.false_eq_true, ↓reduceIte]
  · simp only [nmap_ff he, se_normed, Bool.false_eq_true, ↓reduceIte]
  · rw [nmap_ff he, bodyOf_normed, hmap]
  · simp only [nmap_ff he, Final, se_normed, Bool.false_eq_true, ↓reduceIte]
  · simp only [nmap_ff he, se_normed, Bool.false_eq_true, ↓reduceIte]
  · rw [nmap_ff he]
    exact gd_normed P e

end links

/-! ## Halting on each of the inputs -/

/-- A fact of the root picked that holds of every candidate, and of a node
exactly when of its union with its converse. -/
theorem pick_iff (Pn : Program) (T : Rel → Prop) (H : Prop) (f : Rel × Bool)
    (r : List (Rel × Bool)) (h : ∀ c ∈ f :: r, T c.1 ↔ H)
    (hu : ∀ c ∈ f :: r, T c.1 ↔ T (RelOf.or c.1 c.1.normConv).norm) :
    T (pick Pn f r).root ↔ H := by
  obtain ⟨c, hc, hcm⟩ : ∃ c ∈ f :: r, c.1 = leastRel f.1 (r.map Prod.fst) := by
    rcases List.mem_cons.1 (leastRel_mem f.1 (r.map Prod.fst)) with h | h
    · exact ⟨f, by simp, h.symm⟩
    · obtain ⟨c, hc, e⟩ := List.mem_map.1 h
      exact ⟨c, List.mem_cons_of_mem _ hc, e⟩
  unfold pick
  dsimp only
  split
  · rw [← hcm]
    exact h c hc
  · split
    · rw [← hcm]
      exact h c hc
    · rw [← hcm]
      exact (hu c hc).symm.trans (h c hc)

section theorems

variable (hD : ∀ S : Sorts, S.WellFormed → (dom S).Lawful S.interp)
  (hG : RwLog.Good @U) (hE : Exact @U)
include hD hG hE

/-- The engine halts on a query in a program exactly when it halts on its
normal form in the program with its bodies in normal form. -/
theorem terminates_normed {P : Program} {q : Rel} (wf : P.WellFormed q) :
    (Rt @U dom K hK).Terminates P q ↔ (Rt @U dom K hK).Terminates P.normed q.norm := by
  rw [terminates_iff (K := K) (hK := hK) hD hG wf,
    terminates_iff (K := K) (hK := hK) hD hG wf.normed, norm_norm]
  have h := (mirror_normed (K := K) (hK := hK) hG hE (hD _ wf.2.2.1) wf.progFO).done_iff
    (K := K P.sorts) (hK := hK P.sorts) (normal_norm q) wf.fo.norm
  rw [nmap_ff (normal_norm q)] at h
  exact h

/-- The engine halts on a query exactly when it halts on its converse. -/
theorem terminates_conv {P : Program} {q : Rel} (wf : P.WellFormed q) :
    (Rt @U dom K hK).Terminates P q ↔ (Rt @U dom K hK).Terminates P (.conv q) := by
  rw [terminates_iff (K := K) (hK := hK) hD hG wf,
    terminates_iff (K := K) (hK := hK) hD hG wf.conv]
  have h := (mirror_same (K := K) (hK := hK) hG hE (hD _ wf.2.2.1) wf.progFO true).done_iff
    (K := K P.sorts) (hK := hK P.sorts) (normal_norm q) wf.fo.norm
  have e : nmap true false q.norm = (RelOf.conv q).norm := normB_normB true false q
  rw [e] at h
  exact h

/-- The engine halts on a query exactly when it halts on its mirror image in
the mirrored program. -/
theorem terminates_dual {P : Program} {q : Rel} (wf : P.WellFormed q) :
    (Rt @U dom K hK).Terminates P q ↔ (Rt @U dom K hK).Terminates P.dual q.dual := by
  rw [terminates_iff (K := K) (hK := hK) hD hG wf,
    terminates_iff (K := K) (hK := hK) hD hG wf.dual]
  have h := (mirror_dual (K := K) (hK := hK) hG hE (hD _ wf.2.2.1) wf.progFO
    wf.dual.progFO true).done_iff (K := K P.sorts) (hK := hK P.sorts) (normal_norm q) wf.fo.norm
  have e : nmap true true q.norm = q.dual.norm :=
    (nmap_normB true true false q).trans (normB_dual false q).symm
  rw [e] at h
  exact h

/-- The engine halts on a node exactly when it halts on the union of the
node with its converse. -/
theorem terminates_selfUnion {P : Program} {m : Rel} (wf : P.WellFormed m) (hm : Normal m) :
    (Rt @U dom K hK).Terminates P m ↔
      (Rt @U dom K hK).Terminates P (RelOf.or m m.normConv).norm := by
  have hL := hD _ wf.2.2.1
  have hP := wf.progFO
  have hU := hG (dom P.sorts) P (K P.sorts) (hK P.sorts) hL hP
  have wfu := wf.selfUnion
  have em : m.norm = m := hm.normB_false
  rw [terminates_iff (K := K) (hK := hK) hD hG wf,
    terminates_iff (K := K) (hK := hK) hD hG wfu, norm_norm, em]
  have hmc : Normal m.normConv := normal_normConv m
  constructor
  · intro h
    have hc := (mirror_same (K := K) (hK := hK) hG hE hL hP true).done
      (K := K P.sorts) (hK := hK P.sorts) hm wf.fo h
    refine done_members hL hP hU (roots := [m, m.normConv]) (fun c hc' => ?_) (normal_norm _)
      wfu.fo fun x hx => ?_
    · rcases List.mem_cons.1 hc' with rfl | hc'
      · exact ⟨hm, wf.fo, h⟩
      · obtain rfl := List.mem_singleton.1 hc'
        exact ⟨hmc, wf.fo.normConv, hc⟩
    · rcases (mem_unionParts_or hm hmc).1 hx with hx | hx
      · exact ⟨m, by simp, hx⟩
      · exact ⟨m.normConv, by simp, hx⟩
  · intro h
    refine done_members hL hP hU (roots := [(RelOf.or m m.normConv).norm]) (fun c hc' => ?_) hm
      wf.fo fun x hx => ?_
    · obtain rfl := List.mem_singleton.1 hc'
      exact ⟨normal_norm _, wfu.fo, h⟩
    · exact ⟨_, by simp, (mem_unionParts_or hm hmc).2 (.inl hx)⟩

/-- **The symmetric engine halts on an input exactly when it halts on the
input chosen to run.** -/
theorem sameHalt : ((engine @U).costedAt dom K hK).SameHalt := by
  intro P q wf
  have tn := fun {P : Program} {q : Rel} (wf : P.WellFormed q) =>
    terminates_normed (K := K) (hK := hK) hD hG hE wf
  have tc := fun {P : Program} {q : Rel} (wf : P.WellFormed q) =>
    terminates_conv (K := K) (hK := hK) hD hG hE wf
  have td := fun {P : Program} {q : Rel} (wf : P.WellFormed q) =>
    terminates_dual (K := K) (hK := hK) hD hG hE wf
  have tu := fun {P : Program} {m : Rel} (wf : P.WellFormed m) (hm : Normal m) =>
    terminates_selfUnion (K := K) (hK := hK) hD hG hE wf hm
  show (Rt @U dom K hK).Terminates P q ↔
    (Rt @U dom K hK).Terminates (orient P q).P (orient P q).root
  unfold orient
  cases hc : listCmp relCmp (P.defs.map fun d => d.2.norm) (P.dual.defs.map fun d => d.2.norm)
  · dsimp only
    rw [pick_P]
    refine (pick_iff _ (fun c => (Rt @U dom K hK).Terminates P.normed c) _ _ _ (fun c hc => ?_)
      fun c hc => ?_).symm
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact (tn wf).symm
      · exact (tn wf.conv).symm.trans (tc wf).symm
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact tu wf.normed (normal_norm _)
      · exact tu wf.conv.normed (normal_norm _)
  · have e := normed_dual_of_eq (listCmp_eq (f := relCmp) hc)
    dsimp only
    rw [pick_P]
    refine (pick_iff _ (fun c => (Rt @U dom K hK).Terminates P.normed c) _ _ _ (fun c hc => ?_)
      fun c hc => ?_).symm
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact (tn wf).symm
      · exact (tn wf.conv).symm.trans (tc wf).symm
      · rw [← e]
        exact (tn wf.dual).symm.trans (td wf).symm
      · rw [← e]
        exact ((tn wf.dual.conv).symm.trans (tc wf.dual).symm).trans (td wf).symm
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact tu wf.normed (normal_norm _)
      · exact tu wf.conv.normed (normal_norm _)
      · exact tu (e ▸ wf.dual.normed) (normal_norm _)
      · exact tu (e ▸ wf.dual.conv.normed) (normal_norm _)
  · dsimp only
    rw [pick_P]
    refine (pick_iff _ (fun c => (Rt @U dom K hK).Terminates P.dual.normed c) _ _ _
      (fun c hc => ?_) fun c hc => ?_).symm
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact (tn wf.dual).symm.trans (td wf).symm
      · exact ((tn wf.dual.conv).symm.trans (tc wf.dual).symm).trans (td wf).symm
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact tu wf.dual.normed (normal_norm _)
      · exact tu wf.dual.conv.normed (normal_norm _)

end theorems

end Symmetric

end RwLog
