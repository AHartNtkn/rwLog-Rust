/-
# The interfaces of a span: the Rust `right_bound` and `left_bound`

The interface at a side `p` of a span keeps the constraints whose variables
all occur in `p`. `mark` flags every subterm of `p` in table `A`,
`all_marked` asks of a constraint whether each of its variables is flagged
(table `B` remembers the answer for each node), and `keep` filters the list.

`right_bound_spec` and `left_bound_spec`: the results are the
specification's `bound s.rightIface` and `bound s.leftIface`, within
`ifaceCost` ticks: linear in the distinct subterms of the side and of the
constraints.
-/
import RwLogVerified.Cover

open Aeneas Aeneas.Std Result

namespace RwLogVerified

open rwlog_core RwLog RwLog.Term

variable {nm : Option Nat → Sym}

/-! ## Flagging the subterms of a term -/

/-- The nodes with an entry in the table are exactly the terms of `M`. -/
structure Marked (nm : Option Nat → Sym) (nodes : List store.Node) (A : Nat → Option Nat)
    (M : Finset Pat) : Prop where
  sound : ∀ k, A k ≠ none → ∃ t ∈ M, Repr nm nodes k t
  complete : ∀ t ∈ M, ∃ k, Repr nm nodes k t ∧ A k ≠ none

theorem Marked.iff (hnm : Function.Injective nm) {nodes : List store.Node} (hN : NodesOK nodes)
    {A : Nat → Option Nat} {M : Finset Pat} (h : Marked nm nodes A M) {k : Nat} {t : Pat}
    (hk : Repr nm nodes k t) : A k ≠ none ↔ t ∈ M := by
  constructor
  · intro hA
    obtain ⟨t', ht', hr⟩ := h.sound k hA
    rw [hk.unique hr]; exact ht'
  · intro ht
    obtain ⟨k', hr, hA⟩ := h.complete t ht
    rw [Repr.inj hnm hN hk hr]; exact hA

theorem Marked.extends {s s' : store.Store} {A : Nat → Option Nat} {M : Finset Pat}
    (h : Marked nm s.nodes.val A M) (he : Extends s s') : Marked nm s'.nodes.val A M :=
  ⟨fun k hk => by obtain ⟨t, ht, hr⟩ := h.sound k hk; exact ⟨t, ht, he.repr hr⟩,
   fun t ht => by obtain ⟨k, hr, hk⟩ := h.complete t ht; exact ⟨k, he.repr hr, hk⟩⟩

/-- What `mark` leaves. -/
structure MarkPost (nm : Option Nat → Sym) (s s' : store.Store) (M : Finset Pat) (tp : Pat)
    (S : Finset Pat) : Prop where
  inv : Inv s'
  nodes : s'.nodes.val = s.nodes.val
  tblB : tbl s' .B = tbl s .B
  marked : Marked nm s'.nodes.val (tbl s' .A) (M ∪ tp.subs)
  grow : ∀ k, tbl s .A k ≠ none → tbl s' .A k ≠ none
  cost : s'.ticks.val + 8 * (pending nm s'.nodes.val (tbl s' .A) S).card ≤
    s.ticks.val + 4 + 8 * (pending nm s.nodes.val (tbl s .A) S).card

/-- The state of a flagging walk: `A0` is the table at the start. A flagged
node stands for a term of `M` or of the term walked, and the parts of a
flagged application are flagged or on the stack. -/
structure KSt (nm : Option Nat → Sym) (n0 : List store.Node) (tp : Pat) (p : Nat)
    (M : Finset Pat) (A0 A : Nat → Option Nat) (st : List store.Frame) : Prop where
  grow : ∀ k, A0 k ≠ none → A k ≠ none
  sound : ∀ k, A k ≠ none → ∃ t ∈ M ∪ tp.subs, Repr nm n0 k t
  frames : ∀ f ∈ st, ∃ t ∈ tp.subs, Repr nm n0 (fkey f) t
  app : ∀ k (a b : store.TermId), A k ≠ none → n0[k]? = some (.App a b) →
    (A a.val ≠ none ∨ ∃ f ∈ st, fkey f = a.val) ∧ (A b.val ≠ none ∨ ∃ f ∈ st, fkey f = b.val)
  root : A p ≠ none ∨ ∃ f ∈ st, fkey f = p

variable {n0 : List store.Node} {tp : Pat} {p : Nat} {M : Finset Pat} {A0 A : Nat → Option Nat}

theorem KSt.start (hnm : Function.Injective nm) (hN : NodesOK n0) (hM : Marked nm n0 A0 M)
    (hcl : ∀ u ∈ M, u.subs ⊆ M) (q : store.TermId) (hp : Repr nm n0 q.val tp) :
    KSt nm n0 tp q.val M A0 A0 [.Visit q q] := by
  refine ⟨fun _ h => h, fun k hk => ?_, fun f hf => ?_, fun k a b hk hn => ?_,
    Or.inr ⟨_, List.mem_singleton_self _, rfl⟩⟩
  · obtain ⟨t, ht, hr⟩ := hM.sound k hk
    exact ⟨t, Finset.mem_union_left _ ht, hr⟩
  · simp only [List.mem_singleton] at hf
    subst hf
    exact ⟨tp, Term.self_mem_subs tp, hp⟩
  · obtain ⟨t, ht, hr⟩ := hM.sound k hk
    obtain ⟨ta, tb, e, ha, hb⟩ := hr.of_app hn
    subst e
    have hsa : ta ∈ M := hcl _ ht (by simp [Term.subs, Term.self_mem_subs])
    have hsb : tb ∈ M := hcl _ ht (by simp [Term.subs, Term.self_mem_subs])
    exact ⟨Or.inl ((hM.iff hnm hN ha).2 hsa), Or.inl ((hM.iff hnm hN hb).2 hsb)⟩

/-- The node of the top frame is flagged already. -/
theorem KSt.hit {f : store.Frame} {st : List store.Frame} (h : KSt nm n0 tp p M A0 A (f :: st))
    (hA : A (fkey f) ≠ none) : KSt nm n0 tp p M A0 A st := by
  have hmem : ∀ k, (A k ≠ none ∨ ∃ g ∈ f :: st, fkey g = k) → (A k ≠ none ∨ ∃ g ∈ st, fkey g = k) := by
    rintro k (h | ⟨g, hg, e⟩)
    · exact Or.inl h
    · rcases List.mem_cons.1 hg with rfl | hg
      · exact Or.inl (e ▸ hA)
      · exact Or.inr ⟨g, hg, e⟩
  refine ⟨h.grow, h.sound, fun g hg => h.frames g (List.mem_cons_of_mem _ hg),
    fun k a b hk hn => ?_, hmem _ h.root⟩
  obtain ⟨h1, h2⟩ := h.app k a b hk hn
  exact ⟨hmem _ h1, hmem _ h2⟩

/-- The node of the top frame is flagged. The new stack `st'` holds the old
one and frames for the parts of the node. -/
theorem KSt.set {f : store.Frame} {st st' : List store.Frame}
    (h : KSt nm n0 tp p M A0 A (f :: st)) (r : Nat) (hsub : ∀ g ∈ st, g ∈ st')
    (hfr : ∀ g ∈ st', ∃ t ∈ tp.subs, Repr nm n0 (fkey g) t)
    (hkids : ∀ a b : store.TermId, n0[fkey f]? = some (.App a b) →
      (∃ g ∈ st', fkey g = a.val) ∧ ∃ g ∈ st', fkey g = b.val) :
    KSt nm n0 tp p M A0 (Function.update A (fkey f) (some r)) st' := by
  have hgrow : ∀ k, A k ≠ none → Function.update A (fkey f) (some r) k ≠ none := by
    intro k hk
    by_cases e : k = fkey f
    · rw [e]; simp
    · rw [Function.update_of_ne e]; exact hk
  have hself : Function.update A (fkey f) (some r) (fkey f) ≠ none := by simp
  have hmem : ∀ k, (A k ≠ none ∨ ∃ g ∈ f :: st, fkey g = k) →
      (Function.update A (fkey f) (some r) k ≠ none ∨ ∃ g ∈ st', fkey g = k) := by
    rintro k (h | ⟨g, hg, e⟩)
    · exact Or.inl (hgrow k h)
    · rcases List.mem_cons.1 hg with rfl | hg
      · exact Or.inl (e ▸ hself)
      · exact Or.inr ⟨g, hsub g hg, e⟩
  refine ⟨fun k hk => hgrow k (h.grow k hk), fun k hk => ?_, hfr, fun k a b hk hn => ?_,
    hmem _ h.root⟩
  · by_cases e : k = fkey f
    · obtain ⟨t, ht, hr⟩ := h.frames f List.mem_cons_self
      exact ⟨t, Finset.mem_union_right _ ht, e ▸ hr⟩
    · rw [Function.update_of_ne e] at hk
      exact h.sound k hk
  · by_cases e : k = fkey f
    · subst e
      obtain ⟨h1, h2⟩ := hkids a b hn
      exact ⟨Or.inr h1, Or.inr h2⟩
    · rw [Function.update_of_ne e] at hk
      obtain ⟨h1, h2⟩ := h.app k a b hk hn
      exact ⟨hmem _ h1, hmem _ h2⟩

/-- With an empty stack, every subterm of the term walked is flagged. -/
theorem KSt.done
    (h : KSt nm n0 tp p M A0 A []) (hM : Marked nm n0 A0 M) (hp : Repr nm n0 p tp) :
    Marked nm n0 A (M ∪ tp.subs) := by
  have key : ∀ (t : Pat) (k : Nat), Repr nm n0 k t → A k ≠ none →
      ∀ u ∈ t.subs, ∃ k', Repr nm n0 k' u ∧ A k' ≠ none := by
    intro t
    induction t with
    | var v =>
      intro k hk hA u hu
      simp only [Term.subs, Finset.mem_singleton] at hu
      subst hu
      exact ⟨k, hk, hA⟩
    | sym f =>
      intro k hk hA u hu
      simp only [Term.subs, Finset.mem_singleton] at hu
      subst hu
      exact ⟨k, hk, hA⟩
    | app ta tb iha ihb =>
      intro k hk hA u hu
      simp only [Term.subs, Finset.mem_insert, Finset.mem_union] at hu
      obtain ⟨a, b, hn, ha, hb⟩ := Repr.app_inv hk
      obtain ⟨h1, h2⟩ := h.app k a b hA hn
      rcases hu with rfl | hu | hu
      · exact ⟨k, hk, hA⟩
      · refine iha _ ha ?_ u hu
        rcases h1 with h1 | ⟨f, hf, -⟩
        · exact h1
        · simp at hf
      · refine ihb _ hb ?_ u hu
        rcases h2 with h2 | ⟨f, hf, -⟩
        · exact h2
        · simp at hf
  have hroot : A p ≠ none := by
    rcases h.root with h | ⟨f, hf, -⟩
    · exact h
    · simp at hf
  refine ⟨h.sound, fun t ht => ?_⟩
  rcases Finset.mem_union.1 ht with ht | ht
  · obtain ⟨k, hr, hk⟩ := hM.complete t ht
    exact ⟨k, hr, h.grow k hk⟩
  · exact key tp p hp hroot t ht

/-- The invariant of the loop of `mark`. -/
def KInv (nm : Option Nat → Sym) (s0 : store.Store) (tp : Pat) (p : Nat) (M S : Finset Pat)
    (B : Nat) (s : store.Store) : Prop :=
  Wf s ∧ s.nodes.val = s0.nodes.val ∧ tbl s .B = tbl s0 .B ∧
    KSt nm s0.nodes.val tp p M (tbl s0 .A) (tbl s .A) (stk s) ∧
    s.ticks.val + 1 + 2 * (stk s).length +
      8 * (pending nm s0.nodes.val (tbl s .A) S).card ≤ B

def KDone (nm : Option Nat → Sym) (s0 : store.Store) (tp : Pat) (p : Nat) (M S : Finset Pat)
    (B : Nat) (s : store.Store) : Prop :=
  Wf s ∧ stk s = [] ∧ s.nodes.val = s0.nodes.val ∧ tbl s .B = tbl s0 .B ∧
    KSt nm s0.nodes.val tp p M (tbl s0 .A) (tbl s .A) [] ∧
    s.ticks.val + 8 * (pending nm s0.nodes.val (tbl s .A) S).card ≤ B

def KBodyPost (nm : Option Nat → Sym) (s0 : store.Store) (tp : Pat) (p : Nat) (M S : Finset Pat)
    (B : Nat) (t0 : Nat) : ControlFlow store.Store store.Store → Prop
  | .done s' => KDone nm s0 tp p M S B s'
  | .cont s' => KInv nm s0 tp p M S B s' ∧ t0 < s'.ticks.val

theorem mark_body_spec (hnm : Function.Injective nm) (s0 : store.Store) (tp : Pat) (p : Nat)
    (M S : Finset Pat) (B : Nat) (hB : 40 * B + 100 ≤ Usize.max) (hN : NodesOK s0.nodes.val)
    (hS : tp.subs ⊆ S) (s : store.Store) (h : KInv nm s0 tp p M S B s) :
    cover.mark_loop.body s ⦃ r => KBodyPost nm s0 tp p M S B s.ticks.val r ⦄ := by
  unfold cover.mark_loop.body
  obtain ⟨hW, hn, hTB, hK, hc⟩ := h
  step with pop_w s hW (by unfold Room; omega) as ⟨o, s1, e1, e2, e3, hW1, eo, est⟩
  cases hst : stk s with
  | nil =>
    rw [hst] at eo est hK hc
    simp only [List.head?_nil, List.tail_nil] at eo est
    subst eo
    simp only [WP.spec_ok]
    simp only [List.length_nil] at hc
    exact ⟨hW1, est, by rw [e1, hn], by rw [e2, hTB], by rw [e2]; exact hK, by rw [e2]; omega⟩
  | cons fr st =>
    rw [hst] at eo est hK hc
    simp only [List.head?_cons, List.tail_cons] at eo est
    subst eo
    simp only [List.length_cons] at hc
    obtain ⟨tq, htq, hq⟩ := hK.frames fr List.mem_cons_self
    have hFr' : ∀ g ∈ st, ∃ t ∈ tp.subs, Repr nm s0.nodes.val (fkey g) t :=
      fun g hg => hK.frames g (List.mem_cons_of_mem _ hg)
    simp only [node_of_eq]
    step with get_flag_w s1 .A (fid fr) hW1 (by rw [e1, hn, fid_val]; exact hq.lt)
      (by unfold Room; omega) as ⟨o1, s2, ho1, hK2⟩
    rw [e2, fid_val] at ho1
    have ht2 := hK2.ticks
    have hn2 : s2.nodes.val = s.nodes.val := by rw [hK2.nodes, e1]
    have htb2 : tbl s2 = tbl s := by rw [hK2.tbl, e2]
    have hstk2 : stk s2 = st := by rw [hK2.stk, est]
    cases hAq : tbl s .A (fkey fr) with
    | some w =>
      rw [hAq] at ho1
      simp only [Option.map_some] at ho1
      subst ho1
      simp only [WP.spec_ok]
      refine ⟨⟨hK2.wf, by rw [hn2, hn], by rw [htb2, hTB], ?_, ?_⟩, by omega⟩
      · rw [htb2, hstk2]
        exact hK.hit (by rw [hAq]; simp)
      · rw [htb2, hstk2]; omega
    | none =>
      rw [hAq] at ho1
      simp only [Option.map_none] at ho1
      subst ho1
      simp only
      have hP := pending_set_card hnm hN hq hAq (hS htq) 1
      step with set_flag_w s2 .A (fid fr) true hK2.wf (by rw [hn2, hn, fid_val]; exact hq.lt)
        (by unfold Room; omega) as ⟨s3, g1, g2, g3, g4, g5, g6⟩
      rw [htb2, fid_val] at g4
      simp only [↓reduceIte] at g4
      have hn3 : s3.nodes.val = s.nodes.val := by rw [g1, hn2]
      have hB3 : tbl s3 .B = tbl s .B := by rw [g5 .B (by simp), htb2]
      have hstk3 : stk s3 = st := by rw [g6, hstk2]
      step with read_w s3 (fid fr) g3 (by rw [hn3, hn, fid_val]; exact hq.lt)
        (by unfold Room; omega) as ⟨nd, s4, hnd, hK4⟩
      rw [hn3, hn, fid_val] at hnd
      have ht4 := hK4.ticks
      have hn4 : s4.nodes.val = s.nodes.val := by rw [hK4.nodes, hn3]
      have hA4 : tbl s4 .A = Function.update (tbl s .A) (fkey fr) (some 1) := by
        rw [hK4.tbl, g4]
      have hB4 : tbl s4 .B = tbl s .B := by rw [hK4.tbl, hB3]
      have hstk4 : stk s4 = st := by rw [hK4.stk, hstk3]
      have hplain : (∀ a b, nd ≠ .App a b) →
          KBodyPost nm s0 tp p M S B s.ticks.val (.cont s4) := by
        intro hna
        refine ⟨⟨hK4.wf, by rw [hn4, hn], by rw [hB4, hTB], ?_, ?_⟩, by omega⟩
        · rw [hA4, hstk4]
          refine hK.set 1 (fun _ h => h) hFr' fun a b e => ?_
          rw [hnd] at e
          cases e
          exact absurd rfl (hna a b)
        · rw [hA4, hstk4]; omega
      cases nd with
      | V0 => simp only [WP.spec_ok]; exact hplain (by simp)
      | VL a => simp only [WP.spec_ok]; exact hplain (by simp)
      | VR a => simp only [WP.spec_ok]; exact hplain (by simp)
      | Sym g => simp only [WP.spec_ok]; exact hplain (by simp)
      | Nil => simp only [WP.spec_ok]; exact hplain (by simp)
      | App a b =>
        obtain ⟨ta, tb, e, ha, hb⟩ := hq.of_app hnd
        subst e
        simp only
        step with push_w s4 (.Visit b b) hK4.wf (by unfold Room; omega)
          as ⟨s5, b1, b2, b3, hW5, b5⟩
        step with push_w s5 (.Visit a a) hW5 (by unfold Room; omega)
          as ⟨s6, c1, c2, c3, hW6, c5⟩
        have hstk6 : stk s6 = .Visit a a :: .Visit b b :: st := by rw [c5, b5, hstk4]
        refine ⟨⟨hW6, by rw [c1, b1, hn4, hn], by rw [c2, b2, hB4, hTB], ?_, ?_⟩,
          by omega⟩
        · rw [c2, b2, hA4, hstk6]
          refine hK.set 1 (fun g hg => by simp [hg]) ?_ fun a' b' e => ?_
          · intro g hg
            simp only [List.mem_cons] at hg
            rcases hg with rfl | rfl | hg
            · exact ⟨ta, Term.subs_trans htq (by simp [Term.subs, Term.self_mem_subs]), ha⟩
            · exact ⟨tb, Term.subs_trans htq (by simp [Term.subs, Term.self_mem_subs]), hb⟩
            · exact hFr' g hg
          · rw [hnd] at e
            cases e
            exact ⟨⟨.Visit a a, by simp, rfl⟩, ⟨.Visit b b, by simp, rfl⟩⟩
        · rw [c2, b2, hA4, hstk6]
          simp only [List.length_cons]
          omega

/-- `mark` flags every subterm of the term. It spends four ticks, and eight
more for each term of `S` that had no entry and gets one. -/
theorem mark_spec (hnm : Function.Injective nm) (s : store.Store) (p : store.TermId) {tp : Pat}
    {M : Finset Pat} (S : Finset Pat) (hI : Inv s) (hp : Repr nm s.nodes.val p.val tp)
    (hM : Marked nm s.nodes.val (tbl s .A) M) (hcl : ∀ u ∈ M, u.subs ⊆ M) (hS : tp.subs ⊆ S)
    (hroom : Room s (4 + 8 * (pending nm s.nodes.val (tbl s .A) S).card)) :
    cover.mark s p ⦃ s' => MarkPost nm s s' M tp S ⦄ := by
  unfold cover.mark cover.mark_loop
  have hroom' := hroom
  unfold Room at hroom'
  step with push_w s (.Visit p p) hI.toWf (by unfold Room; omega) as ⟨s1, a1, a2, a3, hW1, a5⟩
  rw [hI.empty] at a5
  let B := s.ticks.val + 4 + 8 * (pending nm s.nodes.val (tbl s .A) S).card
  have hloop := loop.spec_decr_nat
    (fun x : store.Store => B + 1 - x.ticks.val)
    (KInv nm s tp p.val M S B)
    (fun x => MarkPost nm s x M tp S)
    (fun x : store.Store => cover.mark_loop.body x) s1
    (by
      intro x hinv
      refine WP.spec_mono (mark_body_spec hnm s tp p.val M S B (by omega) hI.nodesOK hS x hinv) ?_
      intro r hr
      cases r with
      | done y =>
        obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hr
        exact ⟨⟨h1, h2⟩, h3, h4, by rw [h3]; exact h5.done hM hp, h5.grow,
          by rw [h3]; exact h6⟩
      | cont x' =>
        obtain ⟨h1, h2⟩ := hr
        have hc := h1.2.2.2.2
        exact ⟨h1, by omega⟩)
    ⟨hW1, a1, by rw [a2], by rw [a5, a2]; exact KSt.start hnm hI.nodesOK hM hcl p hp, by
      rw [a5, a2]
      simp only [List.length_singleton]
      omega⟩
  exact hloop

/-! ## Are all variables of a term flagged? -/

/-- Every variable of `t` is in `M`. -/
def AllIn (M : Finset Pat) (t : Pat) : Prop := ∀ v ∈ t.vars, Term.var v ∈ M

instance (M : Finset Pat) (t : Pat) : Decidable (AllIn M t) := by
  unfold AllIn; infer_instance

/-- Every entry of table `B` is the answer for its key. -/
def AllOK (nm : Option Nat → Sym) (nodes : List store.Node) (B : Nat → Option Nat)
    (M : Finset Pat) : Prop :=
  ∀ k w, B k = some w → ∃ t, Repr nm nodes k t ∧ (w ≠ 0 ↔ AllIn M t)

theorem AllOK.set {nodes : List store.Node} {Bt : Nat → Option Nat} {k w : Nat} {t : Pat}
    (h : AllOK nm nodes Bt M) (hk : Repr nm nodes k t) (hw : w ≠ 0 ↔ AllIn M t) :
    AllOK nm nodes (Function.update Bt k (some w)) M := by
  intro k' w' hk'
  by_cases e : k' = k
  · subst e
    simp only [Function.update_self, Option.some.injEq] at hk'
    subst hk'
    exact ⟨t, hk, hw⟩
  · rw [Function.update_of_ne e] at hk'
    exact h k' w' hk'

/-- What `all_marked` leaves. -/
structure AllPost (nm : Option Nat → Sym) (s s' : store.Store) (M : Finset Pat) (t : Pat)
    (S : Finset Pat) (p : Nat) (b : Bool) : Prop where
  inv : Inv s'
  nodes : s'.nodes.val = s.nodes.val
  res : b = decide (AllIn M t)
  memo : AllOK nm s'.nodes.val (tbl s' .B) M
  tblA : tbl s' .A = tbl s .A
  grow : ∀ k, tbl s .B k ≠ none → tbl s' .B k ≠ none
  set : tbl s' .B p ≠ none
  cost : s'.ticks.val + 13 * (pending nm s'.nodes.val (tbl s' .B) S).card ≤
    s.ticks.val + 5 + 13 * (pending nm s.nodes.val (tbl s .B) S).card

theorem allIn_app {a b : Pat} : AllIn M (.app a b) ↔ AllIn M a ∧ AllIn M b := by
  simp only [AllIn, Term.vars, List.mem_append]
  constructor
  · exact fun h => ⟨fun v hv => h v (Or.inl hv), fun v hv => h v (Or.inr hv)⟩
  · rintro ⟨h1, h2⟩ v (hv | hv)
    · exact h1 v hv
    · exact h2 v hv

/-- The invariant of the loop of `all_marked`. -/
def AInv (nm : Option Nat → Sym) (s0 : store.Store) (tp : Pat) (p : Nat) (M S : Finset Pat)
    (B : Nat) (s : store.Store) : Prop :=
  Wf s ∧ s.nodes.val = s0.nodes.val ∧ tbl s .A = tbl s0 .A ∧
    AllOK nm s0.nodes.val (tbl s .B) M ∧
    RSt nm s0.nodes.val tp p (tbl s0 .B) (tbl s .B) (stk s) ∧
    ∃ U, Unb nm s0.nodes.val (tbl s .B) S (stk s) U ∧
      s.ticks.val + 1 + 2 * nV (stk s) + 5 * nB (stk s) + 13 * U.card ≤ B

def ADone (nm : Option Nat → Sym) (s0 : store.Store) (tp : Pat) (p : Nat) (M S : Finset Pat)
    (B : Nat) (s : store.Store) : Prop :=
  Wf s ∧ stk s = [] ∧ s.nodes.val = s0.nodes.val ∧ tbl s .A = tbl s0 .A ∧
    AllOK nm s0.nodes.val (tbl s .B) M ∧
    RSt nm s0.nodes.val tp p (tbl s0 .B) (tbl s .B) [] ∧
    s.ticks.val + 13 * (pending nm s0.nodes.val (tbl s .B) S).card ≤ B

def ABodyPost (nm : Option Nat → Sym) (s0 : store.Store) (tp : Pat) (p : Nat) (M S : Finset Pat)
    (B : Nat) (t0 : Nat) : ControlFlow store.Store store.Store → Prop
  | .done s' => ADone nm s0 tp p M S B s'
  | .cont s' => AInv nm s0 tp p M S B s' ∧ t0 < s'.ticks.val

theorem all_marked_body_spec (hnm : Function.Injective nm) (s0 : store.Store) (tp : Pat)
    (p : Nat) (M S : Finset Pat) (B : Nat) (hB : 40 * B + 100 ≤ Usize.max)
    (hN : NodesOK s0.nodes.val) (hMk : Marked nm s0.nodes.val (tbl s0 .A) M) (hS : tp.subs ⊆ S)
    (s : store.Store) (h : AInv nm s0 tp p M S B s) :
    cover.all_marked_loop.body s ⦃ r => ABodyPost nm s0 tp p M S B s.ticks.val r ⦄ := by
  unfold cover.all_marked_loop.body
  obtain ⟨hW, hn, hTA, hAO, hSt, U, hU, hc⟩ := h
  step with pop_w s hW (by unfold Room; omega) as ⟨o, s1, e1, e2, e3, hW1, eo, est⟩
  cases hst : stk s with
  | nil =>
    rw [hst] at eo est hSt hU hc
    simp only [List.head?_nil, List.tail_nil] at eo est
    subst eo
    simp only [WP.spec_ok]
    have := hU.card_le
    simp only [nV_nil, nB_nil] at hc
    exact ⟨hW1, est, by rw [e1, hn], by rw [e2, hTA], by rw [e2]; exact hAO,
      by rw [e2]; exact hSt, by rw [e2]; omega⟩
  | cons fr st =>
    rw [hst] at eo est hSt hU hc
    simp only [List.head?_cons, List.tail_cons] at eo est
    subst eo
    obtain ⟨hfa, tq, htq, hq⟩ := hSt.frames fr List.mem_cons_self
    -- the answer for the node of the frame is written
    have hset : ∀ (s3 : store.Store) (m : Bool), Wf s3 → s3.nodes.val = s.nodes.val →
        tbl s3 = tbl s → stk s3 = st → tbl s .B (fkey fr) = none →
        ((if m = true then 1 else 0 : Nat) ≠ 0 ↔ AllIn M tq) → s.ticks.val ≤ s3.ticks.val →
        s3.ticks.val + 2 + 2 * nV st + 5 * nB st + 13 * (U.erase tq).card ≤ B →
        (do
          let s5 ← store.Store.set_flag s3 store.Tbl.B (fid fr) m
          ok (ControlFlow.cont s5 : ControlFlow store.Store store.Store)) ⦃ r =>
          ABodyPost nm s0 tp p M S B s.ticks.val r ⦄ := by
      intro s3 m hW3 hn3 htb3 hstk3 hnone hw hlt hcost
      step with set_flag_w s3 .B (fid fr) m hW3 (by rw [hn3, hn, fid_val]; exact hq.lt)
        (by unfold Room; omega) as ⟨s5, g1, g2, g3, g4, g5, g6⟩
      rw [htb3, fid_val] at g4
      refine ⟨⟨g3, by rw [g1, hn3, hn], by rw [g5 .A (by simp), htb3, hTA], ?_, ?_,
        U.erase tq, ?_, ?_⟩, by omega⟩
      · rw [g4]; exact hAO.set hq hw
      · rw [g4, g6, hstk3]; exact hSt.set hnone _
      · rw [g4, g6, hstk3]
        simpa using hU.set hq [] (if m = true then 1 else 0)
      · rw [g6, hstk3]; omega
    cases fr with
    | Visit q u =>
      have : q = u := by simp only [faux, fkey] at hfa; scalar_tac
      subst this
      simp only [fkey] at hq hset
      simp only [nV_visit, nB_visit] at hc
      simp only
      step with get_flag_w s1 .B q hW1 (by rw [e1, hn]; exact hq.lt) (by unfold Room; omega)
        as ⟨o1, s2, ho1, hK2⟩
      rw [e2] at ho1
      have ht2 := hK2.ticks
      have hn2 : s2.nodes.val = s.nodes.val := by rw [hK2.nodes, e1]
      have htb2 : tbl s2 = tbl s := by rw [hK2.tbl, e2]
      have hstk2 : stk s2 = st := by rw [hK2.stk, est]
      cases hBq : tbl s .B q.val with
      | some w =>
        rw [hBq] at ho1
        simp only [Option.map_some] at ho1
        subst ho1
        simp only [WP.spec_ok]
        refine ⟨⟨hK2.wf, by rw [hn2, hn], by rw [htb2, hTA], by rw [htb2]; exact hAO, ?_,
          U, ?_, ?_⟩, by omega⟩
        · rw [htb2, hstk2]; exact hSt.hit (by simp only [fkey]; rw [hBq]; simp)
        · rw [htb2, hstk2]; exact hU.pop_visit trivial
        · rw [hstk2]; omega
      | none =>
        rw [hBq] at ho1
        simp only [Option.map_none] at ho1
        subst ho1
        have htU : tq ∈ U := hU.mem_top hnm hN hSt.waits hq hBq (hS htq)
        have hU1 := card_erase_add_one htU
        simp only
        step with read_w s2 q hK2.wf (by rw [hn2, hn]; exact hq.lt) (by unfold Room; omega)
          as ⟨nd, s3, hnd, hK3⟩
        rw [hn2, hn] at hnd
        have ht3 := hK3.ticks
        have hn3 : s3.nodes.val = s.nodes.val := by rw [hK3.nodes, hn2]
        have htb3 : tbl s3 = tbl s := by rw [hK3.tbl, htb2]
        have hstk3 : stk s3 = st := by rw [hK3.stk, hstk2]
        have hvar : ∀ v, tq = Term.var v →
            (do
              let (o2, s4) ← store.Store.get_flag s3 store.Tbl.A q
              let m := core.option.Option.is_some o2
              let s5 ← store.Store.set_flag s4 store.Tbl.B q m
              ok (ControlFlow.cont s5 : ControlFlow store.Store store.Store)) ⦃ r =>
              ABodyPost nm s0 tp p M S B s.ticks.val r ⦄ := by
          intro v hv
          subst hv
          step with get_flag_w s3 .A q hK3.wf (by rw [hn3, hn]; exact hq.lt)
            (by unfold Room; omega) as ⟨o2, s4, ho2, hK4⟩
          rw [htb3, hTA] at ho2
          have ht4 := hK4.ticks
          have hiff := hMk.iff hnm hN hq
          refine hset s4 (core.option.Option.is_some o2) hK4.wf (by rw [hK4.nodes, hn3])
            (by rw [hK4.tbl, htb3]) (by rw [hK4.stk, hstk3]) hBq ?_ (by omega) (by omega)
          have hall : AllIn M (Term.var v) ↔ Term.var v ∈ M := by simp [AllIn, Term.vars]
          rw [hall, ← hiff, ho2]
          cases tbl s0 .A q.val <;> simp
        have hatom : ∀ f, tq = Term.sym f →
            (do
              let s4 ← store.Store.set_flag s3 store.Tbl.B q true
              ok (ControlFlow.cont s4 : ControlFlow store.Store store.Store)) ⦃ r =>
              ABodyPost nm s0 tp p M S B s.ticks.val r ⦄ := by
          intro f hf
          subst hf
          exact hset s3 true hK3.wf hn3 htb3 hstk3 hBq (by simp [AllIn, Term.vars]) (by omega)
            (by omega)
        cases nd with
        | V0 =>
          obtain ⟨v, hv, -⟩ := hq.of_var hnd trivial
          exact hvar v hv
        | VL a =>
          obtain ⟨v, hv, -⟩ := hq.of_var hnd trivial
          exact hvar v hv
        | VR a =>
          obtain ⟨v, hv, -⟩ := hq.of_var hnd trivial
          exact hvar v hv
        | Sym g => exact hatom _ (hq.of_sym hnd)
        | Nil => exact hatom _ (hq.of_nil hnd)
        | App a b =>
          simp only
          step with push_w s3 (.Build q q) hK3.wf (by unfold Room; omega)
            as ⟨s4, a1, a2, a3, hW4, a5⟩
          step with push_w s4 (.Visit b b) hW4 (by unfold Room; omega)
            as ⟨s5, b1, b2, b3, hW5, b5⟩
          step with push_w s5 (.Visit a a) hW5 (by unfold Room; omega)
            as ⟨s6, c1, c2, c3, hW6, c5⟩
          have htb6 : tbl s6 = tbl s := by rw [c2, b2, a2, htb3]
          have hstk6 : stk s6 = .Visit a a :: .Visit b b :: .Build q q :: st := by
            rw [c5, b5, a5, hstk3]
          refine ⟨⟨hW6, by rw [c1, b1, a1, hn3, hn], by rw [htb6, hTA], by rw [htb6]; exact hAO,
            ?_, U.erase tq, ?_, ?_⟩, by omega⟩
          · rw [htb6, hstk6]; exact hSt.expand hN hBq hnd
          · rw [htb6, hstk6]; exact hU.expand hq
          · rw [hstk6]
            simp only [nV_visit, nV_build, nB_visit, nB_build]
            omega
    | Build q u =>
      simp only [fkey] at hq hset
      simp only [nV_build, nB_build] at hc
      obtain ⟨a, b, hn0, hnone, hBa, hBb⟩ := hSt.top
      obtain ⟨ta, tb, e, ha, hb⟩ := hq.of_app hn0
      subst e
      have hEr := Finset.card_erase_le (s := U) (a := Term.app ta tb)
      simp only
      step with read_w s1 q hW1 (by rw [e1, hn]; exact hq.lt) (by unfold Room; omega)
        as ⟨nd, s2, hnd, hK2⟩
      rw [e1, hn, hn0] at hnd
      cases hnd
      have ht2 := hK2.ticks
      have hn2 : s2.nodes.val = s.nodes.val := by rw [hK2.nodes, e1]
      have htb2 : tbl s2 = tbl s := by rw [hK2.tbl, e2]
      simp only
      step with get_flag_w s2 .B a hK2.wf (by rw [hn2, hn]; exact ha.lt) (by unfold Room; omega)
        as ⟨o1, s3, ho1, hK3⟩
      rw [htb2] at ho1
      have ht3 := hK3.ticks
      have hn3 : s3.nodes.val = s.nodes.val := by rw [hK3.nodes, hn2]
      have htb3 : tbl s3 = tbl s := by rw [hK3.tbl, htb2]
      cases hwa : tbl s .B a.val with
      | none => exact absurd hwa hBa
      | some wa =>
      rw [hwa] at ho1
      simp only [Option.map_some] at ho1
      subst ho1
      simp only [cover.is_set, core.option.Option.unwrap_or_some, bind_ok]
      step with get_flag_w s3 .B b hK3.wf (by rw [hn3, hn]; exact hb.lt) (by unfold Room; omega)
        as ⟨o2, s4, ho2, hK4⟩
      rw [htb3] at ho2
      have ht4 := hK4.ticks
      have hn4 : s4.nodes.val = s.nodes.val := by rw [hK4.nodes, hn3]
      have htb4 : tbl s4 = tbl s := by rw [hK4.tbl, htb3]
      have hstk4 : stk s4 = st := by rw [hK4.stk, hK3.stk, hK2.stk, est]
      cases hwb : tbl s .B b.val with
      | none => exact absurd hwb hBb
      | some wb =>
      rw [hwb] at ho2
      simp only [Option.map_some] at ho2
      subst ho2
      simp only [core.option.Option.unwrap_or_some]
      obtain ⟨ta', h1, hra⟩ := hAO _ _ hwa
      have := ha.unique h1
      subst this
      obtain ⟨tb', h2, hrb⟩ := hAO _ _ hwb
      have := hb.unique h2
      subst this
      by_cases ha0 : wa ≠ 0
      · simp only [decide_eq_true ha0, ↓reduceIte]
        refine hset s4 (decide (wb ≠ 0)) hK4.wf hn4 htb4 hstk4 hnone ?_ (by omega) (by omega)
        rw [allIn_app, ← hra, ← hrb]
        by_cases hb0 : wb ≠ 0 <;> simp [ha0, hb0]
      · simp only [decide_eq_false ha0, Bool.false_eq_true, ↓reduceIte]
        refine hset s4 false hK4.wf hn4 htb4 hstk4 hnone ?_ (by omega) (by omega)
        rw [allIn_app, ← hra]
        simp [ha0]

/-- `all_marked` decides whether every variable of the term is flagged, and
leaves the answer for the node in table `B`. It spends five ticks, and
thirteen more for each term of `S` that had no answer and gets one. -/
theorem all_marked_spec (hnm : Function.Injective nm) (s : store.Store) (p : store.TermId)
    {tp : Pat} {M : Finset Pat} (S : Finset Pat) (hI : Inv s)
    (hp : Repr nm s.nodes.val p.val tp) (hM : Marked nm s.nodes.val (tbl s .A) M)
    (hB : AllOK nm s.nodes.val (tbl s .B) M) (hS : tp.subs ⊆ S)
    (hroom : Room s (5 + 13 * (pending nm s.nodes.val (tbl s .B) S).card)) :
    cover.all_marked s p ⦃ b s' => AllPost nm s s' M tp S p.val b ⦄ := by
  unfold cover.all_marked cover.all_marked_loop
  have hroom' := hroom
  unfold Room at hroom'
  step with push_w s (.Visit p p) hI.toWf (by unfold Room; omega) as ⟨s1, a1, a2, a3, hW1, a5⟩
  rw [hI.empty] at a5
  let B := s.ticks.val + 4 + 13 * (pending nm s.nodes.val (tbl s .B) S).card
  have hloop := loop.spec_decr_nat
    (fun x : store.Store => B + 1 - x.ticks.val)
    (AInv nm s tp p.val M S B)
    (ADone nm s tp p.val M S B)
    (fun x : store.Store => cover.all_marked_loop.body x) s1
    (by
      intro x hinv
      refine WP.spec_mono (all_marked_body_spec hnm s tp p.val M S B (by omega) hI.nodesOK hM hS
        x hinv) ?_
      intro r hr
      cases r with
      | done y => exact hr
      | cont x' =>
        obtain ⟨h1, h2⟩ := hr
        have hc := h1.2.2.2.2.2
        obtain ⟨U, -, hc⟩ := hc
        exact ⟨h1, by omega⟩)
    ⟨hW1, a1, by rw [a2], by rw [a2]; exact hB,
      ⟨by rw [a2]; exact fun _ _ h => h, by
        rw [a5]
        intro f' hf'
        simp only [List.mem_singleton] at hf'
        subst hf'
        exact ⟨rfl, tp, Term.self_mem_subs tp, hp⟩, by
        rw [a5]
        intro q u hq
        simp at hq, by rw [a5]; exact Waits.single p p, by
        rw [a5]; exact Or.inr ⟨_, List.mem_singleton_self _, rfl⟩⟩,
      _, Unb.start _ _ _ _, by
        rw [a5, a2]
        simp only [nV_visit, nV_nil, nB_visit, nB_nil]
        omega⟩
  step with hloop as ⟨s2, hD⟩
  obtain ⟨hW2, hemp, hn2, hTA2, hAO2, hSt2, hc2⟩ := hD
  have hBp := hSt2.done
  step with get_flag_w s2 .B p hW2 (by rw [hn2]; exact hp.lt) (by unfold Room; omega)
    as ⟨o, s3, ho, hK3⟩
  have ht3 := hK3.ticks
  cases hw : tbl s2 .B p.val with
  | none => exact absurd hw hBp
  | some w =>
    rw [hw] at ho
    simp only [Option.map_some] at ho
    subst ho
    simp only [cover.is_set, core.option.Option.unwrap_or_some, bind_ok, WP.spec_ok]
    obtain ⟨t', h1, hr⟩ := hAO2 _ _ hw
    have := hp.unique h1
    subst this
    refine ⟨⟨hK3.wf, by rw [hK3.stk]; exact hemp⟩, by rw [hK3.nodes, hn2], decide_eq_decide.2 hr,
      by rw [hK3.nodes, hn2, hK3.tbl]; exact hAO2, by rw [hK3.tbl, hTA2], ?_,
      by rw [hK3.tbl, hw]; simp, by rw [hK3.nodes, hn2, hK3.tbl]; omega⟩
    intro k hk
    rw [hK3.tbl]
    cases hk0 : tbl s .B k with
    | none => exact absurd hk0 hk
    | some v => rw [hSt2.keep k v hk0]; simp

theorem AllOK.extends {s s' : store.Store} {B : Nat → Option Nat}
    (h : AllOK nm s.nodes.val B M) (he : Extends s s') : AllOK nm s'.nodes.val B M :=
  fun k w hk => by
    obtain ⟨t, hr, hw⟩ := h k w hk
    exact ⟨t, he.repr hr, hw⟩


/-! ## Filtering the constraints -/

/-- The first loop of `keep` leaves in table `B` the answer for every
constraint. It spends one tick, six for each constraint, and thirteen for
each term of `S` that had no answer and gets one. -/
theorem keep_flag_spec (hnm : Function.Injective nm) (M S : Finset Pat) :
    ∀ (cs : List Pat) (s : store.Store) (l : store.TermId), Inv s →
      Repr nm s.nodes.val l.val (encList (nm none) cs) →
      Marked nm s.nodes.val (tbl s .A) M → AllOK nm s.nodes.val (tbl s .B) M →
      (∀ a ∈ cs, a.subs ⊆ S) →
      Room s (1 + 6 * cs.length + 13 * (pending nm s.nodes.val (tbl s .B) S).card) →
      cover.keep_loop0 l s ⦃ s' =>
        Inv s' ∧ s'.nodes.val = s.nodes.val ∧ tbl s' .A = tbl s .A ∧
        AllOK nm s'.nodes.val (tbl s' .B) M ∧
        (∀ k, tbl s .B k ≠ none → tbl s' .B k ≠ none) ∧
        (∀ a ∈ cs, ∀ k, Repr nm s.nodes.val k a → tbl s' .B k ≠ none) ∧
        s'.ticks.val + 13 * (pending nm s'.nodes.val (tbl s' .B) S).card ≤
          s.ticks.val + 1 + 6 * cs.length + 13 * (pending nm s.nodes.val (tbl s .B) S).card ⦄ := by
  unfold cover.keep_loop0
  intro cs
  induction cs with
  | nil =>
    intro s l hI hl hM hB hS hroom
    rw [loop]
    simp only [cover.keep_loop0.body]
    step with read_spec s l hI hl.lt (by unfold Room at hroom ⊢; omega) as ⟨r0, hnd, hK⟩
    obtain ⟨nd, s1⟩ := r0
    simp only at hnd hK ⊢
    have hfin : Inv s1 ∧ s1.nodes.val = s.nodes.val ∧ tbl s1 .A = tbl s .A ∧
        AllOK nm s1.nodes.val (tbl s1 .B) M ∧
        (∀ k, tbl s .B k ≠ none → tbl s1 .B k ≠ none) ∧
        (∀ a ∈ ([] : List Pat), ∀ k, Repr nm s.nodes.val k a → tbl s1 .B k ≠ none) ∧
        s1.ticks.val + 13 * (pending nm s1.nodes.val (tbl s1 .B) S).card ≤
          s.ticks.val + 1 + 6 * ([] : List Pat).length +
            13 * (pending nm s.nodes.val (tbl s .B) S).card :=
      ⟨hK.inv, hK.nodes, by rw [hK.tbl], by rw [hK.nodes, hK.tbl]; exact hB,
        by rw [hK.tbl]; exact fun _ h => h, by simp,
        by have := hK.ticks; rw [hK.nodes, hK.tbl]; simp only [List.length_nil]; omega⟩
    cases nd with
    | App h t =>
      obtain ⟨ta, tb, e', -, -⟩ := hl.of_app hnd
      cases e'
    | V0 => step*
    | VL _ => step*
    | VR _ => step*
    | Sym _ => step*
    | Nil => step*
  | cons a ts ih =>
    intro s l hI hl hM hB hS hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons] at hroom'
    rw [loop]
    simp only [cover.keep_loop0.body]
    step with read_spec s l hI hl.lt (by unfold Room; omega) as ⟨r0, hnd, hK⟩
    obtain ⟨nd, s1⟩ := r0
    simp only at hnd hK ⊢
    obtain ⟨h, t, hnode, hh, ht⟩ := Repr.app_inv (ta := a) (tb := encList (nm none) ts) hl
    rw [hnode] at hnd
    cases hnd
    have ht1 := hK.ticks
    have hn1 := hK.nodes
    step with all_marked_spec hnm s1 h S hK.inv (by rw [hn1]; exact hh)
      (by rw [hn1, hK.tbl]; exact hM) (by rw [hn1, hK.tbl]; exact hB)
      (hS a List.mem_cons_self) (by rw [hn1, hK.tbl]; unfold Room; omega) as ⟨r0, h3⟩
    obtain ⟨b, s2⟩ := r0
    simp only at h3 ⊢
    simp only [uncurry, bind_ok]
    have hc3 := h3.cost
    rw [hn1, hK.tbl] at hc3
    have hn2 : s2.nodes.val = s.nodes.val := by rw [h3.nodes, hn1]
    have hA2 : tbl s2 .A = tbl s .A := by rw [h3.tblA, hK.tbl]
    refine WP.spec_mono (ih s2 t h3.inv (by rw [hn2]; exact ht) (by rw [hn2, hA2]; exact hM)
      h3.memo (fun x hx => hS x (List.mem_cons_of_mem _ hx)) (by unfold Room; omega)) ?_
    rintro s3 ⟨hI3, b1, b2, b3, b4, b5, b6⟩
    rw [hn2] at b5
    refine ⟨hI3, by rw [b1, hn2], by rw [b2, hA2], b3,
      fun k hk => b4 k (h3.grow k (by rw [hK.tbl]; exact hk)), ?_,
      by simp only [List.length_cons]; omega⟩
    intro x hx k hk
    rcases List.mem_cons.1 hx with rfl | hx
    · have : k = h.val := Repr.inj hnm hI.nodesOK hk hh
      subst this
      exact b4 _ h3.set
    · exact b5 x hx k hk

/-- The second loop of `keep` pushes the constraints whose answer is yes,
the last on top. -/
theorem keep_push_spec (M : Finset Pat) : ∀ (cs : List Pat) (s : store.Store) (l : store.TermId),
    Wf s → Repr nm s.nodes.val l.val (encList (nm none) cs) →
    AllOK nm s.nodes.val (tbl s .B) M →
    (∀ a ∈ cs, ∀ k, Repr nm s.nodes.val k a → tbl s .B k ≠ none) →
    Room s (3 * cs.length + 1) →
    cover.keep_loop1 l s ⦃ s' l' =>
      Wf s' ∧ s'.nodes.val = s.nodes.val ∧ tbl s' = tbl s ∧
        s'.ticks.val ≤ s.ticks.val + 3 * cs.length + 1 ∧
        Repr nm s.nodes.val l'.val (encList (nm none) []) ∧
        ∃ fs, stk s' = fs ++ stk s ∧
          List.Forall₂ (fun f t => Repr nm s.nodes.val (fkey f) t) fs
            (cs.filter fun a => decide (AllIn M a)).reverse ⦄ := by
  unfold cover.keep_loop1
  intro cs
  induction cs with
  | nil =>
    intro s l hW hl hB hset hroom
    rw [loop]
    simp only [cover.keep_loop1.body]
    step with read_w s l hW hl.lt (by unfold Room at hroom ⊢; omega) as ⟨r0, hnd, hK⟩
    obtain ⟨nd, s1⟩ := r0
    simp only at hnd hK ⊢
    have hfin : Wf s1 ∧ s1.nodes.val = s.nodes.val ∧ tbl s1 = tbl s ∧
        s1.ticks.val ≤ s.ticks.val + 3 * ([] : List Pat).length + 1 ∧
        Repr nm s.nodes.val l.val (encList (nm none) []) ∧
        ∃ fs, stk s1 = fs ++ stk s ∧
          List.Forall₂ (fun f t => Repr nm s.nodes.val (fkey f) t) fs
            (([] : List Pat).filter fun a => decide (AllIn M a)).reverse :=
      ⟨hK.wf, hK.nodes, hK.tbl, by have := hK.ticks; simp; omega, hl, [], by simp [hK.stk],
        by simp⟩
    cases nd with
    | App h t =>
      obtain ⟨ta, tb, e', -, -⟩ := hl.of_app hnd
      cases e'
    | V0 => step*
    | VL _ => step*
    | VR _ => step*
    | Sym _ => step*
    | Nil => step*
  | cons a ts ih =>
    intro s l hW hl hB hset hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons] at hroom'
    rw [loop]
    simp only [cover.keep_loop1.body]
    step with read_w s l hW hl.lt (by unfold Room; omega) as ⟨r0, hnd, hK⟩
    obtain ⟨nd, s1⟩ := r0
    simp only at hnd hK ⊢
    obtain ⟨h, t, hnode, hh, ht⟩ := Repr.app_inv (ta := a) (tb := encList (nm none) ts) hl
    rw [hnode] at hnd
    cases hnd
    have ht1 := hK.ticks
    have hn1 := hK.nodes
    step with get_flag_w s1 .B h hK.wf (by rw [hn1]; exact hh.lt) (by unfold Room; omega)
      as ⟨r0, ho, hK2⟩
    obtain ⟨o, s2⟩ := r0
    simp only at ho hK2 ⊢
    rw [hK.tbl] at ho
    have ht2 := hK2.ticks
    have hn2 : s2.nodes.val = s.nodes.val := by rw [hK2.nodes, hn1]
    have htb2 : tbl s2 = tbl s := by rw [hK2.tbl, hK.tbl]
    have hstk2 : stk s2 = stk s := by rw [hK2.stk, hK.stk]
    cases hw : tbl s .B h.val with
    | none => exact absurd hw (hset a List.mem_cons_self _ hh)
    | some w =>
    rw [hw] at ho
    simp only [Option.map_some] at ho
    subst ho
    simp only [uncurry]
    rw [show cover.is_set (some (decide (w ≠ 0))) = ok (decide (w ≠ 0)) from rfl]
    simp only [bind_ok]
    obtain ⟨t', h1, hr⟩ := hB _ _ hw
    have := hh.unique h1
    subst this
    have hset' : ∀ x ∈ ts, ∀ k, Repr nm s.nodes.val k x → tbl s .B k ≠ none :=
      fun x hx => hset x (List.mem_cons_of_mem _ hx)
    by_cases hw0 : w ≠ 0
    · simp only [decide_eq_true hw0, ↓reduceIte]
      have hya : AllIn M a := hr.1 hw0
      step with push_w s2 (.Visit h h) hK2.wf (by unfold Room; omega)
        as ⟨s3, a1, a2, a3, hW3, a5⟩
      have hn3 : s3.nodes.val = s.nodes.val := by rw [a1, hn2]
      have htb3 : tbl s3 = tbl s := by rw [a2, htb2]
      refine WP.spec_mono (ih s3 t hW3 (by rw [hn3]; exact ht) (by rw [hn3, htb3]; exact hB)
        (by rw [hn3, htb3]; exact hset') (by unfold Room; omega)) ?_
      rintro ⟨s4, l'⟩ ⟨hW4, b1, b2, b3, b4, fs, b5, b6⟩
      rw [hn3] at b4 b6
      refine ⟨hW4, by rw [b1, hn3], by rw [b2, htb3],
        by simp only [List.length_cons]; omega, b4, fs ++ [.Visit h h], ?_, ?_⟩
      · rw [b5, a5, hstk2]; simp
      · have e : (a :: ts).filter (fun a => decide (AllIn M a)) =
            a :: ts.filter (fun a => decide (AllIn M a)) := by simp [hya]
        rw [e, List.reverse_cons]
        exact List.rel_append b6 (.cons hh .nil)
    · simp only [decide_eq_false hw0, Bool.false_eq_true, ↓reduceIte, bind_ok]
      have hna : ¬ AllIn M a := fun h => hw0 (hr.2 h)
      refine WP.spec_mono (ih s2 t hK2.wf (by rw [hn2]; exact ht) (by rw [hn2, htb2]; exact hB)
        (by rw [hn2, htb2]; exact hset') (by unfold Room; omega)) ?_
      rintro ⟨s4, l'⟩ ⟨hW4, b1, b2, b3, b4, fs, b5, b6⟩
      rw [hn2] at b4 b6
      refine ⟨hW4, by rw [b1, hn2], by rw [b2, htb2],
        by simp only [List.length_cons]; omega, b4, fs, by rw [b5, hstk2], ?_⟩
      have e : (a :: ts).filter (fun a => decide (AllIn M a)) =
          ts.filter (fun a => decide (AllIn M a)) := by simp [hna]
      rw [e]; exact b6

/-- What `keep` leaves. -/
structure KeepPost (nm : Option Nat → Sym) (s s' : store.Store) (M : Finset Pat) (cs : List Pat)
    (S : Finset Pat) (r : store.TermId) : Prop where
  inv : Inv s'
  ext : Extends s s'
  repr : Repr nm s'.nodes.val r.val (encList (nm none) (cs.filter fun a => decide (AllIn M a)))
  memo : AllOK nm s'.nodes.val (tbl s' .B) M
  tblA : tbl s' .A = tbl s .A
  cost : s'.ticks.val + 13 * (pending nm s'.nodes.val (tbl s' .B) S).card ≤
    s.ticks.val + 3 + 11 * cs.length + 13 * (pending nm s.nodes.val (tbl s .B) S).card

/-- `keep` returns the constraints whose variables are all flagged, in their
order. It spends three ticks, eleven for each constraint, and thirteen for
each term of `S` that had no answer and gets one. -/
theorem keep_spec (hnm : Function.Injective nm) (M S : Finset Pat) (cs : List Pat)
    (s : store.Store) (c : store.TermId) (hI : Inv s)
    (hc : Repr nm s.nodes.val c.val (encList (nm none) cs))
    (hM : Marked nm s.nodes.val (tbl s .A) M) (hB : AllOK nm s.nodes.val (tbl s .B) M)
    (hS : ∀ a ∈ cs, a.subs ⊆ S)
    (hroom : Room s (3 + 11 * cs.length + 13 * (pending nm s.nodes.val (tbl s .B) S).card)) :
    cover.keep s c ⦃ r s' => KeepPost nm s s' M cs S r ⦄ := by
  unfold cover.keep
  have hroom' := hroom
  unfold Room at hroom'
  step with keep_flag_spec hnm M S cs s c hI hc hM hB hS (by unfold Room; omega)
    as ⟨s1, hI1, hn1, hA1, hB1, _, hset1, hc1⟩
  step with keep_push_spec (nm := nm) M cs s1 c hI1.toWf (by rw [hn1]; exact hc) hB1
    (by rw [hn1]; exact hset1) (by unfold Room; omega)
    as ⟨s2, l, hW2, hn2, htb2, ht2, hl, fs, hstk2, hF⟩
  rw [hI1.empty, List.append_nil] at hstk2
  have hlen : fs.length ≤ cs.length := by
    have := hF.length_eq
    simp only [List.length_reverse] at this
    rw [this]; exact List.length_filter_le _ _
  have hx2 : Extends s1 s2 := Extends.of_eq hn2
  step with unstack_spec (nm := nm) fs (cs.filter fun a => decide (AllIn M a)).reverse [] s2 l
    hW2 hstk2 (hF.imp fun _ _ h => hx2.repr h) (hx2.repr hl) (by unfold Room; omega)
    as ⟨r, s3, h1, h2, h3, h4, h5⟩
  obtain ⟨m3, hm3⟩ := h2
  have hpm : pending nm s3.nodes.val (tbl s3 .B) S ⊆ pending nm s1.nodes.val (tbl s1 .B) S := by
    rw [hm3, h5, hn2, htb2]; exact pending_mono (fun k hk => hk)
  have hcard := Finset.card_le_card hpm
  have hx3 : Extends s1 s3 := hx2.trans ⟨m3, hm3⟩
  refine ⟨h1, (Extends.of_eq hn1).trans hx3, by simpa using h3,
    by rw [h5, htb2]; exact hB1.extends hx3, by rw [h5, htb2, hA1], by omega⟩

/-! ## The interface -/

theorem cover_is_var_spec (s : store.Store) (p : store.TermId) {tp : Pat} (hI : Inv s)
    (hp : Repr nm s.nodes.val p.val tp) (hroom : Room s 1) :
    cover.is_var s p ⦃ b s' => (b = true ↔ ∃ v, tp = Term.var v) ∧ Kept s s' 1 ⦄ := by
  unfold cover.is_var
  step with read_spec s p hI hp.lt hroom as ⟨nd, s1, hnd, hK⟩
  cases nd with
  | V0 =>
    obtain ⟨v, hv, -⟩ := hp.of_var hnd trivial
    simp only [WP.spec_ok]
    exact ⟨by simp [hv], hK⟩
  | VL a =>
    obtain ⟨v, hv, -⟩ := hp.of_var hnd trivial
    simp only [WP.spec_ok]
    exact ⟨by simp [hv], hK⟩
  | VR a =>
    obtain ⟨v, hv, -⟩ := hp.of_var hnd trivial
    simp only [WP.spec_ok]
    exact ⟨by simp [hv], hK⟩
  | Sym g =>
    simp only [WP.spec_ok]
    exact ⟨by simp [hp.of_sym hnd], hK⟩
  | Nil =>
    simp only [WP.spec_ok]
    exact ⟨by simp [hp.of_nil hnd], hK⟩
  | App a b =>
    obtain ⟨ta, tb, e, -, -⟩ := hp.of_app hnd
    simp only [WP.spec_ok]
    exact ⟨by simp [e], hK⟩

theorem cover_is_nil_spec (hnm : Function.Injective nm) (s : store.Store) (c : store.TermId)
    {cs : List Pat} (hI : Inv s) (hc : Repr nm s.nodes.val c.val (encList (nm none) cs))
    (hroom : Room s 1) :
    cover.is_nil s c ⦃ b s' => (b = true ↔ cs = []) ∧ Kept s s' 1 ⦄ := by
  unfold cover.is_nil
  step with read_spec s c hI hc.lt hroom as ⟨nd, s1, hnd, hK⟩
  cases nd with
  | V0 =>
    obtain ⟨v, hv, -⟩ := hc.of_var hnd trivial
    have : cs ≠ [] := by rintro rfl; simp [encList] at hv
    simp only [WP.spec_ok]
    exact ⟨by simp [this], hK⟩
  | VL a =>
    obtain ⟨v, hv, -⟩ := hc.of_var hnd trivial
    have : cs ≠ [] := by rintro rfl; simp [encList] at hv
    simp only [WP.spec_ok]
    exact ⟨by simp [this], hK⟩
  | VR a =>
    obtain ⟨v, hv, -⟩ := hc.of_var hnd trivial
    have : cs ≠ [] := by rintro rfl; simp [encList] at hv
    simp only [WP.spec_ok]
    exact ⟨by simp [this], hK⟩
  | Sym g =>
    have e := hc.of_sym hnd
    have : cs ≠ [] := by
      rintro rfl
      simp only [encList, Term.sym.injEq] at e
      exact absurd (hnm e) (by simp)
    simp only [WP.spec_ok]
    exact ⟨by simp [this], hK⟩
  | Nil =>
    have : cs = [] := encList_of_not_app hc hnd (by simp)
    simp only [WP.spec_ok]
    exact ⟨by simp [this], hK⟩
  | App a b =>
    obtain ⟨t, ts, e, -, -⟩ := encList_of_app hc hnd
    simp only [WP.spec_ok]
    exact ⟨by simp [e], hK⟩

/-- The ticks an interface may spend: linear in the distinct subterms of the
side and of the constraints, and in the number of constraints. -/
def ifaceCost (tp : Pat) (cs : List Pat) : Nat :=
  11 + 8 * tp.subs.card + 11 * cs.length + 13 * (cs.toFinset.biUnion Term.subs).card

/-- `iface` returns the interface at the side `tp` of a span with
constraints `cs`, as a boundary, within `ifaceCost` ticks. -/
theorem iface_spec (hnm : Function.Injective nm) (s : store.Store) (p c : store.TermId)
    {tp : Pat} {cs : List Pat} (hI : Inv s) (hp : Repr nm s.nodes.val p.val tp)
    (hc : Repr nm s.nodes.val c.val (encList (nm none) cs)) (hroom : Room s (ifaceCost tp cs)) :
    cover.iface s p c ⦃ r s' =>
      Inv s' ∧ Extends s s' ∧
      OptSpanAt nm s'.nodes.val r
        (bound ⟨tp, tp, cs.filter fun a => a.vars.all (· ∈ tp.vars)⟩) ∧
      s'.ticks.val ≤ s.ticks.val + ifaceCost tp cs ⦄ := by
  unfold cover.iface
  have hroom' := hroom
  unfold Room ifaceCost at hroom'
  step with clear_spec s .A hI (by unfold Room; omega) as ⟨s1, hn1, ht1, hI1, hA1, ho1⟩
  have hM1 : Marked nm s1.nodes.val (tbl s1 .A) ∅ :=
    ⟨fun k hk => absurd (hA1 k) hk, fun t ht => by simp at ht⟩
  have hP1 := pending_card_le (nm := nm) s1.nodes.val (tbl s1 .A) tp.subs
  step with mark_spec hnm s1 p tp.subs hI1 (by rw [hn1]; exact hp) hM1 (by simp)
    (Finset.Subset.refl _) (by unfold Room; omega) as ⟨s2, h2⟩
  have hc2 := h2.cost
  have hn2 : s2.nodes.val = s.nodes.val := by rw [h2.nodes, hn1]
  step with clear_spec s2 .B h2.inv (by unfold Room; omega) as ⟨s3, hn3, ht3, hI3, hB3, ho3⟩
  have hn3' : s3.nodes.val = s.nodes.val := by rw [hn3, hn2]
  have hM3 : Marked nm s3.nodes.val (tbl s3 .A) tp.subs := by
    rw [hn3, ho3 .A (by simp)]; simpa using h2.marked
  have hB3' : AllOK nm s3.nodes.val (tbl s3 .B) tp.subs := fun k w hk => by
    rw [hB3 k] at hk; cases hk
  have hP3 := pending_card_le (nm := nm) s3.nodes.val (tbl s3 .B) (cs.toFinset.biUnion Term.subs)
  step with keep_spec hnm tp.subs (cs.toFinset.biUnion Term.subs) cs s3 c hI3
    (by rw [hn3']; exact hc) hM3 hB3'
    (fun a ha => Finset.subset_biUnion_of_mem Term.subs (List.mem_toFinset.2 ha))
    (by unfold Room; omega) as ⟨c2, s4, h4⟩
  have hc4 := h4.cost
  have hx4 : Extends s s4 := (Extends.of_eq hn3').trans h4.ext
  have hfilt : cs.filter (fun a => decide (AllIn tp.subs a)) =
      cs.filter (fun a => a.vars.all (· ∈ tp.vars)) := by
    apply List.filter_congr
    intro a _
    simp only [AllIn, var_mem_subs_iff]
    rw [Bool.eq_iff_iff]; simp [List.all_eq_true]
  have hrc := h4.repr
  rw [hfilt] at hrc
  step with cover_is_var_spec s4 p h4.inv (hx4.repr hp) (by unfold Room; omega) as ⟨b, s5, hb, hK5⟩
  have ht5 := hK5.ticks
  refine WP.spec_bind (Pₘ := fun r => Inv r.1 ∧ r.1.nodes.val = s4.nodes.val ∧
    r.1.ticks.val ≤ s5.ticks.val + 1 ∧
    (r.2 = true ↔ (∃ v, tp = Term.var v) ∧
      cs.filter (fun a => a.vars.all (· ∈ tp.vars)) = [])) ?_ ?_
  · cases b with
    | true =>
      simp only [↓reduceIte]
      step with cover_is_nil_spec hnm s5 c2 hK5.inv (by rw [hK5.nodes]; exact hrc)
        (by unfold Room; omega) as ⟨b1, s7, hb1, hK7⟩
      refine ⟨hK7.inv, by rw [hK7.nodes, hK5.nodes], by have := hK7.ticks; omega, ?_⟩
      exact ⟨fun h => ⟨hb.1 rfl, hb1.1 h⟩, fun h => hb1.2 h.2⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      refine ⟨hK5.inv, hK5.nodes, by omega, ?_⟩
      constructor
      · intro h; cases h
      · rintro ⟨hv, -⟩; exact absurd (hb.2 hv) (by simp)
  · rintro ⟨s6, tr⟩ hmid
    have hmid : Inv s6 ∧ s6.nodes.val = s4.nodes.val ∧ s6.ticks.val ≤ s5.ticks.val + 1 ∧
        (tr = true ↔ (∃ v, tp = Term.var v) ∧
          cs.filter (fun a => a.vars.all (· ∈ tp.vars)) = []) := hmid
    obtain ⟨hI6, hn6, ht6, htr⟩ := hmid
    have hx6 : Extends s s6 := hx4.trans (Extends.of_eq hn6)
    have hticks : s6.ticks.val ≤ s.ticks.val + ifaceCost tp cs := by unfold ifaceCost; omega
    cases tr with
    | true =>
      simp only [uncurry_apply_pair, ↓reduceIte, WP.spec_ok]
      obtain ⟨⟨v, hv⟩, hnil⟩ := htr.1 rfl
      refine ⟨hI6, hx6, ?_, hticks⟩
      rw [hnil]; subst hv; simp [bound, OptSpanAt]
    | false =>
      simp only [uncurry_apply_pair, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      refine ⟨hI6, hx6, ?_, hticks⟩
      have hbd : bound ⟨tp, tp, cs.filter fun a => a.vars.all (· ∈ tp.vars)⟩ =
          some ⟨tp, tp, cs.filter fun a => a.vars.all (· ∈ tp.vars)⟩ := by
        unfold bound
        split
        · next v h1 h2 => exact absurd (htr.2 ⟨⟨v, h1⟩, h2⟩) (by simp)
        · rfl
      rw [hbd]
      exact ⟨hx6.repr hp, hx6.repr hp, by rw [hn6]; exact hrc⟩

/-- `right_bound` returns the specification's right interface of the span,
as a boundary, within `ifaceCost` ticks. -/
theorem right_bound_spec (hnm : Function.Injective nm) (s : store.Store) (x : span.Span)
    {sx : Span} (hI : Inv s) (hx : SpanAt nm s.nodes.val x sx)
    (hroom : Room s (ifaceCost sx.r sx.c)) :
    cover.right_bound s x ⦃ r s' =>
      Inv s' ∧ Extends s s' ∧ OptSpanAt nm s'.nodes.val r (bound sx.rightIface) ∧
      s'.ticks.val ≤ s.ticks.val + ifaceCost sx.r sx.c ⦄ := by
  unfold cover.right_bound
  exact iface_spec hnm s x.r x.c hI hx.r hx.c hroom

/-- `left_bound` returns the specification's left interface of the span, as
a boundary, within `ifaceCost` ticks. -/
theorem left_bound_spec (hnm : Function.Injective nm) (s : store.Store) (x : span.Span)
    {sx : Span} (hI : Inv s) (hx : SpanAt nm s.nodes.val x sx)
    (hroom : Room s (ifaceCost sx.l sx.c)) :
    cover.left_bound s x ⦃ r s' =>
      Inv s' ∧ Extends s s' ∧ OptSpanAt nm s'.nodes.val r (bound sx.leftIface) ∧
      s'.ticks.val ≤ s.ticks.val + ifaceCost sx.l sx.c ⦄ := by
  unfold cover.left_bound
  exact iface_spec hnm s x.l x.c hI hx.l hx.c hroom
end RwLogVerified
