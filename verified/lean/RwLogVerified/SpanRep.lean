/-
# The representative of a span as written

`dom::rep` reads a span off the store and returns its representative
(`Sorts.repOf`): nothing when a side or a constraint is not first-order or
a constraint is a variable, and otherwise the normal store of the pair of
the two sides under the sorts and the disequalities the constraints say.

`first_order` walks a term with the stack of the store. Table `B` flags the
nodes already visited, so a node is examined once however often it occurs.
The walk stops at the first application of a variable.
-/
import RwLogVerified.Dom

open Aeneas Aeneas.Std Result

namespace RwLogVerified

open rwlog_core RwLog

variable {nm : Option Nat → Sym}

/-- A subterm of a first-order term is first-order. -/
theorem fo_of_mem_subs {t u : Pat} (h : u ∈ t.subs) (ht : t.firstOrder = true) :
    u.firstOrder = true := by
  induction t with
  | var v => simp only [Term.subs, Finset.mem_singleton] at h; subst h; rfl
  | sym f => simp only [Term.subs, Finset.mem_singleton] at h; subst h; rfl
  | app a b iha ihb =>
    simp only [Term.subs, Finset.mem_insert, Finset.mem_union] at h
    obtain ⟨h1, h2, -⟩ := firstOrder_app ht
    rcases h with rfl | h | h
    · exact ht
    · exact iha h h1
    · exact ihb h h2

/-- What `first_order` leaves. -/
structure FOPost (s s' : store.Store) (t : Pat) (S : Finset Pat) (b : Bool) : Prop where
  inv : Inv s'
  nodes : s'.nodes.val = s.nodes.val
  res : b = t.firstOrder
  tblA : tbl s' .A = tbl s .A
  cost : s'.ticks.val ≤ s.ticks.val + 5 + 9 * S.card
  mono : s.ticks.val ≤ s'.ticks.val

/-- The flagged nodes: the first part of a flagged application is not a
variable, and its parts are flagged or on the stack. -/
structure SeenFO (n0 : List store.Node) (Bt : Nat → Option Nat) (st : List store.Frame) :
    Prop where
  app : ∀ k (a b : store.TermId), Bt k ≠ none → n0[k]? = some (.App a b) →
    (∀ v, ¬ VarAt n0 a.val v) ∧
    (Bt a.val ≠ none ∨ ∃ f ∈ st, fkey f = a.val) ∧ (Bt b.val ≠ none ∨ ∃ f ∈ st, fkey f = b.val)

/-- When the stack is empty, every flagged term is first-order. -/
theorem SeenFO.fo {n0 : List store.Node} {Bt : Nat → Option Nat} (h : SeenFO n0 Bt []) :
    ∀ (t : Pat) (k : Nat), Repr nm n0 k t → Bt k ≠ none → t.firstOrder = true := by
  intro t
  induction t with
  | var v => intro _ _ _; rfl
  | sym f => intro _ _ _; rfl
  | app ta tb iha ihb =>
    intro k hk hB
    cases hk with
    | app hn ha hb =>
      obtain ⟨h0, h1, h2⟩ := h.app k _ _ hB hn
      refine Term.fo_app_mk (iha _ ha ?_) (ihb _ hb ?_) ?_
      · rcases h1 with h1 | ⟨f, hf, -⟩
        · exact h1
        · simp at hf
      · rcases h2 with h2 | ⟨f, hf, -⟩
        · exact h2
        · simp at hf
      · intro x e
        subst e
        cases ha with
        | var hv => exact h0 x hv

/-- The invariant of the loop: the walk goes on, or a variable was found
applied. -/
def FoInv (nm : Option Nat → Sym) (s0 : store.Store) (tp : Pat) (p : Nat)
    (S : Finset Pat) (B : Nat) : store.Store × Bool → Prop
  | (s, ok) => Wf s ∧ s.nodes.val = s0.nodes.val ∧ tbl s .A = tbl s0 .A ∧
    if ok then (∀ f ∈ stk s, ∃ u ∈ tp.subs, Repr nm s0.nodes.val (fkey f) u) ∧
      SeenFO s0.nodes.val (tbl s .B) (stk s) ∧
      (tbl s .B p ≠ none ∨ ∃ f ∈ stk s, fkey f = p) ∧
      s.ticks.val + 1 + 2 * (stk s).length +
        9 * (pending nm s.nodes.val (tbl s .B) S).card ≤ B
    else stk s = [] ∧ tp.firstOrder = false ∧ s.ticks.val + 1 ≤ B

def FoBodyPost (nm : Option Nat → Sym) (s0 : store.Store) (tp : Pat) (p : Nat)
    (S : Finset Pat) (B : Nat) (t0 : Nat) :
    ControlFlow (store.Store × Bool) (Bool × store.Store) → Prop
  | .done (b, s') => Wf s' ∧ stk s' = [] ∧ s'.nodes.val = s0.nodes.val ∧
      tbl s' .A = tbl s0 .A ∧ b = tp.firstOrder ∧ s'.ticks.val ≤ B ∧ t0 ≤ s'.ticks.val
  | .cont x => FoInv nm s0 tp p S B x ∧ t0 < x.1.ticks.val

theorem first_order_body_spec (hnm : Function.Injective nm) (s0 : store.Store)
    (tp : Pat) (p : Nat) (S : Finset Pat) (B : Nat)
    (hB : 40 * B + 100 ≤ Usize.max)
    (hp : Repr nm s0.nodes.val p tp) (hS : tp.subs ⊆ S) (s : store.Store) (ok : Bool)
    (h : FoInv nm s0 tp p S B (s, ok)) :
    dom.first_order_loop.body s ok ⦃ r => FoBodyPost nm s0 tp p S B s.ticks.val r ⦄ := by
  unfold dom.first_order_loop.body
  obtain ⟨hW, hn, hTA, h⟩ := h
  cases ok with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨hemp, hnfo, hc⟩ := h
    step with pop_w s hW (by unfold Room; omega) as ⟨o, s1, e1, e2, e3, hW1, eo, est⟩
    rw [hemp] at eo est
    simp only [List.head?_nil, List.tail_nil] at eo est
    subst eo
    simp only [WP.spec_ok]
    exact ⟨hW1, est, by rw [e1, hn], by rw [e2, hTA], hnfo.symm, by omega, by omega⟩
  | true =>
    simp only [↓reduceIte] at h
    obtain ⟨hFr, hSeen, hRoot, hc⟩ := h
    have hN : NodesOK s.nodes.val := hW.nodesOK
    step with pop_w s hW (by unfold Room; omega) as ⟨o, s1, e1, e2, e3, hW1, eo, est⟩
    cases hst : stk s with
    | nil =>
      rw [hst] at eo est hSeen hRoot
      simp only [List.head?_nil, List.tail_nil] at eo est
      subst eo
      simp only [WP.spec_ok]
      refine ⟨hW1, est, by rw [e1, hn], by rw [e2, hTA], ?_, by omega, by omega⟩
      have hBp : tbl s .B p ≠ none := by
        rcases hRoot with h | ⟨f, hf, -⟩
        · exact h
        · simp at hf
      exact (hSeen.fo tp p hp hBp).symm
    | cons fr st =>
      rw [hst] at eo est hSeen hRoot hFr hc
      simp only [List.head?_cons, List.tail_cons] at eo est
      subst eo
      simp only [List.length_cons] at hc
      obtain ⟨tq, htq, hq0⟩ := hFr fr List.mem_cons_self
      have hq : Repr nm s.nodes.val (fkey fr) tq := by rw [hn]; exact hq0
      simp only [node_of_eq]
      step with get_flag_w s1 .B (fid fr) hW1 (by rw [e1, fid_val]; exact hq.lt)
        (by unfold Room; omega) as ⟨o1, s2, ho1, hK2⟩
      rw [e2, fid_val] at ho1
      have ht2 := hK2.ticks
      have hn2 : s2.nodes.val = s.nodes.val := by rw [hK2.nodes, e1]
      have htb2 : tbl s2 = tbl s := by rw [hK2.tbl, e2]
      have hstk2 : stk s2 = st := by rw [hK2.stk, est]
      have hFr' : ∀ f ∈ st, ∃ u ∈ tp.subs, Repr nm s0.nodes.val (fkey f) u :=
        fun f hf => hFr f (List.mem_cons_of_mem _ hf)
      cases hBq : tbl s .B (fkey fr) with
      | some w =>
        rw [hBq] at ho1
        simp only [Option.map_some] at ho1
        subst ho1
        simp only [WP.spec_ok]
        refine ⟨⟨hK2.wf, by rw [hn2, hn], by rw [htb2, hTA], ?_⟩, by simp only; omega⟩
        simp only [↓reduceIte]
        rw [hstk2, htb2, hn2]
        refine ⟨hFr', ⟨fun k a b hk hnk => ?_⟩, ?_, by omega⟩
        · obtain ⟨h0, h1, h2⟩ := hSeen.app k a b hk hnk
          refine ⟨h0, ?_, ?_⟩
          · rcases h1 with h1 | ⟨f, hf, e⟩
            · exact Or.inl h1
            · rcases List.mem_cons.1 hf with rfl | hf
              · left; rw [← e, hBq]; simp
              · exact Or.inr ⟨f, hf, e⟩
          · rcases h2 with h2 | ⟨f, hf, e⟩
            · exact Or.inl h2
            · rcases List.mem_cons.1 hf with rfl | hf
              · left; rw [← e, hBq]; simp
              · exact Or.inr ⟨f, hf, e⟩
        · rcases hRoot with h | ⟨f, hf, e⟩
          · exact Or.inl h
          · rcases List.mem_cons.1 hf with rfl | hf
            · left; rw [← e, hBq]; simp
            · exact Or.inr ⟨f, hf, e⟩
      | none =>
        rw [hBq] at ho1
        simp only [Option.map_none] at ho1
        subst ho1
        simp only
        have hP := pending_set_card hnm hN hq hBq (hS htq) 1
        step with set_flag_w s2 .B (fid fr) true hK2.wf (by rw [hn2, fid_val]; exact hq.lt)
          (by unfold Room; omega) as ⟨s3, g1, g2, g3, g4, g5, g6⟩
        rw [htb2, fid_val] at g4
        simp only [↓reduceIte] at g4
        have hn3 : s3.nodes.val = s.nodes.val := by rw [g1, hn2]
        have hA3 : tbl s3 .A = tbl s .A := by rw [g5 .A (by simp), htb2]
        have hstk3 : stk s3 = st := by rw [g6, hstk2]
        step with read_w s3 (fid fr) g3 (by rw [hn3, fid_val]; exact hq.lt)
          (by unfold Room; omega) as ⟨nd, s4, hnd, hK4⟩
        rw [hn3, fid_val] at hnd
        have ht4 := hK4.ticks
        have hn4 : s4.nodes.val = s.nodes.val := by rw [hK4.nodes, hn3]
        have htb4B : tbl s4 .B = Function.update (tbl s .B) (fkey fr) (some 1) := by
          rw [hK4.tbl, g4]
        have hA4 : tbl s4 .A = tbl s .A := by rw [hK4.tbl, hA3]
        have hstk4 : stk s4 = st := by rw [hK4.stk, hstk3]
        have hnd0 : s0.nodes.val[fkey fr]? = some nd := by rw [← hn]; exact hnd
        have hgrow : ∀ k, tbl s .B k ≠ none →
            Function.update (tbl s .B) (fkey fr) (some 1) k ≠ none := by
          intro k hk
          by_cases e : k = fkey fr
          · rw [e]; simp
          · rw [Function.update_of_ne e]; exact hk
        have hself : Function.update (tbl s .B) (fkey fr) (some 1) (fkey fr) ≠ none := by simp
        have hseen : ∀ st' : List store.Frame, (∀ f ∈ st, f ∈ st') →
            (∀ a b : store.TermId, nd = .App a b → (∀ v, ¬ VarAt s0.nodes.val a.val v) ∧
              (∃ f ∈ st', fkey f = a.val) ∧ ∃ f ∈ st', fkey f = b.val) →
            SeenFO s0.nodes.val (Function.update (tbl s .B) (fkey fr) (some 1)) st' := by
          intro st' hsub happ
          refine ⟨fun k a b hk hnk => ?_⟩
          by_cases e : k = fkey fr
          · subst e
            rw [hnd0] at hnk
            cases hnk
            obtain ⟨h0, h1, h2⟩ := happ a b rfl
            exact ⟨h0, Or.inr h1, Or.inr h2⟩
          · rw [Function.update_of_ne e] at hk
            obtain ⟨h0, h1, h2⟩ := hSeen.app k a b hk hnk
            refine ⟨h0, ?_, ?_⟩
            · rcases h1 with h1 | ⟨f, hf, e'⟩
              · exact Or.inl (hgrow _ h1)
              · rcases List.mem_cons.1 hf with rfl | hf
                · left; rw [← e']; exact hself
                · exact Or.inr ⟨f, hsub f hf, e'⟩
            · rcases h2 with h2 | ⟨f, hf, e'⟩
              · exact Or.inl (hgrow _ h2)
              · rcases List.mem_cons.1 hf with rfl | hf
                · left; rw [← e']; exact hself
                · exact Or.inr ⟨f, hsub f hf, e'⟩
        have hroot : ∀ st' : List store.Frame, (∀ f ∈ st, f ∈ st') →
            Function.update (tbl s .B) (fkey fr) (some 1) p ≠ none ∨ ∃ f ∈ st', fkey f = p := by
          intro st' hsub
          rcases hRoot with h | ⟨f, hf, e⟩
          · exact Or.inl (hgrow _ h)
          · rcases List.mem_cons.1 hf with rfl | hf
            · left; rw [← e]; exact hself
            · exact Or.inr ⟨f, hsub f hf, e⟩
        have hplain : (∀ a b, nd ≠ .App a b) →
            FoBodyPost nm s0 tp p S B s.ticks.val (.cont (s4, true)) := by
          intro hna
          refine ⟨⟨hK4.wf, by rw [hn4, hn], by rw [hA4, hTA], ?_⟩, by simp only; omega⟩
          simp only [↓reduceIte]
          rw [hstk4, htb4B, hn4]
          exact ⟨hFr', hseen st (fun _ h => h) (fun a b e => absurd e (hna a b)),
            hroot st (fun _ h => h), by omega⟩
        cases nd with
        | V0 => simp only [WP.spec_ok]; exact hplain (fun a b e => by cases e)
        | VL a => simp only [WP.spec_ok]; exact hplain (fun a b e => by cases e)
        | VR a => simp only [WP.spec_ok]; exact hplain (fun a b e => by cases e)
        | Sym g => simp only [WP.spec_ok]; exact hplain (fun a b e => by cases e)
        | Nil => simp only [WP.spec_ok]; exact hplain (fun a b e => by cases e)
        | App a b =>
          obtain ⟨ta, tb, e, ha, hb⟩ := hq0.of_app hnd0
          subst e
          simp only
          step with is_var_w s4 a hK4.wf (q := ta) (by rw [hn4, hn]; exact ha)
            (by unfold Room; omega) as ⟨b1, s5, hb1, hK5⟩
          have ht5 := hK5.ticks
          have hn5 : s5.nodes.val = s.nodes.val := by rw [hK5.nodes, hn4]
          split
          · rename_i hbt
            obtain ⟨v, rfl⟩ := hb1.1 hbt
            step with drop_stack_w s5 hK5.wf (by unfold Room; omega) as ⟨s6, d1, d2, d3, hW6, d5⟩
            refine ⟨⟨hW6, by rw [d1, hn5, hn], by rw [d2, hK5.tbl, hA4, hTA], ?_⟩,
              by simp only; omega⟩
            simp only [Bool.false_eq_true, ↓reduceIte]
            refine ⟨d5, ?_, by omega⟩
            cases hfo : tp.firstOrder with
            | false => rfl
            | true =>
              have := fo_of_mem_subs htq hfo
              simp [Term.firstOrder] at this
          · rename_i hbf
            have hnv : ∀ v, ta ≠ .var v := fun v e => hbf (hb1.2 ⟨v, e⟩)
            step with push_w s5 (.Visit b b) hK5.wf (by unfold Room; omega)
              as ⟨s6, b1', b2, b3, hW6, b5⟩
            step with push_w s6 (.Visit a a) hW6 (by unfold Room; omega)
              as ⟨s7, c1, c2, c3, hW7, c5⟩
            have hn7 : s7.nodes.val = s.nodes.val := by rw [c1, b1', hn5]
            have hstk7 : stk s7 = .Visit a a :: .Visit b b :: st := by
              rw [c5, b5, hK5.stk, hstk4]
            refine ⟨⟨hW7, by rw [hn7, hn], by rw [c2, b2, hK5.tbl, hA4, hTA], ?_⟩,
              by simp only; omega⟩
            simp only [↓reduceIte]
            rw [hstk7, c2, b2, hK5.tbl, htb4B, hn7]
            have hsub : ∀ f ∈ st, f ∈ store.Frame.Visit a a :: store.Frame.Visit b b :: st :=
              fun f hf => by simp [hf]
            refine ⟨?_, hseen _ hsub ?_, hroot _ hsub, ?_⟩
            · intro f hf
              simp only [List.mem_cons] at hf
              rcases hf with rfl | rfl | hf
              · exact ⟨ta, Term.subs_trans htq (by simp [Term.subs, Term.self_mem_subs]), ha⟩
              · exact ⟨tb, Term.subs_trans htq (by simp [Term.subs, Term.self_mem_subs]), hb⟩
              · exact hFr' f hf
            · intro a' b' e
              cases e
              refine ⟨fun v hv => hnv v ?_, ⟨.Visit a a, by simp, rfl⟩, ⟨.Visit b b, by simp, rfl⟩⟩
              exact ha.unique (Repr.var hv)
            · simp only [List.length_cons]
              omega

/-- `first_order` decides whether a term is first-order. It spends five
ticks, and nine for each term of `S`. -/
theorem first_order_spec (hnm : Function.Injective nm) (s : store.Store) (p : store.TermId)
    {t : Pat} (S : Finset Pat) (hI : Inv s) (hp : Repr nm s.nodes.val p.val t)
    (hS : t.subs ⊆ S) (hroom : Room s (5 + 9 * S.card)) :
    dom.first_order s p ⦃ b s' => FOPost s s' t S b ⦄ := by
  unfold dom.first_order dom.first_order_loop
  have hroom' := hroom
  unfold Room at hroom'
  step with clear_w s .B hI.toWf (by unfold Room; omega) as ⟨s0, z1, z2, hW0, z4, z5, z6⟩
  step with push_w s0 (.Visit p p) hW0 (by unfold Room; omega) as ⟨s1, a1, a2, a3, hW1, a5⟩
  rw [z6, hI.empty] at a5
  have hP := pending_card_le (nm := nm) s0.nodes.val (tbl s0 .B) S
  have hp0 : Repr nm s0.nodes.val p.val t := by rw [z1]; exact hp
  let B := s.ticks.val + 5 + 9 * S.card
  have hloop := loop.spec_decr_nat
    (fun y : store.Store × Bool => B + 1 - y.1.ticks.val)
    (fun y => FoInv nm s0 t p.val S B y ∧ s.ticks.val ≤ y.1.ticks.val)
    (fun y : Bool × store.Store => FOPost s y.2 t S y.1)
    (fun y : store.Store × Bool => dom.first_order_loop.body y.1 y.2) (s1, true)
    (by
      rintro ⟨y, ok⟩ ⟨hinv, hy⟩
      refine WP.spec_mono (first_order_body_spec hnm s0 t p.val S B (by omega) hp0 hS y ok
        hinv) ?_
      intro r hr
      cases r with
      | done z =>
        obtain ⟨b, z⟩ := z
        obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hr
        refine ⟨⟨h1, h2⟩, by rw [h3, z1], h5, by rw [h4, z5 .A (by simp)], by omega, ?_⟩
        exact Nat.le_trans hy h7
      | cont y' =>
        obtain ⟨h1, h2⟩ := hr
        obtain ⟨z, ok'⟩ := y'
        have hz : z.ticks.val + 1 ≤ B := by
          obtain ⟨-, -, -, h⟩ := h1
          cases ok' with
          | false => simp only [Bool.false_eq_true, ↓reduceIte] at h; exact h.2.2
          | true => simp only [↓reduceIte] at h; omega
        simp only at hy h2
        exact ⟨⟨h1, by simp only; omega⟩, by simp only; omega⟩)
    ⟨⟨hW1, a1, by rw [a2], by
      simp only [↓reduceIte]
      rw [a5, a2, a1]
      refine ⟨?_, ⟨fun k a b hk => absurd (z4 k) hk⟩,
        Or.inr ⟨_, List.mem_singleton_self _, rfl⟩, ?_⟩
      · intro f hf
        simp only [List.mem_singleton] at hf
        subst hf
        exact ⟨t, Term.self_mem_subs t, hp0⟩
      · simp only [List.length_singleton]
        omega⟩, by simp only; omega⟩
  exact hloop

/-- `is_atom` decides whether a term can be a constraint. It spends six
ticks, and nine for each term of `S`. -/
theorem is_atom_spec (hnm : Function.Injective nm) (s : store.Store) (p : store.TermId)
    {t : Pat} (S : Finset Pat) (hI : Inv s) (hp : Repr nm s.nodes.val p.val t)
    (hS : t.subs ⊆ S) (hroom : Room s (6 + 9 * S.card)) :
    dom.is_atom s p ⦃ b s' =>
      Inv s' ∧ s'.nodes.val = s.nodes.val ∧ s'.ticks.val ≤ s.ticks.val + 6 + 9 * S.card ∧
        s.ticks.val ≤ s'.ticks.val ∧ b = t.isAtom ⦄ := by
  unfold dom.is_atom
  have hroom' := hroom
  unfold Room at hroom'
  step with is_var_w s p hI.toWf hp (by unfold Room; omega) as ⟨b, s1, hb, hK⟩
  have K1 := hK.kept hI
  have ht1 := K1.ticks
  split
  · rename_i hbt
    obtain ⟨v, rfl⟩ := hb.1 hbt
    simp only [WP.spec_ok]
    exact ⟨K1.inv, K1.nodes, by omega, by omega, rfl⟩
  · rename_i hbf
    refine WP.spec_mono (first_order_spec hnm s1 p S K1.inv (by rw [K1.nodes]; exact hp) hS
      (by unfold Room; omega)) ?_
    rintro ⟨b', s'⟩ h
    have h1 := h.cost
    have h2 := h.mono
    refine ⟨h.inv, by rw [h.nodes, K1.nodes], by omega, by omega, ?_⟩
    rw [h.res]
    cases t with
    | var v => exact absurd (hb.2 ⟨v, rfl⟩) hbf
    | sym f => rfl
    | app a b => rfl

/-- `among` decides whether a term is a member of a list. -/
theorem among_loop_spec (hnm : Function.Injective nm) :
    ∀ (L : List Pat) (s : store.Store) (n l : store.TermId) {tn : Pat},
    Inv s → Repr nm s.nodes.val n.val tn → Repr nm s.nodes.val l.val (encList (nm none) L) →
    Room s (2 * L.length + 1) →
    dom.among_loop s n false l true ⦃ res s' =>
      Inv s' ∧ s'.nodes.val = s.nodes.val ∧ tbl s' = tbl s ∧
        s'.ticks.val ≤ s.ticks.val + 2 * L.length + 1 ∧ s.ticks.val ≤ s'.ticks.val ∧
        res = decide (tn ∈ L) ⦄ := by
  intro L
  induction L with
  | nil =>
    intro s n l tn hI hn hl hroom
    have hroom' := hroom
    unfold Room at hroom'
    unfold dom.among_loop
    rw [loop]
    simp only [dom.among_loop.body, ↓reduceIte]
    step with uncons_repr s l hI.toWf (p := Term.sym (nm none)) hl (by unfold Room; omega)
      as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    subst hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    simp only [uncurry, bind_ok]
    rw [loop]
    simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, WP.spec_ok]
    exact ⟨K1.inv, K1.nodes, K1.tbl, by simp only [List.length_nil]; omega, by omega, by simp⟩
  | cons p L ih =>
    intro s n l tn hI hn hl hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons] at hroom'
    unfold dom.among_loop
    rw [loop]
    simp only [dom.among_loop.body, ↓reduceIte]
    step with uncons_repr s l hI.toWf (p := Term.app p (encList (nm none) L)) hl
      (by unfold Room; omega) as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    obtain ⟨m, rest, rfl, rp, rrest⟩ := hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    step with same_spec s1 m n K1.inv (by unfold Room; omega) as ⟨r1, hres, K2⟩
    obtain ⟨b, s2⟩ := r1
    simp only at hres K2
    have ht2 := K2.ticks
    have hn2 : s2.nodes.val = s.nodes.val := by rw [K2.nodes, K1.nodes]
    have htb2 : tbl s2 = tbl s := by rw [K2.tbl, K1.tbl]
    by_cases e : m.val = n.val
    · have : b = true := by simp [hres, e]
      subst this
      have hpt : tn = p := by rw [e] at rp; exact hn.unique rp
      simp only [↓reduceIte, uncurry, bind_ok]
      rw [loop]
      simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, WP.spec_ok]
      exact ⟨K2.inv, hn2, htb2, by simp only [List.length_cons]; omega, by omega, by simp [hpt]⟩
    · have : b = false := by simp [hres, e]
      subst this
      have hpt : tn ≠ p := fun h => e (Repr.inj hnm hI.nodesOK rp (h ▸ hn))
      simp only [Bool.false_eq_true, ↓reduceIte, uncurry, bind_ok]
      have IH := ih s2 n rest (tn := tn) K2.inv (by rw [hn2]; exact hn) (by rw [hn2]; exact rrest)
        (by unfold Room; omega)
      unfold dom.among_loop at IH
      refine WP.spec_mono IH ?_
      rintro ⟨res, s'⟩ ⟨hI', hn', htb', ht', hm', hres'⟩
      refine ⟨hI', by rw [hn', hn2], by rw [htb', htb2], by simp only [List.length_cons]; omega,
        by omega, ?_⟩
      rw [hres']
      simp [hpt]

/-- What `con` says of a constraint. -/
def ConPost (nm : Option Nat → Sym) (nodes : List store.Node) (t : Pat) : dom.Con → Prop
  | .Sort h => ∃ n p, t = .app (.sym n) p ∧ Repr nm nodes h.val (.sym n)
  | .Differ p q => ∃ tp tq, t = .app (.app (.sym neSym) tp) tq ∧ Repr nm nodes p.val tp ∧
      Repr nm nodes q.val tq
  | .Never => Sorts.atomOf t = [] ∧ Sorts.exclOf t = [[]]

/-- `con` reads what a constraint says, in at most four ticks. -/
theorem con_spec (hnm : Function.Injective nm) (hz : nm none = "") (s : store.Store) (ne : U32)
    (hne : nm (some ne.val) = neSym) (c : store.TermId) {t : Pat} (hI : Inv s)
    (hc : Repr nm s.nodes.val c.val t) (hroom : Room s 4) :
    dom.con s ne c ⦃ r s' =>
      Inv s' ∧ s'.nodes.val = s.nodes.val ∧ tbl s' = tbl s ∧
        s'.ticks.val ≤ s.ticks.val + 4 ∧ s.ticks.val ≤ s'.ticks.val ∧
        ConPost nm s.nodes.val t r ⦄ := by
  unfold dom.con
  have hroom' := hroom
  unfold Room at hroom'
  step with read_spec s c hI hc.lt (by unfold Room; omega) as ⟨n, s1, hn, K1⟩
  have ht1 := K1.ticks
  cases hc with
  | var hv =>
    rename_i v0
    obtain ⟨m, hm, hvn⟩ := hv.node
    rw [hm] at hn
    cases hn
    have fin : Inv s1 ∧ s1.nodes.val = s.nodes.val ∧ tbl s1 = tbl s ∧
        s1.ticks.val ≤ s.ticks.val + 4 ∧ s.ticks.val ≤ s1.ticks.val ∧
        ConPost nm s.nodes.val (.var v0) .Never :=
      ⟨K1.inv, K1.nodes, K1.tbl, by omega, by omega, rfl, rfl⟩
    cases n <;> first | exact hvn.elim | (simp only [WP.spec_ok]; exact fin)
  | sym h =>
    rw [h] at hn; cases hn
    simp only [WP.spec_ok]
    exact ⟨K1.inv, K1.nodes, K1.tbl, by omega, by omega, rfl, rfl⟩
  | nil h =>
    rw [h] at hn; cases hn
    simp only [WP.spec_ok]
    exact ⟨K1.inv, K1.nodes, K1.tbl, by omega, by omega, rfl, rfl⟩
  | app h ha hb =>
    rename_i a b ta tb
    rw [h] at hn; cases hn
    simp only
    step with read_spec s1 a K1.inv (by rw [K1.nodes]; exact ha.lt) (by unfold Room; omega)
      as ⟨n1, s2, hn1, K2⟩
    rw [K1.nodes] at hn1
    have ht2 := K2.ticks
    have hn2 : s2.nodes.val = s.nodes.val := by rw [K2.nodes, K1.nodes]
    have htb2 : tbl s2 = tbl s := by rw [K2.tbl, K1.tbl]
    cases ha with
    | var hv =>
      rename_i v0
      obtain ⟨m, hm, hvn⟩ := hv.node
      rw [hm] at hn1
      cases hn1
      have fin : Inv s2 ∧ s2.nodes.val = s.nodes.val ∧ tbl s2 = tbl s ∧
          s2.ticks.val ≤ s.ticks.val + 4 ∧ s.ticks.val ≤ s2.ticks.val ∧
          ConPost nm s.nodes.val (.app (.var v0) tb) .Never :=
        ⟨K2.inv, hn2, htb2, by omega, by omega, rfl, rfl⟩
      cases n1 <;> first | exact hvn.elim | (simp only [WP.spec_ok]; exact fin)
    | sym h1 =>
      rw [h1] at hn1; cases hn1
      simp only [WP.spec_ok]
      exact ⟨K2.inv, hn2, htb2, by omega, by omega, _, tb, rfl, .sym h1⟩
    | nil h1 =>
      rw [h1] at hn1; cases hn1
      simp only [WP.spec_ok]
      exact ⟨K2.inv, hn2, htb2, by omega, by omega, _, tb, rfl, .nil h1⟩
    | app h1 ha1 hb1 =>
      rename_i a1 b1 ta1 tb1
      rw [h1] at hn1; cases hn1
      simp only
      step with read_spec s2 a1 K2.inv (by rw [hn2]; exact ha1.lt) (by unfold Room; omega)
        as ⟨n2, s3, hn3', K3⟩
      rw [hn2] at hn3'
      have ht3 := K3.ticks
      have hn3 : s3.nodes.val = s.nodes.val := by rw [K3.nodes, hn2]
      have htb3 : tbl s3 = tbl s := by rw [K3.tbl, htb2]
      cases ha1 with
      | var hv =>
        rename_i v0
        obtain ⟨m, hm, hvn⟩ := hv.node
        rw [hm] at hn3'
        cases hn3'
        have fin : Inv s3 ∧ s3.nodes.val = s.nodes.val ∧ tbl s3 = tbl s ∧
            s3.ticks.val ≤ s.ticks.val + 4 ∧ s.ticks.val ≤ s3.ticks.val ∧
            ConPost nm s.nodes.val (.app (.app (.var v0) tb1) tb) .Never :=
          ⟨K3.inv, hn3, htb3, by omega, by omega, rfl, rfl⟩
        cases n2 <;> first | exact hvn.elim | (simp only [WP.spec_ok]; exact fin)
      | sym h2 =>
        rename_i w
        rw [h2] at hn3'; cases hn3'
        simp only
        step with word_eq_spec s3 w ne K3.inv (by unfold Room; omega) as ⟨bw, s4, hbw, K4⟩
        have ht4 := K4.ticks
        split
        · rename_i hbt
          have hw : w = ne := by simpa [hbw] using hbt
          subst hw
          simp only [WP.spec_ok]
          refine ⟨K4.inv, by rw [K4.nodes, hn3], by rw [K4.tbl, htb3], by omega, by omega, ?_⟩
          exact ⟨tb1, tb, by rw [hne], hb1, hb⟩
        · rename_i hbf
          have hw : w ≠ ne := by simpa [hbw] using hbf
          simp only [WP.spec_ok]
          refine ⟨K4.inv, by rw [K4.nodes, hn3], by rw [K4.tbl, htb3], by omega, by omega, rfl,
            ?_⟩
          have : nm (some w.val) ≠ neSym := by
            rw [← hne]
            intro e
            have := hnm e
            simp only [Option.some.injEq] at this
            exact hw (UScalar.eq_of_val_eq this)
          simp [Sorts.exclOf, this]
      | nil h2 =>
        rw [h2] at hn3'; cases hn3'
        simp only [WP.spec_ok]
        refine ⟨K3.inv, hn3, htb3, by omega, by omega, rfl, ?_⟩
        simp [Sorts.exclOf, hz, neSym]
      | app h2 _ _ =>
        rw [h2] at hn3'; cases hn3'
        simp only [WP.spec_ok]
        exact ⟨K3.inv, hn3, htb3, by omega, by omega, rfl, rfl⟩

/-! ## The parts of the constraints -/

/-- A sort that has a member is declared. -/
theorem kids_lookup {S : Sorts} : ∀ (t : GTerm) (n : Name) (e : Nat),
    (Sorts.kids S t n e).isSome = true → n ∈ Sorts.names S
  | .sym f, n, e, h => by
    simp only [Sorts.kids, Sorts.step] at h
    cases hd : S.lookup n with
    | none => simp [hd] at h
    | some d =>
      have := Sorts.mem_of_lookup hd
      simp only [Sorts.names, List.mem_toFinset, List.mem_flatMap]
      exact ⟨(n, d), this, by simp⟩
  | .app t u, n, e, h => by
    simp only [Sorts.kids] at h
    cases hk : Sorts.kids S t n (e + 1) with
    | none => simp [hk] at h
    | some ks => exact kids_lookup t n (e + 1) (by simp [hk])

theorem mem_names {S : Sorts} {n : Name} {g : GTerm} (h : Sorts.mem S n g = true) :
    n ∈ Sorts.names S :=
  kids_lookup g n 0 h

/-- A constraint the store can state: it can be a constraint, the sort it
names is one of `U`, and it is not one that never holds. -/
def ConOK (U : List Name) (c : Pat) : Prop :=
  c.isAtom = true ∧ (∀ a ∈ Sorts.atomOf c, a.1 ∈ U) ∧ [] ∉ Sorts.exclOf c

/-- A span with a constraint on an undeclared sort, or one that never
holds, relates nothing. -/
theorem spanProb_dead {S : Sorts} {sp : Span} {c : Pat} (hc : c ∈ sp.c)
    (h : (∃ a ∈ Sorts.atomOf c, a.1 ∉ Sorts.names S) ∨ [] ∈ Sorts.exclOf c) :
    (Sorts.spanProb sp).Den S = ∅ := by
  ext g
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨σ, ⟨-, ha, hx⟩, -⟩
  rcases h with ⟨a, ha', hn⟩ | h
  · exact hn (mem_names (ha a (List.mem_flatMap.2 ⟨c, hc, ha'⟩)))
  · exact hx [] (List.mem_flatMap.2 ⟨c, hc, h⟩) (fun p hp => by simp at hp)

/-- The problem of a span as the store states it: the sorts and the
exclusions of the constraints, the last first. -/
def spanProbR (sp : Span) : Sorts.Prob :=
  ⟨Sorts.tpair sp.l sp.r, [], (sp.c.flatMap Sorts.atomOf).reverse,
    (sp.c.flatMap Sorts.exclOf).reverse⟩

theorem spanProbR_den {S : Sorts} (sp : Span) :
    (spanProbR sp).Den S = (Sorts.spanProb sp).Den S := by
  simp only [Sorts.Prob.Den, Sorts.Prob.Sol, spanProbR, Sorts.spanProb, List.mem_reverse]

theorem spanProbR_fo {sp : Span} (hfo : sp.firstOrder = true) : (spanProbR sp).FO := by
  have h := Sorts.spanProb_fo hfo
  exact ⟨h.t, h.e, fun a ha => h.a a (List.mem_reverse.1 ha),
    fun E hE => h.x E (List.mem_reverse.1 hE)⟩

/-- The ticks `parts` may take in its loop. -/
def partsCost (u : Nat) (Cs : List Pat) : Nat :=
  (Cs.map fun c => 9 * c.subs.card + 2 * u + 14).sum + 1

theorem parts_loop_spec (hnm : Function.Injective nm) (hz : nm none = "") (U : List Name)
    (ne : U32) (hne : nm (some ne.val) = neSym) :
    ∀ (Cs : List Pat) (As : List (Name × Pat)) (Xs : List (Eqns Nat)) (s : store.Store)
      (names nil atoms excl c : store.TermId),
    Inv s → Repr nm s.nodes.val names.val (namesPat (nm none) U) →
    Repr nm s.nodes.val nil.val (.sym (nm none)) →
    Repr nm s.nodes.val atoms.val (encList (nm none) (As.map ppair)) →
    Repr nm s.nodes.val excl.val (encX nm Xs) →
    Repr nm s.nodes.val c.val (encList (nm none) Cs) →
    Room s (partsCost U.length Cs) →
    dom.parts_loop s names ne nil atoms excl c true true ⦃ r =>
      Inv r.1 ∧ Extends s r.1 ∧ r.1.ticks.val ≤ s.ticks.val + partsCost U.length Cs ∧
        (r.2.2.2 = true ↔ ∀ c ∈ Cs, ConOK U c) ∧
        (r.2.2.2 = true →
          Repr nm r.1.nodes.val r.2.1.val
            (encList (nm none) (((Cs.flatMap Sorts.atomOf).reverse ++ As).map ppair)) ∧
          Repr nm r.1.nodes.val r.2.2.1.val
            (encX nm ((Cs.flatMap Sorts.exclOf).reverse ++ Xs))) ⦄ := by
  intro Cs
  induction Cs with
  | nil =>
    intro As Xs s names nil atoms excl c hI hU hnil hat hex hc hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [partsCost, List.map_nil, List.sum_nil] at hroom'
    unfold dom.parts_loop
    rw [loop]
    simp only [dom.parts_loop.body, ↓reduceIte]
    step with uncons_repr s c hI.toWf (p := Term.sym (nm none)) hc (by unfold Room; omega)
      as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    subst hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    simp only [uncurry, bind_ok]
    rw [loop]
    simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, WP.spec_ok]
    refine ⟨K1.inv, Extends.of_eq K1.nodes (by omega), by simp only [partsCost]; omega,
      by simp, fun _ => ?_⟩
    rw [K1.nodes]
    exact ⟨by simpa using hat, by simpa using hex⟩
  | cons k0 Cs ih =>
    intro As Xs s names nil atoms excl c hI hU hnil hat hex hc hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [partsCost, List.map_cons, List.sum_cons] at hroom'
    have hpc : partsCost U.length (k0 :: Cs) =
        9 * k0.subs.card + 2 * U.length + 14 + partsCost U.length Cs := by
      simp only [partsCost, List.map_cons, List.sum_cons]; omega
    have hpc' : partsCost U.length Cs = (Cs.map fun c => 9 * c.subs.card + 2 * U.length + 14).sum + 1 :=
      rfl
    unfold dom.parts_loop
    rw [loop]
    simp only [dom.parts_loop.body, ↓reduceIte]
    step with uncons_repr s c hI.toWf (p := Term.app k0 (encList (nm none) Cs)) hc
      (by unfold Room; omega) as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    obtain ⟨k, rest, rfl, rk, rrest⟩ := hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    step with is_atom_spec hnm s1 k k0.subs K1.inv (by rw [K1.nodes]; exact rk)
      (Finset.Subset.refl _) (by unfold Room; omega) as ⟨r2, hI2, hn2', ht2, hm2, hb⟩
    obtain ⟨b, s2⟩ := r2
    simp only at hI2 hn2' ht2 hm2 hb
    have hn2 : s2.nodes.val = s.nodes.val := by rw [hn2', K1.nodes]
    -- leaving the loop with nothing
    have hexit : ∀ s4 : store.Store, Inv s4 → s4.nodes.val = s.nodes.val →
        s.ticks.val ≤ s4.ticks.val →
        s4.ticks.val ≤ s.ticks.val + partsCost U.length (k0 :: Cs) → ¬ ConOK U k0 →
        Inv s4 ∧ Extends s s4 ∧ s4.ticks.val ≤ s.ticks.val + partsCost U.length (k0 :: Cs) ∧
          (False ↔ ∀ c ∈ k0 :: Cs, ConOK U c) ∧
          (False →
            Repr nm s4.nodes.val atoms.val (encList (nm none)
              ((((k0 :: Cs).flatMap Sorts.atomOf).reverse ++ As).map ppair)) ∧
            Repr nm s4.nodes.val excl.val
              (encX nm (((k0 :: Cs).flatMap Sorts.exclOf).reverse ++ Xs))) := by
      intro s4 hI4 hn4 hm4 ht4 hbad
      refine ⟨hI4, Extends.of_eq hn4 hm4, ht4, ?_, fun h => h.elim⟩
      constructor
      · intro h; exact h.elim
      · intro h; exact absurd (h k0 (by simp)) hbad
    by_cases hatom : k0.isAtom = true
    · rw [hatom] at hb
      simp only [hb, uncurry, ↓reduceIte]
      step with con_spec hnm hz s2 ne hne k hI2 (by rw [hn2]; exact rk) (by unfold Room; omega)
        as ⟨r3, hI3, hn3', htb3, ht3, hm3, hpost⟩
      obtain ⟨c1, s3⟩ := r3
      simp only at hI3 hn3' htb3 ht3 hm3 hpost
      have hn3 : s3.nodes.val = s.nodes.val := by rw [hn3', hn2]
      rcases c1 with h | ⟨p, q⟩ | _
      · obtain ⟨n, p, rfl, rh⟩ := hpost
        rw [hn2] at rh
        simp only [dom.among]
        unfold namesPat at hU
        step with among_loop_spec hnm (U.map fun n => (.sym n : Pat)) s3 h names
          (tn := .sym n) hI3 (by rw [hn3]; exact rh) (by rw [hn3]; exact hU)
          (by simp only [List.length_map]; unfold Room; omega)
          as ⟨r4, hI4, hn4', htb4, ht4, hm4, hres⟩
        obtain ⟨b1, s4⟩ := r4
        simp only [List.length_map] at hI4 hn4' htb4 ht4 hm4 hres
        have hn4 : s4.nodes.val = s.nodes.val := by rw [hn4', hn3]
        by_cases hin : n ∈ U
        · have : b1 = true := by
            rw [hres]; exact decide_eq_true (List.mem_map.2 ⟨n, hin, rfl⟩)
          subst this
          simp only [uncurry, ↓reduceIte]
          step with alloc_spec s4 (.App k atoms) hI4
            ⟨by rw [hn4]; exact rk.lt, by rw [hn4]; exact hat.lt⟩ (by unfold Room; omega)
            as ⟨rs5, hI5, ht5, htb5, hx5, hr5⟩
          obtain ⟨atoms1, s5⟩ := rs5
          simp only at hI5 ht5 htb5 hx5 hr5
          simp only [norm] at hr5
          have hx05 : Extends s s5 := (Extends.of_eq hn4 (by omega)).trans hx5
          have hx45 : ∀ {i : Nat} {t : Pat}, Repr nm s.nodes.val i t →
              Repr nm s5.nodes.val i t := fun h => hx5.repr (by rw [hn4]; exact h)
          have rat : Repr nm s5.nodes.val atoms1.val
              (encList (nm none) (((n, p) :: As).map ppair)) :=
            .app hr5 (hx45 rk) (hx45 hat)
          simp only [uncurry, bind_ok]
          have IH := ih ((n, p) :: As) Xs s5 names nil atoms1 excl rest hI5 (hx45 hU)
            (hx45 hnil) rat (hx45 hex) (hx45 rrest) (by unfold Room; omega)
          unfold dom.parts_loop at IH
          refine WP.spec_mono IH ?_
          rintro ⟨s', at', ex', ok⟩ ⟨hI', hx', ht', hiff, hrep⟩
          simp only at hI' hx' ht' hiff hrep ⊢
          have hok : ConOK U (.app (.sym n) p) :=
            ⟨hatom, by simp [Sorts.atomOf, hin], by simp [Sorts.exclOf]⟩
          refine ⟨hI', hx05.trans hx', by omega, ?_, fun h => ?_⟩
          · rw [hiff]
            constructor
            · intro h c hc
              rcases List.mem_cons.1 hc with rfl | hc
              · exact hok
              · exact h c hc
            · intro h c hc; exact h c (List.mem_cons_of_mem _ hc)
          · have := hrep h
            simpa [List.flatMap_cons, Sorts.atomOf, Sorts.exclOf] using this
        · have : b1 = false := by
            rw [hres]
            refine decide_eq_false fun h => ?_
            obtain ⟨m, hm, e⟩ := List.mem_map.1 h
            cases e
            exact hin hm
          subst this
          simp only [Bool.false_eq_true, ↓reduceIte, uncurry, bind_ok]
          rw [loop]
          simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, WP.spec_ok]
          refine hexit s4 hI4 hn4 (by omega) (by omega) ?_
          rintro ⟨-, h, -⟩
          exact hin (h (n, p) (by simp [Sorts.atomOf]))
      · obtain ⟨tp, tq, rfl, rp, rq⟩ := hpost
        rw [hn2] at rp rq
        step with alloc_spec s3 (.App p q) hI3
          ⟨by rw [hn3]; exact rp.lt, by rw [hn3]; exact rq.lt⟩ (by unfold Room; omega)
          as ⟨rs4, hI4, ht4, htb4, hx4, hr4⟩
        obtain ⟨e, s4⟩ := rs4
        simp only at hI4 ht4 htb4 hx4 hr4
        simp only [norm] at hr4
        have hx34 : ∀ {i : Nat} {t : Pat}, Repr nm s.nodes.val i t →
            Repr nm s4.nodes.val i t := fun h => hx4.repr (by rw [hn3]; exact h)
        have re : Repr nm s4.nodes.val e.val (.app tp tq) := .app hr4 (hx34 rp) (hx34 rq)
        step with alloc_spec s4 (.App e nil) hI4 ⟨re.lt, (hx34 hnil).lt⟩
          (by unfold Room; omega) as ⟨rs5, hI5, ht5, htb5, hx5, hr5⟩
        obtain ⟨l, s5⟩ := rs5
        simp only at hI5 ht5 htb5 hx5 hr5
        simp only [norm] at hr5
        have rl : Repr nm s5.nodes.val l.val (encEqs nm [(tp, tq)]) :=
          .app hr5 (hx5.repr re) (hx5.repr (hx34 hnil))
        step with alloc_spec s5 (.App l excl) hI5 ⟨rl.lt, (hx5.repr (hx34 hex)).lt⟩
          (by unfold Room; omega) as ⟨rs6, hI6, ht6, htb6, hx6, hr6⟩
        obtain ⟨excl1, s6⟩ := rs6
        simp only at hI6 ht6 htb6 hx6 hr6
        simp only [norm] at hr6
        have hx06 : Extends s s6 :=
          (Extends.of_eq hn3 (by omega)).trans (hx4.trans (hx5.trans hx6))
        have hx36 : ∀ {i : Nat} {t : Pat}, Repr nm s.nodes.val i t →
            Repr nm s6.nodes.val i t := fun h => hx6.repr (hx5.repr (hx34 h))
        have rex : Repr nm s6.nodes.val excl1.val (encX nm ([(tp, tq)] :: Xs)) :=
          .app hr6 (hx6.repr rl) (hx36 hex)
        simp only [uncurry, bind_ok]
        have IH := ih As ([(tp, tq)] :: Xs) s6 names nil atoms excl1 rest hI6 (hx36 hU)
          (hx36 hnil) (hx36 hat) rex (hx36 rrest) (by unfold Room; omega)
        unfold dom.parts_loop at IH
        refine WP.spec_mono IH ?_
        rintro ⟨s', at', ex', ok⟩ ⟨hI', hx', ht', hiff, hrep⟩
        simp only at hI' hx' ht' hiff hrep ⊢
        have hok : ConOK U (.app (.app (.sym neSym) tp) tq) :=
          ⟨hatom, by simp [Sorts.atomOf], by simp [Sorts.exclOf]⟩
        refine ⟨hI', hx06.trans hx', by omega, ?_, fun h => ?_⟩
        · rw [hiff]
          constructor
          · intro h c hc
            rcases List.mem_cons.1 hc with rfl | hc
            · exact hok
            · exact h c hc
          · intro h c hc; exact h c (List.mem_cons_of_mem _ hc)
        · have := hrep h
          simpa [List.flatMap_cons, Sorts.atomOf, Sorts.exclOf] using this
      · obtain ⟨-, hx0⟩ := hpost
        simp only [uncurry, bind_ok]
        rw [loop]
        simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, WP.spec_ok]
        refine hexit s3 hI3 hn3 (by omega) (by omega) ?_
        rintro ⟨-, -, h⟩
        exact h (by rw [hx0]; simp)
    · have hbf : b = false := by rw [hb]; simpa using hatom
      subst hbf
      simp only [Bool.false_eq_true, ↓reduceIte, uncurry, bind_ok]
      rw [loop]
      simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, WP.spec_ok]
      exact hexit s2 hI2 hn2 (by omega) (by omega) (fun h => hatom h.1)

/-- `parts` gives the sorted patterns and the exclusions of a list of
constraints, or nothing when one of them cannot be stated. -/
theorem parts_spec (hnm : Function.Injective nm) (hz : nm none = "") (U : List Name)
    (ne : U32) (hne : nm (some ne.val) = neSym) (Cs : List Pat) (s : store.Store)
    (names c : store.TermId) (hI : Inv s)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (hc : Repr nm s.nodes.val c.val (encList (nm none) Cs))
    (hroom : Room s (1 + partsCost U.length Cs)) :
    dom.parts s names ne c ⦃ o s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + 1 + partsCost U.length Cs ∧
        match o with
        | none => ¬ ∀ c ∈ Cs, ConOK U c
        | some (a, e) => (∀ c ∈ Cs, ConOK U c) ∧
            Repr nm s'.nodes.val a.val
              (encList (nm none) ((Cs.flatMap Sorts.atomOf).reverse.map ppair)) ∧
            Repr nm s'.nodes.val e.val (encX nm (Cs.flatMap Sorts.exclOf).reverse) ⦄ := by
  unfold dom.parts
  have hroom' := hroom
  unfold Room at hroom'
  step with alloc_spec s .Nil hI trivial (by unfold Room; omega)
    as ⟨nil, s1, hI1, ht1, htb1, hx1, hr1⟩
  simp only [norm] at hr1
  have rnil : Repr nm s1.nodes.val nil.val (.sym (nm none)) := .nil hr1
  step with parts_loop_spec hnm hz U ne hne Cs [] [] s1 names nil nil nil c hI1 (hx1.repr hU)
    rnil rnil rnil (hx1.repr hc) (by unfold Room; omega) as ⟨s2, atoms, excl, ok, hI2, hx2, ht2, hiff, hrep⟩
  split
  · rename_i hok
    simp only [WP.spec_ok]
    exact ⟨hI2, hx1.trans hx2, by omega, hiff.1 hok, by
      have := hrep hok
      rwa [List.append_nil, List.append_nil] at this⟩
  · rename_i hok
    simp only [WP.spec_ok]
    exact ⟨hI2, hx1.trans hx2, by omega, fun h => hok (hiff.2 h)⟩

/-! ## The representative -/

theorem repOf_not_fo {S : Sorts} {sp : Span} (h : ¬ sp.firstOrder = true) :
    Sorts.repOf S sp = none := by
  by_cases hS : S.WellFormed
  · simp only [Sorts.repOf, hS, h, ↓reduceDIte, Bool.false_eq_true]
  · simp only [Sorts.repOf, hS, ↓reduceDIte]

theorem repOf_fo {S : Sorts} (hS : S.WellFormed) {sp : Span} (hfo : sp.firstOrder = true) :
    Sorts.repOf S sp =
      Sorts.Rep.of hS (Sorts.spanProb sp) (Sorts.spanProb_fo hfo) ⟨sp.l, sp.r, rfl⟩ := by
  simp only [Sorts.repOf, hS, hfo, ↓reduceDIte]

/-- A span with a constraint the store cannot state has no
representative. -/
theorem repOf_bad {S : Sorts} {U : List Name} (hU : ∀ n ∈ Sorts.names S, n ∈ U) {sp : Span}
    (h : ¬ ∀ c ∈ sp.c, ConOK U c) : Sorts.repOf S sp = none := by
  by_cases hS : S.WellFormed
  · by_cases hfo : sp.firstOrder = true
    · rw [repOf_fo hS hfo, Sorts.Rep.of_eq_none]
      refine Sorts.Prob.norm_of_empty hS (Sorts.spanProb_fo hfo) ?_
      by_contra hne
      apply h
      intro c hc
      have hat : c.isAtom = true := by
        simp only [Span.firstOrder, Bool.and_eq_true, List.all_eq_true] at hfo
        exact hfo.2 c hc
      refine ⟨hat, fun a ha => ?_, fun hx => ?_⟩
      · by_contra hn
        exact hne (spanProb_dead hc (.inl ⟨a, ha, fun hm => hn (hU _ hm)⟩))
      · exact hne (spanProb_dead hc (.inr hx))
    · exact repOf_not_fo hfo
  · simp only [Sorts.repOf, hS, ↓reduceDIte]

/-- The ticks `rep` may take before the normal store of its problem: the
two first-order checks, and for each constraint its check, its reading, the
search for its sort among the `u` names and its place in the lists. -/
def spanCost (u : Nat) (sp : Span) : Nat :=
  (5 + 9 * sp.l.subs.card) + (5 + 9 * sp.r.subs.card) + (1 + partsCost u sp.c) + 4

/-- `rep` computes the representative of a span as written
(`Sorts.repOf`). -/
theorem rep_spec (hnm : Function.Injective nm) (hz : nm none = "") {S : Sorts} {dp : Pat}
    {U : List Name} (hC : Ctx nm S dp U) (hS : S.WellFormed)
    (hUS : ∀ n ∈ U, n ∈ Sorts.names S) {rc q : Nat}
    (hr : ∀ d, (Sorts.reachSet S d).card ≤ rc)
    (hq : ∀ d m, (Sorts.reachGSet S (d, some m)).card ≤ q) (sp : Span) (ne : U32)
    (hne : nm (some ne.val) = neSym) (B : Nat)
    (hB : NormBound nm S U rc q (spanProbR sp) B)
    (s : store.Store) (decls names : store.TermId) (x : span.Span)
    (hI : Inv s) (hde : Repr nm s.nodes.val decls.val dp)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (hx : SpanAt nm s.nodes.val x sp)
    (hroom : Room s (spanCost U.length sp + startCost nm S U.length (spanProbR sp) + B)) :
    dom.rep s decls names ne x ⦃ res s' =>
      Inv s' ∧ Extends s s' ∧
        s'.ticks.val ≤ s.ticks.val + spanCost U.length sp +
          startCost nm S U.length (spanProbR sp) + B ∧
        RepPost nm U s'.nodes.val (Sorts.repOf S sp) res ⦄ := by
  unfold dom.rep
  have hroom' := hroom
  unfold Room at hroom'
  simp only [spanCost] at hroom'
  step with first_order_spec hnm s x.l sp.l.subs hI hx.l (Finset.Subset.refl _)
    (by unfold Room; omega) as ⟨b, s1, h1⟩
  have c1 := h1.cost
  have m1 := h1.mono
  have hx1 : Extends s s1 := Extends.of_eq h1.nodes m1
  split
  · rename_i hb
    have hl : sp.l.firstOrder = true := by rw [← h1.res]; exact hb
    step with first_order_spec hnm s1 x.r sp.r.subs h1.inv (by rw [h1.nodes]; exact hx.r)
      (Finset.Subset.refl _) (by unfold Room; omega) as ⟨b', s2, h2⟩
    have c2 := h2.cost
    have m2 := h2.mono
    have hn2 : s2.nodes.val = s.nodes.val := by rw [h2.nodes, h1.nodes]
    have hx2 : Extends s s2 := Extends.of_eq hn2 (by omega)
    split
    · rename_i hb'
      have hr' : sp.r.firstOrder = true := by rw [← h2.res]; exact hb'
      step with parts_spec hnm hz U ne hne sp.c s2 names x.c h2.inv (by rw [hn2]; exact hU)
        (by rw [hn2]; exact hx.c) (by unfold Room; omega) as ⟨o, s3, hI3, hx3, ht3, hpost⟩
      cases o with
      | none =>
        simp only at hpost
        simp only [WP.spec_ok]
        exact ⟨hI3, hx2.trans hx3, by simp only [spanCost]; omega, repOf_bad hC.names hpost⟩
      | some p =>
        obtain ⟨a, e⟩ := p
        simp only at hpost
        obtain ⟨hok, ra, re⟩ := hpost
        have hfo : sp.firstOrder = true := by
          simp only [Span.firstOrder, Bool.and_eq_true, List.all_eq_true]
          exact ⟨⟨hl, hr'⟩, fun c hc => (hok c hc).1⟩
        have hx03 := hx2.trans hx3
        simp only
        step with pair_spec hz s3 x.l x.r hI3 (hx03.repr hx.l) (hx03.repr hx.r)
          (by unfold Room; omega) as ⟨t, s4, hI4, hx4, ht4, rt⟩
        step with alloc_spec s4 .Nil hI4 trivial (by unfold Room; omega)
          as ⟨nil, s5, hI5, ht5, htb5, hx5, hr5⟩
        simp only [norm] at hr5
        have hx05 := hx03.trans (hx4.trans hx5)
        have hPa : ∀ a ∈ (spanProbR sp).a, a.1 ∈ Sorts.names S := by
          intro a ha
          obtain ⟨c, hc, hac⟩ := List.mem_flatMap.1 (List.mem_reverse.1 ha)
          exact hUS _ ((hok c hc).2.1 a hac)
        refine WP.spec_mono (normal_spec hnm hz hC hS hUS hr hq (spanProbR sp) (spanProbR_fo hfo)
          hPa B hB s5 decls names t nil a e hI5 (hx05.repr hde) (hx05.repr hU) (hx5.repr rt)
          (.nil hr5) ((hx4.trans hx5).repr ra) ((hx4.trans hx5).repr re)
          (by unfold Room; omega)) ?_
        rintro ⟨res, s'⟩ ⟨hI', hx', ht', hpost'⟩
        refine ⟨hI', hx05.trans hx', by simp only [spanCost]; omega, ?_⟩
        rw [repOf_fo hS hfo]
        exact repPost_of hS (Sorts.spanProb_fo hfo) ⟨sp.l, sp.r, rfl⟩
          (Sorts.Prob.norm_congr hS (spanProbR_fo hfo) (Sorts.spanProb_fo hfo) (spanProbR_den sp))
          hpost'
    · rename_i hb'
      simp only [WP.spec_ok]
      refine ⟨h2.inv, hx2, by simp only [spanCost]; omega, repOf_not_fo fun h => ?_⟩
      simp only [Span.firstOrder, Bool.and_eq_true] at h
      exact hb' (by rw [h2.res]; exact h.1.2)
  · rename_i hb
    simp only [WP.spec_ok]
    refine ⟨h1.inv, hx1, by simp only [spanCost]; omega, repOf_not_fo fun h => ?_⟩
    simp only [Span.firstOrder, Bool.and_eq_true] at h
    exact hb (by rw [h1.res]; exact h.1.1)

end RwLogVerified
