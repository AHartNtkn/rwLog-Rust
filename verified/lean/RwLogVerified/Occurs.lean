/-
# The occurs check: the Rust `occurs` decides membership in `Term.vars`

`occurs s x p` says whether the variable at `x` occurs in the term at `p`.
It walks the term with the stack of the store. Table `B`, empty at the
start, flags the nodes already visited, so a node is examined once however
often it occurs. The walk stops at the first node that is the variable.

`occurs_spec`: the answer is `xv ∈ t.vars`, no node is added, table `A` is
untouched, and the cost is four ticks plus eight for each distinct subterm.
An application costs the eight: it is taken off the stack and looked up
(two), flagged and read (two), and its two parts are put on the stack (two)
and each taken off and looked up again when already flagged (two).
-/
import RwLogVerified.Rebuild

open Aeneas Aeneas.Std Result

namespace RwLogVerified

open rwlog_core RwLog

variable {nm : Option Nat → Sym}

theorem var_mem_subs_iff {v : Nat} {t : Pat} : Term.var v ∈ t.subs ↔ v ∈ t.vars := by
  induction t with
  | var w => simp [Term.subs, Term.vars]
  | sym f => simp [Term.subs, Term.vars]
  | app a b iha ihb => simp [Term.subs, Term.vars, iha, ihb]

/-- Giving a node its entry takes its term out of the terms without one. -/
theorem pending_set_card (hnm : Function.Injective nm) {nodes : List store.Node}
    (hN : NodesOK nodes) {A : Nat → Option Nat} {S : Finset Pat} {t : Pat} {q : Nat}
    (hq : Repr nm nodes q t) (hnone : A q = none) (ht : t ∈ S) (r : Nat) :
    (pending nm nodes (Function.update A q (some r)) S).card + 1 ≤ (pending nm nodes A S).card := by
  have hsub := pending_after_set (nm := nm) (nodes := nodes) (more := []) (A := A)
    (A' := Function.update A q (some r)) (S := S) (t := t) (p := q) (by simpa using hq)
    (by simp)
    (by
      intro k hk
      by_cases e : k = q
      · subst e; simp
      · rw [Function.update_of_ne e]; exact hk)
  simp only [List.append_nil] at hsub
  have h1 := Finset.card_le_card hsub
  have h2 := pending_erase_card (mem_pending_of_none hnm hN hq hnone ht)
  omega

/-- What `occurs` leaves. -/
structure OccursPost (s s' : store.Store) (xv : Nat) (t : Pat) (S : Finset Pat) (b : Bool) :
    Prop where
  inv : Inv s'
  nodes : s'.nodes.val = s.nodes.val
  res : b = decide (xv ∈ t.vars)
  tblA : tbl s' .A = tbl s .A
  cost : s'.ticks.val ≤ s.ticks.val + 4 + 8 * S.card
  mono : s.ticks.val ≤ s'.ticks.val

/-- The flagged nodes: no flagged variable is the one looked for, and the
parts of a flagged application are flagged or on the stack. -/
structure Seen (n0 : List store.Node) (Bt : Nat → Option Nat) (xv : Nat) (st : List store.Frame) :
    Prop where
  var : ∀ k v, Bt k ≠ none → VarAt n0 k v → v ≠ xv
  app : ∀ k (a b : store.TermId), Bt k ≠ none → n0[k]? = some (.App a b) →
    (Bt a.val ≠ none ∨ ∃ f ∈ st, fkey f = a.val) ∧ (Bt b.val ≠ none ∨ ∃ f ∈ st, fkey f = b.val)

/-- When the stack is empty, the variable is in no flagged term. -/
theorem Seen.not_mem {n0 : List store.Node} {Bt : Nat → Option Nat} {xv : Nat}
    (h : Seen n0 Bt xv []) : ∀ (t : Pat) (k : Nat), Repr nm n0 k t → Bt k ≠ none → xv ∉ t.vars := by
  intro t
  induction t with
  | var v =>
    intro k hk hB
    cases hk with
    | var hv =>
      have := h.var k v hB hv
      simp only [Term.vars, List.mem_singleton]
      exact fun e => this e.symm
  | sym f => intro k _ _; simp [Term.vars]
  | app ta tb iha ihb =>
    intro k hk hB
    cases hk with
    | app hn ha hb =>
      obtain ⟨h1, h2⟩ := h.app k _ _ hB hn
      simp only [Term.vars, List.mem_append, not_or]
      refine ⟨iha _ ha ?_, ihb _ hb ?_⟩
      · rcases h1 with h1 | ⟨f, hf, -⟩
        · exact h1
        · simp at hf
      · rcases h2 with h2 | ⟨f, hf, -⟩
        · exact h2
        · simp at hf

/-- The invariant of the loop: the walk goes on, or the variable was found. -/
def OInv (nm : Option Nat → Sym) (s0 : store.Store) (xv : Nat) (tp : Pat) (p : Nat)
    (S : Finset Pat) (B : Nat) : store.Store × Bool → Prop
  | (s, found) => Wf s ∧ s.nodes.val = s0.nodes.val ∧ tbl s .A = tbl s0 .A ∧
    if found then stk s = [] ∧ xv ∈ tp.vars ∧ s.ticks.val + 1 ≤ B
    else (∀ f ∈ stk s, ∃ u ∈ tp.subs, Repr nm s0.nodes.val (fkey f) u) ∧
      Seen s0.nodes.val (tbl s .B) xv (stk s) ∧
      (tbl s .B p ≠ none ∨ ∃ f ∈ stk s, fkey f = p) ∧
      s.ticks.val + 1 + 2 * (stk s).length +
        8 * (pending nm s.nodes.val (tbl s .B) S).card ≤ B

def OBodyPost (nm : Option Nat → Sym) (s0 : store.Store) (xv : Nat) (tp : Pat) (p : Nat)
    (S : Finset Pat) (B : Nat) (t0 : Nat) :
    ControlFlow (store.Store × Bool) (Bool × store.Store) → Prop
  | .done (b, s') => Wf s' ∧ stk s' = [] ∧ s'.nodes.val = s0.nodes.val ∧
      tbl s' .A = tbl s0 .A ∧ b = decide (xv ∈ tp.vars) ∧ s'.ticks.val ≤ B ∧ t0 ≤ s'.ticks.val
  | .cont x => OInv nm s0 xv tp p S B x ∧ t0 < x.1.ticks.val

theorem occurs_body_spec (hnm : Function.Injective nm) (s0 : store.Store) (x : store.TermId)
    (xv : Nat) (tp : Pat) (p : Nat) (S : Finset Pat) (B : Nat)
    (hB : 40 * B + 100 ≤ Usize.max) (hx : VarAt s0.nodes.val x.val xv)
    (hp : Repr nm s0.nodes.val p tp) (hS : tp.subs ⊆ S) (s : store.Store) (found : Bool)
    (h : OInv nm s0 xv tp p S B (s, found)) :
    term.occurs_loop.body x s found ⦃ r => OBodyPost nm s0 xv tp p S B s.ticks.val r ⦄ := by
  unfold term.occurs_loop.body
  obtain ⟨hW, hn, hTA, h⟩ := h
  cases found with
  | true =>
    simp only [↓reduceIte] at h
    obtain ⟨hemp, hmem, hc⟩ := h
    step with pop_w s hW (by unfold Room; omega) as ⟨o, s1, e1, e2, e3, hW1, eo, est⟩
    rw [hemp] at eo est
    simp only [List.head?_nil, List.tail_nil] at eo est
    subst eo
    simp only [WP.spec_ok]
    exact ⟨hW1, est, by rw [e1, hn], by rw [e2, hTA], by simp [hmem], by omega, by omega⟩
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
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
      have := hSeen.not_mem tp p hp hBp
      simp [this]
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
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [hstk2, htb2, hn2]
        refine ⟨hFr', ⟨hSeen.var, fun k a b hk hnk => ?_⟩, ?_, by omega⟩
        · obtain ⟨h1, h2⟩ := hSeen.app k a b hk hnk
          refine ⟨?_, ?_⟩
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
        -- entries only grow
        have hgrow : ∀ k, tbl s .B k ≠ none →
            Function.update (tbl s .B) (fkey fr) (some 1) k ≠ none := by
          intro k hk
          by_cases e : k = fkey fr
          · rw [e]; simp
          · rw [Function.update_of_ne e]; exact hk
        have hself : Function.update (tbl s .B) (fkey fr) (some 1) (fkey fr) ≠ none := by simp
        -- what is flagged after the node is, for a stack `st'` that holds `st`
        -- and the parts of the node
        have hseen : ∀ st' : List store.Frame, (∀ f ∈ st, f ∈ st') →
            (∀ v, VarAt s0.nodes.val (fkey fr) v → v ≠ xv) →
            (∀ a b : store.TermId, nd = .App a b →
              (∃ f ∈ st', fkey f = a.val) ∧ ∃ f ∈ st', fkey f = b.val) →
            Seen s0.nodes.val (Function.update (tbl s .B) (fkey fr) (some 1)) xv st' := by
          intro st' hsub hvar happ
          refine ⟨fun k v hk hv => ?_, fun k a b hk hnk => ?_⟩
          · by_cases e : k = fkey fr
            · subst e; exact hvar v hv
            · rw [Function.update_of_ne e] at hk
              exact hSeen.var k v hk hv
          · by_cases e : k = fkey fr
            · subst e
              rw [hnd0] at hnk
              cases hnk
              obtain ⟨h1, h2⟩ := happ a b rfl
              exact ⟨Or.inr h1, Or.inr h2⟩
            · rw [Function.update_of_ne e] at hk
              obtain ⟨h1, h2⟩ := hSeen.app k a b hk hnk
              refine ⟨?_, ?_⟩
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
        -- a node that is not an application and not the variable
        have hplain : ∀ s5 : store.Store, Wf s5 → s5.nodes.val = s.nodes.val →
            tbl s5 = tbl s4 → stk s5 = st → s5.ticks.val ≤ s4.ticks.val + 1 →
            s4.ticks.val ≤ s5.ticks.val →
            (∀ v, VarAt s0.nodes.val (fkey fr) v → v ≠ xv) → (∀ a b, nd ≠ .App a b) →
            OBodyPost nm s0 xv tp p S B s.ticks.val (.cont (s5, false)) := by
          intro s5 hW5 hn5 htb5 hstk5 ht5 hm5 hvar hna
          refine ⟨⟨hW5, by rw [hn5, hn], by rw [htb5, hA4, hTA], ?_⟩, by simp only; omega⟩
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [hstk5, htb5, htb4B, hn5]
          exact ⟨hFr', hseen st (fun _ h => h) hvar (fun a b e => absurd e (hna a b)),
            hroot st (fun _ h => h), by omega⟩
        -- a variable: compared with the one looked for
        have hvarcase : ∀ v, tq = Term.var v → VarAt s0.nodes.val (fkey fr) v →
            (∀ a b, nd ≠ .App a b) →
            (do
              let (b, s5) ← store.Store.same s4 (fid fr) x
              if b then do
                let s6 ← store.Store.drop_stack s5
                ok (ControlFlow.cont (s6, true) :
                  ControlFlow (store.Store × Bool) (Bool × store.Store))
              else ok (ControlFlow.cont (s5, false))) ⦃ r =>
              OBodyPost nm s0 xv tp p S B s.ticks.val r ⦄ := by
          intro v hv hva hna
          subst hv
          step with same_w s4 (fid fr) x hK4.wf (by unfold Room; omega) as ⟨b, s5, hb, hK5⟩
          have ht5 := hK5.ticks
          rw [fid_val] at hb
          split
          · rename_i hbt
            have hqx : fkey fr = x.val := by simpa [hb] using hbt
            have hvx : v = xv := by rw [hqx] at hva; exact hva.unique hx
            subst hvx
            step with drop_stack_w s5 hK5.wf (by unfold Room; omega) as ⟨s6, d1, d2, d3, hW6, d5⟩
            refine ⟨⟨hW6, by rw [d1, hK5.nodes, hn4, hn], by rw [d2, hK5.tbl, hA4, hTA], ?_⟩,
              by simp only; omega⟩
            simp only [↓reduceIte]
            exact ⟨d5, var_mem_subs_iff.1 htq, by omega⟩
          · rename_i hbf
            have hqx : fkey fr ≠ x.val := by simpa [hb] using hbf
            simp only [WP.spec_ok]
            refine hplain s5 hK5.wf (by rw [hK5.nodes, hn4]) hK5.tbl (by rw [hK5.stk, hstk4])
              (by omega) (by omega) ?_ hna
            intro v' hv' e
            subst e
            have hN0 : NodesOK s0.nodes.val := by rw [← hn]; exact hN
            exact hqx (hv'.inj hN0 hx)
        cases nd with
        | V0 =>
          obtain ⟨v, hv, hva⟩ := hq0.of_var hnd0 trivial
          exact hvarcase v hv hva (fun a b e => by cases e)
        | VL a =>
          obtain ⟨v, hv, hva⟩ := hq0.of_var hnd0 trivial
          exact hvarcase v hv hva (fun a b e => by cases e)
        | VR a =>
          obtain ⟨v, hv, hva⟩ := hq0.of_var hnd0 trivial
          exact hvarcase v hv hva (fun a b e => by cases e)
        | Sym g =>
          simp only [WP.spec_ok]
          refine hplain s4 hK4.wf hn4 rfl hstk4 (by omega) (by omega) ?_ (fun a b e => by cases e)
          intro v hv
          obtain ⟨m, hm, hvn⟩ := hv.node
          rw [hnd0] at hm; cases hm; exact hvn.elim
        | Nil =>
          simp only [WP.spec_ok]
          refine hplain s4 hK4.wf hn4 rfl hstk4 (by omega) (by omega) ?_ (fun a b e => by cases e)
          intro v hv
          obtain ⟨m, hm, hvn⟩ := hv.node
          rw [hnd0] at hm; cases hm; exact hvn.elim
        | App a b =>
          obtain ⟨ta, tb, e, ha, hb⟩ := hq0.of_app hnd0
          subst e
          simp only
          step with push_w s4 (.Visit b b) hK4.wf (by unfold Room; omega)
            as ⟨s5, b1, b2, b3, hW5, b5⟩
          step with push_w s5 (.Visit a a) hW5 (by unfold Room; omega)
            as ⟨s6, c1, c2, c3, hW6, c5⟩
          have hn6 : s6.nodes.val = s.nodes.val := by rw [c1, b1, hn4]
          have hstk6 : stk s6 = .Visit a a :: .Visit b b :: st := by rw [c5, b5, hstk4]
          refine ⟨⟨hW6, by rw [hn6, hn], by rw [c2, b2, hA4, hTA], ?_⟩, by simp only; omega⟩
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [hstk6, c2, b2, htb4B, hn6]
          have hsub : ∀ f ∈ st, f ∈ store.Frame.Visit a a :: store.Frame.Visit b b :: st :=
            fun f hf => by simp [hf]
          refine ⟨?_, hseen _ hsub ?_ ?_, hroot _ hsub, ?_⟩
          · intro f hf
            simp only [List.mem_cons] at hf
            rcases hf with rfl | rfl | hf
            · exact ⟨ta, Term.subs_trans htq (by simp [Term.subs, Term.self_mem_subs]), ha⟩
            · exact ⟨tb, Term.subs_trans htq (by simp [Term.subs, Term.self_mem_subs]), hb⟩
            · exact hFr' f hf
          · intro v hv
            obtain ⟨m, hm, hvn⟩ := hv.node
            rw [hnd0] at hm; cases hm; exact hvn.elim
          · intro a' b' e
            cases e
            exact ⟨⟨.Visit a a, by simp, rfl⟩, ⟨.Visit b b, by simp, rfl⟩⟩
          · simp only [List.length_cons]
            omega

/-- `occurs` decides whether a variable occurs in a term. Table `B` is
empty at the start. It spends four ticks, and eight for each term of `S`. -/
theorem occurs_spec (hnm : Function.Injective nm) (s : store.Store) (x p : store.TermId)
    {t : Pat} {xv : Nat} (S : Finset Pat) (hI : Inv s) (hp : Repr nm s.nodes.val p.val t)
    (hx : VarAt s.nodes.val x.val xv) (hBe : ∀ k, tbl s .B k = none)
    (hS : t.subs ⊆ S) (hroom : Room s (4 + 8 * S.card)) :
    term.occurs s x p ⦃ b s' => OccursPost s s' xv t S b ⦄ := by
  unfold term.occurs term.occurs_loop
  have hroom' := hroom
  unfold Room at hroom'
  step with push_w s (.Visit p p) hI.toWf (by unfold Room; omega) as ⟨s1, a1, a2, a3, hW1, a5⟩
  rw [hI.empty] at a5
  have hP := pending_card_le (nm := nm) s.nodes.val (tbl s .B) S
  let B := s.ticks.val + 4 + 8 * S.card
  have hloop := loop.spec_decr_nat
    (fun y : store.Store × Bool => B + 1 - y.1.ticks.val)
    (fun y => OInv nm s xv t p.val S B y ∧ s.ticks.val ≤ y.1.ticks.val)
    (fun y : Bool × store.Store => OccursPost s y.2 xv t S y.1)
    (fun y : store.Store × Bool => term.occurs_loop.body x y.1 y.2) (s1, false)
    (by
      rintro ⟨y, found⟩ ⟨hinv, hy⟩
      refine WP.spec_mono (occurs_body_spec hnm s x xv t p.val S B (by omega) hx hp hS y found
        hinv) ?_
      intro r hr
      cases r with
      | done z =>
        obtain ⟨b, z⟩ := z
        obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hr
        refine ⟨⟨h1, h2⟩, h3, h5, h4, by omega, ?_⟩
        exact Nat.le_trans hy h7
      | cont y' =>
        obtain ⟨h1, h2⟩ := hr
        obtain ⟨z, found'⟩ := y'
        have hz : z.ticks.val + 1 ≤ B := by
          obtain ⟨-, -, -, h⟩ := h1
          cases found' with
          | true => simp only [↓reduceIte] at h; exact h.2.2
          | false => simp only [Bool.false_eq_true, ↓reduceIte] at h; omega
        simp only at hy h2
        exact ⟨⟨h1, by simp only; omega⟩, by simp only; omega⟩)
    ⟨⟨hW1, a1, by rw [a2], by
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [a5, a2, a1]
      refine ⟨?_, ⟨fun k v hk => absurd (hBe k) hk, fun k a b hk => absurd (hBe k) hk⟩,
        Or.inr ⟨_, List.mem_singleton_self _, rfl⟩, ?_⟩
      · intro f hf
        simp only [List.mem_singleton] at hf
        subst hf
        exact ⟨t, Term.self_mem_subs t, hp⟩
      · simp only [List.length_singleton]
        omega⟩, by simp only; omega⟩
  exact hloop

end RwLogVerified
