/-
# Solving equations: the Rust `solve_into` computes `solve`

`act_spec`: `act` decides what to do with one equation, and what it decides
agrees with one step of the specification's `solve`.

`solve_into_spec`: the loop returns the output term with the solution of the
equations applied, or reports that there is none, exactly as `solveOn` says.
It spends at most `solveCost` ticks.
-/
import RwLogVerified.Occurs
import RwLogVerified.SolveCost

open Aeneas Aeneas.Std Result

namespace RwLogVerified

open rwlog_core RwLog RwLog.Term
open RwLog.Eqns (solveOn solveOn_elim_left solveOn_elim_right solveOn_occurs_left
  solveOn_occurs_right solveOn_clash solveOn_sym_app solveOn_app_sym solveOn_refl solveOn_split
  solveOn_nil)

variable {nm : Option Nat → Sym}

/-! ## What a node is -/

def KindOK (nm : Option Nat → Sym) (nodes : List store.Node) (t : Pat) (p : Nat) :
    span.Kind → Prop
  | .Var => ∃ v, t = .var v ∧ VarAt nodes p v
  | .Atom => ∃ f, t = .sym f
  | .App a b => ∃ ta tb, t = .app ta tb ∧ Repr nm nodes a.val ta ∧ Repr nm nodes b.val tb

theorem kind_spec (s : store.Store) (p : store.TermId) {t : Pat} (hI : Inv s)
    (hp : Repr nm s.nodes.val p.val t) (hroom : Room s 1) :
    span.kind s p ⦃ k s' => KindOK nm s.nodes.val t p.val k ∧ Kept s s' 1 ⦄ := by
  unfold span.kind
  step with read_spec s p hI hp.lt hroom as ⟨nd, s1, hnd, hK⟩
  cases nd with
  | V0 =>
    obtain ⟨v, hv, hva⟩ := hp.of_var hnd trivial
    step*
    exact ⟨⟨v, hv, hva⟩, hK⟩
  | VL a =>
    obtain ⟨v, hv, hva⟩ := hp.of_var hnd trivial
    step*
    exact ⟨⟨v, hv, hva⟩, hK⟩
  | VR a =>
    obtain ⟨v, hv, hva⟩ := hp.of_var hnd trivial
    step*
    exact ⟨⟨v, hv, hva⟩, hK⟩
  | Sym g =>
    step*
    exact ⟨⟨_, hp.of_sym hnd⟩, hK⟩
  | Nil =>
    step*
    exact ⟨⟨_, hp.of_nil hnd⟩, hK⟩
  | App a b =>
    obtain ⟨ta, tb, e, ha, hb⟩ := hp.of_app hnd
    step*
    exact ⟨⟨ta, tb, e, ha, hb⟩, hK⟩

/-! ## One equation -/

/-- What `act` decided is right for the equation between `t` and `u`. -/
def ActOK (nm : Option Nat → Sym) (nodes : List store.Node) (t u : Pat) : span.Act → Prop
  | .Skip => t = u
  | .Fail => ∀ (E : Eqns Nat) (o : Pat), solveOn ((t, u) :: E) o = none
  | .Split a c b d => ∃ ta tb tc td, t = .app ta tb ∧ u = .app tc td ∧ t ≠ u ∧
      Repr nm nodes a.val ta ∧ Repr nm nodes c.val tc ∧ Repr nm nodes b.val tb ∧
      Repr nm nodes d.val td
  | .Elim x w => ∃ xv tu, VarAt nodes x.val xv ∧ Repr nm nodes w.val tu ∧ xv ∉ tu.vars ∧
      ((t = .var xv ∧ u = tu) ∨ (u = .var xv ∧ t = tu)) ∧
      ∀ (E : Eqns Nat) (o : Pat),
        solveOn ((t, u) :: E) o = solveOn (Eqns.subst xv tu E) (o.bind (single xv tu))

/-- The ticks `act` may spend. -/
def actCost (t u : Pat) : span.Act → Nat
  | .Skip => 1
  | .Split _ _ _ _ => 3
  | _ => 8 + 8 * (t.subs ∪ u.subs).card

theorem actOK_elim_left {nodes : List store.Node} {p q : store.TermId} {v : Nat} {u : Pat}
    (hv : VarAt nodes p.val v) (hq : Repr nm nodes q.val u) (hne : u ≠ .var v)
    (hx : v ∉ u.vars) : ActOK nm nodes (.var v) u (.Elim p q) :=
  ⟨v, u, hv, hq, hx, Or.inl ⟨rfl, rfl⟩, fun E o => solveOn_elim_left hne hx E o⟩

theorem actOK_elim_right {nodes : List store.Node} {p q : store.TermId} {w : Nat} {t : Pat}
    (hw : VarAt nodes q.val w) (hp : Repr nm nodes p.val t) (hu : ∀ y, t ≠ .var y)
    (hx : w ∉ t.vars) : ActOK nm nodes t (.var w) (.Elim q p) :=
  ⟨w, t, hw, hp, hx, Or.inr ⟨rfl, rfl⟩, fun E o => solveOn_elim_right hu hx E o⟩

theorem act_spec (hnm : Function.Injective nm) (s : store.Store) (p q : store.TermId) {t u : Pat}
    (hI : Inv s) (hp : Repr nm s.nodes.val p.val t) (hq : Repr nm s.nodes.val q.val u)
    (hroom : Room s (8 + 8 * (t.subs ∪ u.subs).card)) :
    span.act s p q ⦃ a s' =>
      Inv s' ∧ s'.nodes.val = s.nodes.val ∧ tbl s' .A = tbl s .A ∧ ActOK nm s.nodes.val t u a ∧
        s'.ticks.val ≤ s.ticks.val + actCost t u a ∧ s.ticks.val ≤ s'.ticks.val ⦄ := by
  unfold span.act
  have hroom' := hroom
  unfold Room at hroom'
  step with same_spec s p q hI (by unfold Room; omega) as ⟨b, s1, hb, hK1⟩
  have ht1 := hK1.ticks
  have hn1 := hK1.nodes
  by_cases hpq : p.val = q.val
  · have hbt : b = true := by simp [hb, hpq]
    subst hbt
    simp only [↓reduceIte]
    step*
    refine ⟨hK1.inv, hn1, by rw [hK1.tbl], ?_, by simp only [actCost]; omega, by omega⟩
    rw [hpq] at hp
    simp only [ActOK]
    exact hp.unique hq
  · have hbf : b = false := by simp [hb, hpq]
    subst hbf
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hne : t ≠ u := fun e => hpq (Repr.inj hnm hI.nodesOK hp (e ▸ hq))
    step with kind_spec (nm := nm) s1 p (t := t) hK1.inv (by rw [hn1]; exact hp)
      (by unfold Room; omega) as ⟨k, s2, hk, hK2⟩
    rw [hn1] at hk
    have ht2 := hK2.ticks
    have hn2 : s2.nodes.val = s.nodes.val := by rw [hK2.nodes, hn1]
    have htb2 : tbl s2 = tbl s := by rw [hK2.tbl, hK1.tbl]
    have hcu : (u.subs).card ≤ (t.subs ∪ u.subs).card :=
      Finset.card_le_card Finset.subset_union_right
    have hct : (t.subs).card ≤ (t.subs ∪ u.subs).card :=
      Finset.card_le_card Finset.subset_union_left
    -- the occurs check, for a variable at `x` and an application at `w`
    have hocc : ∀ (s3 : store.Store), Kept s2 s3 1 → ∀ (x w : store.TermId) (xv : Nat) (tw : Pat), VarAt s.nodes.val x.val xv →
        Repr nm s.nodes.val w.val tw → tw.subs.card ≤ (t.subs ∪ u.subs).card →
        ∀ (P : span.Act → Prop), (xv ∈ tw.vars → P .Fail) → (xv ∉ tw.vars → P (.Elim x w)) →
        (do
          let s4 ← store.Store.clear s3 store.Tbl.B
          let (b1, s5) ← term.occurs s4 x w
          if b1 then ok (span.Act.Fail, s5) else ok (span.Act.Elim x w, s5)) ⦃ a s' =>
            Inv s' ∧ s'.nodes.val = s.nodes.val ∧ tbl s' .A = tbl s .A ∧ P a ∧
              s'.ticks.val ≤ s.ticks.val + 8 + 8 * (t.subs ∪ u.subs).card ∧
              s.ticks.val ≤ s'.ticks.val ⦄ := by
      intro s3 hK3 x w xv tw hx hw hcard P hPf hPe
      have ht3 := hK3.ticks
      have hn3 : s3.nodes.val = s.nodes.val := by rw [hK3.nodes, hn2]
      have htb3 : tbl s3 = tbl s := by rw [hK3.tbl, htb2]
      step with clear_spec s3 .B hK3.inv (by unfold Room; omega) as ⟨s4, c1, c2, c3, c4, c5⟩
      have hn4 : s4.nodes.val = s.nodes.val := by rw [c1, hn3]
      step with occurs_spec hnm s4 x w (t := tw) (xv := xv) tw.subs c3 (by rw [hn4]; exact hw)
        (by rw [hn4]; exact hx) (fun k => by rw [c4])
        (Finset.Subset.refl _) (by unfold Room; omega) as ⟨b1, s5, hO⟩
      have hcO := hO.cost
      have hn5 : s5.nodes.val = s.nodes.val := by rw [hO.nodes, hn4]
      have hA5 : tbl s5 .A = tbl s .A := by rw [hO.tblA, c5 .A (by simp), htb3]
      cases b1 with
      | true =>
        simp only [↓reduceIte]
        step*
        exact ⟨hO.inv, hn5, hA5, hPf (by simpa using hO.res.symm), by omega,
          by have := hO.mono; omega⟩
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        step*
        exact ⟨hO.inv, hn5, hA5, hPe (by simpa using hO.res.symm), by omega,
          by have := hO.mono; omega⟩
    cases k with
    | Var =>
      obtain ⟨v, rfl, hv⟩ := hk
      simp only
      step with kind_spec (nm := nm) s2 q (t := u) hK2.inv (by rw [hn2]; exact hq)
        (by unfold Room; omega) as ⟨k1, s3, hk1, hK3⟩
      rw [hn2] at hk1
      have ht3 := hK3.ticks
      have hn3 : s3.nodes.val = s.nodes.val := by rw [hK3.nodes, hn2]
      have htb3 : tbl s3 = tbl s := by rw [hK3.tbl, htb2]
      cases k1 with
      | Var =>
        obtain ⟨w, rfl, hw⟩ := hk1
        step*
        refine ⟨hK3.inv, hn3, by rw [htb3], ?_, by simp only [actCost]; omega, by omega⟩
        have hvw : v ≠ w := fun e => hne (by rw [e])
        exact actOK_elim_left hv hq (fun e => hne e.symm) (by simpa [Term.vars] using hvw)
      | Atom =>
        obtain ⟨f, rfl⟩ := hk1
        step*
        refine ⟨hK3.inv, hn3, by rw [htb3], ?_, by simp only [actCost]; omega, by omega⟩
        exact actOK_elim_left hv hq (by simp) (by simp [Term.vars])
      | App a b =>
        obtain ⟨ta, tb, rfl, ha, hb⟩ := hk1
        simp only
        refine WP.spec_mono (hocc s3 hK3 p q v _ hv hq hcu (fun a => ActOK nm s.nodes.val (.var v) (.app ta tb) a ∧
            actCost (.var v) (.app ta tb) a = 8 + 8 * ((Term.var v).subs ∪ (ta.app tb).subs).card)
          (fun h => ⟨fun E o => solveOn_occurs_left h E o, rfl⟩)
          (fun h => ⟨actOK_elim_left hv hq (by simp) h, rfl⟩)) ?_
        rintro ⟨a', s'⟩ ⟨h1, h2, h3, ⟨h4, h4c⟩, h5, h6⟩
        exact ⟨h1, h2, h3, h4, by rw [h4c]; omega, h6⟩
    | Atom =>
      obtain ⟨f, rfl⟩ := hk
      simp only
      step with kind_spec (nm := nm) s2 q (t := u) hK2.inv (by rw [hn2]; exact hq)
        (by unfold Room; omega) as ⟨k1, s3, hk1, hK3⟩
      rw [hn2] at hk1
      have ht3 := hK3.ticks
      have hn3 : s3.nodes.val = s.nodes.val := by rw [hK3.nodes, hn2]
      have htb3 : tbl s3 = tbl s := by rw [hK3.tbl, htb2]
      cases k1 with
      | Var =>
        obtain ⟨w, rfl, hw⟩ := hk1
        step*
        refine ⟨hK3.inv, hn3, by rw [htb3], ?_, by simp only [actCost]; omega, by omega⟩
        exact actOK_elim_right hw hp (by simp) (by simp [Term.vars])
      | Atom =>
        obtain ⟨g, rfl⟩ := hk1
        step*
        refine ⟨hK3.inv, hn3, by rw [htb3], ?_, by simp only [actCost]; omega, by omega⟩
        exact fun E o => solveOn_clash (fun e => hne (by rw [e])) E o
      | App a b =>
        obtain ⟨ta, tb, rfl, ha, hb⟩ := hk1
        step*
        refine ⟨hK3.inv, hn3, by rw [htb3], ?_, by simp only [actCost]; omega, by omega⟩
        exact fun E o => solveOn_sym_app f ta tb E o
    | App a b =>
      obtain ⟨ta, tb, rfl, ha, hb⟩ := hk
      simp only
      step with kind_spec (nm := nm) s2 q (t := u) hK2.inv (by rw [hn2]; exact hq)
        (by unfold Room; omega) as ⟨k1, s3, hk1, hK3⟩
      rw [hn2] at hk1
      have ht3 := hK3.ticks
      have hn3 : s3.nodes.val = s.nodes.val := by rw [hK3.nodes, hn2]
      have htb3 : tbl s3 = tbl s := by rw [hK3.tbl, htb2]
      cases k1 with
      | Var =>
        obtain ⟨w, rfl, hw⟩ := hk1
        simp only
        refine WP.spec_mono (hocc s3 hK3 q p w _ hw hp hct (fun a => ActOK nm s.nodes.val (.app ta tb) (.var w) a ∧
            actCost (.app ta tb) (.var w) a = 8 + 8 * ((ta.app tb).subs ∪ (Term.var w).subs).card)
          (fun h => ⟨fun E o => solveOn_occurs_right h E o, rfl⟩)
          (fun h => ⟨actOK_elim_right hw hp (by simp) h, rfl⟩)) ?_
        rintro ⟨a', s'⟩ ⟨h1, h2, h3, ⟨h4, h4c⟩, h5, h6⟩
        exact ⟨h1, h2, h3, h4, by rw [h4c]; omega, h6⟩
      | Atom =>
        obtain ⟨g, rfl⟩ := hk1
        step*
        refine ⟨hK3.inv, hn3, by rw [htb3], ?_, by simp only [actCost]; omega, by omega⟩
        exact fun E o => solveOn_app_sym g ta tb E o
      | App c d =>
        obtain ⟨tc, td, rfl, hc, hd⟩ := hk1
        step*
        refine ⟨hK3.inv, hn3, by rw [htb3], ?_, by simp only [actCost]; omega, by omega⟩
        exact ⟨ta, tb, tc, td, rfl, rfl, hne, ha, hc, hb, hd⟩

/-! ## The list of equations in the store -/

theorem Repr.app_inv {nodes : List store.Node} {i : Nat} {ta tb : Pat}
    (h : Repr nm nodes i (.app ta tb)) :
    ∃ a b, nodes[i]? = some (.App a b) ∧ Repr nm nodes a.val ta ∧ Repr nm nodes b.val tb := by
  generalize ht : Term.app ta tb = t at h
  cases h with
  | var _ => cases ht
  | sym _ => cases ht
  | nil _ => cases ht
  | app h ha hb => cases ht; exact ⟨_, _, h, ha, hb⟩

theorem enc_of_not_app {nodes : List store.Node} {E : Eqns Nat} {i : Nat} {n : store.Node}
    (h : Repr nm nodes i (encEqs nm E)) (hn : nodes[i]? = some n) (hna : ∀ a b, n ≠ .App a b) :
    E = [] := by
  cases E with
  | nil => rfl
  | cons p E =>
    obtain ⟨a, b, h1, _, _⟩ := Repr.app_inv (ta := .app p.1 p.2) (tb := encEqs nm E) h
    rw [hn] at h1
    cases h1
    exact absurd rfl (hna a b)

theorem enc_of_app {nodes : List store.Node} {E : Eqns Nat} {i : Nat} {e rest : store.TermId}
    (h : Repr nm nodes i (encEqs nm E)) (hn : nodes[i]? = some (.App e rest)) :
    ∃ t u E', E = (t, u) :: E' ∧ Repr nm nodes e.val (.app t u) ∧
      Repr nm nodes rest.val (encEqs nm E') := by
  cases E with
  | nil =>
    obtain ⟨ta, tb, e', -, -⟩ := h.of_app hn
    cases e'
  | cons p E =>
    obtain ⟨ta, tb, e', ha, hb⟩ := h.of_app hn
    obtain ⟨t, u⟩ := p
    simp only [encEqs, Term.app.injEq] at e'
    obtain ⟨rfl, rfl⟩ := e'
    exact ⟨t, u, E, rfl, ha, hb⟩

/-! ## The loop -/

/-- What the loop reports: the output with the solution applied, which has
at most `D` distinct subterms, or that there is no solution. -/
def SolveRes (nm : Option Nat → Sym) (nodes : List store.Node) (D : Nat) (R : Option Pat)
    (ok : Bool) (out : store.TermId) : Prop :=
  if ok then ∃ o, Repr nm nodes out.val o ∧ R = some o ∧ o.subs.card ≤ D else R = none

/-- The invariant of the loop. `s0` is the store at the start, `B` the tick
count the loop must stay under, and `R` the answer of the specification. -/
def SolveInv (nm : Option Nat → Sym) (s0 : store.Store) (D L B : Nat) (R : Option Pat) :
    store.Store × store.TermId × store.TermId × Bool × Bool → Prop
  | (s, eqs, out, ok, go) => Inv s ∧ Extends s0 s ∧
    if go then ok = true ∧ ∃ E o, Repr nm s.nodes.val eqs.val (encEqs nm E) ∧
        Repr nm s.nodes.val out.val o ∧ solveOn E o = R ∧ Good D L E o ∧
        s.ticks.val + pot D (L + D) E ≤ B
    else s.ticks.val ≤ B ∧ SolveRes nm s.nodes.val D R ok out

theorem SolveInv.ticks_le {s0 : store.Store} {D L B : Nat} {R : Option Pat}
    {x : store.Store × store.TermId × store.TermId × Bool × Bool} (h : SolveInv nm s0 D L B R x) :
    x.1.ticks.val ≤ B := by
  obtain ⟨s, eqs, out, ok, go⟩ := x
  obtain ⟨-, -, h⟩ := h
  cases go
  · exact h.1
  · obtain ⟨-, E, o, -, -, -, -, hc⟩ := h
    simp only
    omega

def SolvePost (nm : Option Nat → Sym) (s0 : store.Store) (D B : Nat) (R : Option Pat) :
    store.Store × store.TermId × Bool → Prop
  | (s, out, ok) => Inv s ∧ Extends s0 s ∧ s.ticks.val ≤ B ∧ SolveRes nm s.nodes.val D R ok out

def BodyPost (nm : Option Nat → Sym) (s0 : store.Store) (D L B : Nat) (R : Option Pat)
    (t0 : Nat) :
    ControlFlow (store.Store × store.TermId × store.TermId × Bool × Bool)
      (store.Store × store.TermId × Bool) → Prop
  | .done y => SolvePost nm s0 D B R y
  | .cont x => SolveInv nm s0 D L B R x ∧ t0 < x.1.ticks.val

theorem solve_body_spec (hnm : Function.Injective nm) (s0 : store.Store) (D L B : Nat)
    (R : Option Pat) (hB : 40 * B + 100 ≤ Usize.max) (st : store.Store) (eqs out : store.TermId)
    (ok go : Bool) (h : SolveInv nm s0 D L B R (st, eqs, out, ok, go)) :
    span.solve_into_loop.body st eqs out ok go ⦃ r => BodyPost nm s0 D L B R st.ticks.val r ⦄ := by
  unfold span.solve_into_loop.body
  obtain ⟨hI, hE0, h⟩ := h
  cases go with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    step*
    exact ⟨hI, hE0, h.1, h.2⟩
  | true =>
    simp only [↓reduceIte] at h ⊢
    obtain ⟨hok, E, o, he, ho, hR, hG, hc⟩ := h
    subst hok
    have hge := pot_ge D (L + D) E
    have hDc := hG.dcount_le
    step with read_spec st eqs hI he.lt (by unfold Room; omega) as ⟨nd, s1, hnd, hK1⟩
    have ht1 := hK1.ticks
    have hn1 := hK1.nodes
    have hstop : (∀ a b, nd ≠ .App a b) →
        BodyPost nm s0 D L B R st.ticks.val (ControlFlow.cont (s1, eqs, out, true, false)) := by
      intro hna
      have hE := enc_of_not_app he hnd hna
      subst hE
      refine ⟨⟨hK1.inv, hE0.trans (Extends.of_eq hn1 (by omega)), ?_⟩, by simp only; omega⟩
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine ⟨by omega, ?_⟩
      simp only [SolveRes, ↓reduceIte]
      refine ⟨o, by rw [hn1]; exact ho, by rw [← hR, solveOn_nil], ?_⟩
      unfold dcount at hDc
      exact (Finset.card_le_card Finset.subset_union_right).trans hDc
    cases nd with
    | V0 => step*
    | VL a => step*
    | VR a => step*
    | Sym g => step*
    | Nil => step*
    | App e rest =>
      obtain ⟨t, u, E', hE, hpair, hrest⟩ := enc_of_app he hnd
      subst hE
      obtain ⟨p, q, hnode, hp, hq⟩ := Repr.app_inv hpair
      simp only
      step with read_spec s1 e hK1.inv (by rw [hn1]; exact hpair.lt) (by unfold Room; omega)
        as ⟨n1, s2, hn1', hK2⟩
      rw [hn1, hnode] at hn1'
      cases hn1'
      have ht2 := hK2.ticks
      have hn2 : s2.nodes.val = st.nodes.val := by rw [hK2.nodes, hn1]
      have hD : dcount ((t, u) :: E') o = (Eqns.subs ((t, u) :: E') ∪ o.subs).card := rfl
      have hctu : (t.subs ∪ u.subs).card ≤ dcount ((t, u) :: E') o := by
        apply Finset.card_le_card
        intro w hw
        simp only [Eqns.subs_cons, Finset.mem_union] at hw ⊢
        tauto
      simp only
      step with act_spec hnm s2 p q (t := t) (u := u) hK2.inv (by rw [hn2]; exact hp)
        (by rw [hn2]; exact hq) (by unfold Room; omega) as ⟨a, s3, hI3, hn3', htA3, hact, ht3, hm3⟩
      rw [hn2] at hact
      have hn3 : s3.nodes.val = st.nodes.val := by rw [hn3', hn2]
      have hext3 : Extends s0 s3 := hE0.trans (Extends.of_eq hn3 (by omega))
      cases a with
      | Skip =>
        simp only [ActOK] at hact
        subst hact
        simp only [actCost] at ht3
        step*
        refine ⟨⟨hI3, hext3, ?_⟩, by simp only; omega⟩
        simp only [↓reduceIte, true_and]
        refine ⟨E', o, by rw [hn3]; exact hrest, by rw [hn3]; exact ho, ?_, hG.skip, ?_⟩
        · rw [← hR, solveOn_refl]
        · have := pot_skip D (L + D) t E'
          omega
      | Fail =>
        simp only [ActOK] at hact
        simp only [actCost] at ht3
        step*
        refine ⟨⟨hI3, hext3, ?_⟩, by simp only; omega⟩
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine ⟨by omega, ?_⟩
        simp only [SolveRes, Bool.false_eq_true, ↓reduceIte]
        rw [← hR, hact]
      | Split a c b d =>
        obtain ⟨ta, tb, tc, td, rfl, rfl, hne, ha, hc', hb, hd⟩ := hact
        simp only [actCost] at ht3
        have hcs := pot_split D (L + D) E' hne
        simp only
        step with alloc_spec s3 (.App b d) hI3 ⟨by rw [hn3]; exact hb.lt, by rw [hn3]; exact hd.lt⟩
          (by unfold Room; omega) as ⟨e2, s4, hI4, ht4, htb4, hx4, hr4⟩
        have hst4 : Extends st s4 := (Extends.of_eq hn3 (by omega)).trans hx4
        simp only [norm] at hr4
        have hre2 : Repr nm s4.nodes.val e2.val (.app tb td) :=
          .app hr4 (hst4.repr hb) (hst4.repr hd)
        step with alloc_spec s4 (.App e2 rest) hI4 ⟨hre2.lt, (hst4.repr hrest).lt⟩
          (by unfold Room; omega) as ⟨r2, s5, hI5, ht5, htb5, hx5, hr5⟩
        have hst5 : Extends st s5 := hst4.trans hx5
        simp only [norm] at hr5
        have hrr2 : Repr nm s5.nodes.val r2.val (encEqs nm ((tb, td) :: E')) :=
          .app hr5 (hx5.repr hre2) (hst5.repr hrest)
        step with alloc_spec s5 (.App a c) hI5 ⟨(hst5.repr ha).lt, (hst5.repr hc').lt⟩
          (by unfold Room; omega) as ⟨e1, s6, hI6, ht6, htb6, hx6, hr6⟩
        have hst6 : Extends st s6 := hst5.trans hx6
        simp only [norm] at hr6
        have hre1 : Repr nm s6.nodes.val e1.val (.app ta tc) :=
          .app hr6 (hst6.repr ha) (hst6.repr hc')
        step with alloc_spec s6 (.App e1 r2) hI6 ⟨hre1.lt, (hx6.repr hrr2).lt⟩
          (by unfold Room; omega) as ⟨eqs1, s7, hI7, ht7, htb7, hx7, hr7⟩
        have hst7 : Extends st s7 := hst6.trans hx7
        simp only [norm] at hr7
        have hreqs : Repr nm s7.nodes.val eqs1.val (encEqs nm ((ta, tc) :: (tb, td) :: E')) :=
          .app hr7 (hx7.repr hre1) (hx7.repr (hx6.repr hrr2))
        refine ⟨⟨hI7, hE0.trans hst7, ?_⟩, by simp only; omega⟩
        simp only [↓reduceIte, true_and]
        refine ⟨_, o, hreqs, hst7.repr ho, ?_, hG.split, by omega⟩
        rw [← hR, solveOn_split]
      | Elim x w =>
        obtain ⟨xv, tu, hx, hw, hxn, hor, hsol⟩ := hact
        simp only [actCost] at ht3
        have hG' := hG.elim hxn hor
        have hce := pot_elim D (L + D) E' hxn hor hG'.lead_le
        have hdt := hG.skip.dcount_le
        have hlen := hG.len
        simp only [List.length_cons] at hlen
        simp only
        step with clear_spec s3 .A hI3 (by unfold Room; omega) as ⟨s4, c1, c2, c3, c4, c5⟩
        have hn4 : s4.nodes.val = st.nodes.val := by rw [c1, hn3]
        have hSc := card_subs_enc_le (nm := nm) E' o
        have hpc := pending_card_le (nm := nm) s4.nodes.val (tbl s4 .A)
          ((encEqs nm E').subs ∪ o.subs)
        have hleaf : LeafOK nm s4.nodes.val (tbl s4 .B) (term.Leaf.Sub x w) (single xv tu) :=
          ⟨xv, tu, by rw [hn4]; exact hx, by rw [hn4]; exact hw, rfl⟩
        step with rebuild_spec hnm s4 (term.Leaf.Sub x w) rest (t := encEqs nm E')
          (σ := single xv tu) ((encEqs nm E').subs ∪ o.subs) c3 (by rw [hn4]; exact hrest) hleaf
          (by intro k v hk; rw [c4] at hk; cases hk) Finset.subset_union_left
          (by unfold Room; omega) as ⟨eqs1, s5, hR5⟩
        have hc5 := hR5.cost
        step with rebuild_spec hnm s5 (term.Leaf.Sub x w) out (t := o)
          (σ := single xv tu) ((encEqs nm E').subs ∪ o.subs) hR5.inv
          (hR5.ext.repr (by rw [hn4]; exact ho)) (hleaf.extends hR5.ext) hR5.memo
          Finset.subset_union_right (by unfold Room; omega) as ⟨out1, s6, hR6⟩
        have hc6 := hR6.cost
        have hm5 := hR5.mono
        have hm6 := hR6.mono
        refine ⟨⟨hR6.inv, hE0.trans ((Extends.of_eq hn4 (by omega)).trans (hR5.ext.trans hR6.ext)), ?_⟩,
          by simp only; omega⟩
        simp only [↓reduceIte, true_and]
        refine ⟨Eqns.subst xv tu E', _, ?_, hR6.repr, ?_, hG', by omega⟩
        · rw [← enc_subst]; exact hR6.ext.repr hR5.repr
        · rw [← hR, hsol]

/-- `solve_into` returns the output with the solution of the equations
applied, or reports that there is none, and spends at most `solveCost`
ticks. -/
theorem solve_into_spec (hnm : Function.Injective nm) (s : store.Store) (eqs out : store.TermId)
    {E : Eqns Nat} {o : Pat} (hI : Inv s) (he : Repr nm s.nodes.val eqs.val (encEqs nm E))
    (ho : Repr nm s.nodes.val out.val o) (hroom : Room s (solveCost E o)) :
    span.solve_into s eqs out ⦃ r s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + solveCost E o ∧
        SolveRes nm s'.nodes.val (dcount E o) (solveOn E o) r.1 r.2 ⦄ := by
  unfold span.solve_into span.solve_into_loop
  have hB : 40 * (s.ticks.val + solveCost E o) + 100 ≤ Usize.max := hroom
  have hloop := loop.spec_decr_nat
    (fun x : store.Store × store.TermId × store.TermId × Bool × Bool =>
      s.ticks.val + solveCost E o + 1 - x.1.ticks.val)
    (SolveInv nm s (dcount E o) E.length (s.ticks.val + solveCost E o) (solveOn E o))
    (SolvePost nm s (dcount E o) (s.ticks.val + solveCost E o) (solveOn E o))
    (fun x : store.Store × store.TermId × store.TermId × Bool × Bool =>
      span.solve_into_loop.body x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
    (s, eqs, out, true, true)
    (by
      rintro ⟨st, eqs', out', ok', go'⟩ hinv
      refine WP.spec_mono (solve_body_spec hnm s _ _ _ _ hB st eqs' out' ok' go' hinv) ?_
      intro r hr
      cases r with
      | done y => exact hr
      | cont x' =>
        obtain ⟨h1, h2⟩ := hr
        have := h1.ticks_le
        exact ⟨h1, by simp only; omega⟩)
    ⟨hI, Extends.refl s, by
      simp only [↓reduceIte, true_and]
      exact ⟨E, o, he, ho, rfl, Good.init E o, Nat.le_refl _⟩⟩
  step with hloop as ⟨s', out', ok', hy⟩
  have hy' : Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + solveCost E o ∧
      SolveRes nm s'.nodes.val (dcount E o) (solveOn E o) ok' out' := hy
  obtain ⟨h1, h2, h3, h4⟩ := hy'
  step*

end RwLogVerified
