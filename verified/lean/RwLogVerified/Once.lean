/-
# No variable twice: the Rust `once_each`

`once_each s u` answers whether no variable occurs twice in the term at `u`.
It is called with table `A` holding, for each subterm of the term, what
`rebuild` with `Leaf::Right` made of it; a subterm is its own entry exactly
when it has no variable (`bind_right_eq_iff`), and such a subterm is not
entered. A subterm with a variable is flagged in table `B` when it is
entered, and entered a second time only to answer no. So a subterm is
entered at most once however often it occurs, and the charge is by the
distinct subterms of the term (`onceCost`).

`once_each_spec`: the answer is whether the variables of the term, listed
with repetition, have none twice; and when it is yes, table `B` flags the
variable nodes of the term and only nodes of subterms of the term
(`OnceFlags`).
-/
import RwLogVerified.Sorts

open Aeneas Aeneas.Std Result ControlFlow

namespace RwLogVerified

open rwlog_core RwLog

variable {nm : Option Nat → Sym}

/-- The substitution `Leaf::Right` stands for. -/
def rightSub : Nat → Pat := fun v => Term.var (2 * v + 1)

/-- A term is unchanged by `Leaf::Right` exactly when it has no variable. -/
theorem bind_right_eq_iff (t : Pat) : t.bind rightSub = t ↔ t.vars = [] := by
  induction t with
  | var v => simp only [Term.bind, rightSub, Term.vars]; simp; omega
  | sym f => simp [Term.bind, Term.vars]
  | app a b iha ihb => simp [Term.bind, Term.vars, iha, ihb]

/-- A subterm of a term with a node has a node. -/
theorem Repr.of_subs {nodes : List store.Node} {i : Nat} {t : Pat} (h : Repr nm nodes i t) :
    ∀ {q : Pat}, q ∈ t.subs → ∃ k, Repr nm nodes k q := by
  induction h with
  | var hv =>
    intro q hq
    simp only [Term.subs, Finset.mem_singleton] at hq
    subst hq
    exact ⟨_, .var hv⟩
  | sym hs =>
    intro q hq
    simp only [Term.subs, Finset.mem_singleton] at hq
    subst hq
    exact ⟨_, .sym hs⟩
  | nil hs =>
    intro q hq
    simp only [Term.subs, Finset.mem_singleton] at hq
    subst hq
    exact ⟨_, .nil hs⟩
  | app hn ha hb iha ihb =>
    intro q hq
    simp only [Term.subs, Finset.mem_insert, Finset.mem_union] at hq
    rcases hq with rfl | hq | hq
    · exact ⟨_, .app hn ha hb⟩
    · exact iha hq
    · exact ihb hq

/-- Table `A` holds, for each subterm of `u`, what `Leaf::Right` makes of
it. -/
def RightMemo (nm : Option Nat → Sym) (nodes : List store.Node) (A : Nat → Option Nat)
    (u : Pat) : Prop :=
  ∀ q ∈ u.subs, ∀ k, Repr nm nodes k q →
    ∃ g, A k = some g ∧ Repr nm nodes g (q.bind rightSub)

/-- What the table of flags holds when no variable occurs twice: every
variable of the term is flagged, and only subterms of the term are. -/
def OnceFlags (nm : Option Nat → Sym) (u : Pat) (nodes : List store.Node) (B : Nat → Option Nat) :
    Prop :=
  (∀ y ∈ u.vars, ∃ k, Repr nm nodes k (.var y) ∧ B k ≠ none) ∧
    ∀ k, B k ≠ none → ∃ q, Repr nm nodes k q ∧ q ∈ u.subs

/-- What the loop keeps true while it runs: `done` are the variables met,
`ps` the subterms still to enter. -/
structure OnceGo (nm : Option Nat → Sym) (u : Pat) (nodes : List store.Node) (B : Nat → Option Nat)
    (todo : Nat) (done : List Nat) (ps : List Pat) : Prop where
  todo : Repr nm nodes todo (encList (nm none) ps)
  sub : ∀ p ∈ ps, p ∈ u.subs
  vars : u.vars = done ++ ps.flatMap Term.vars
  nodup : done.Nodup
  seen : ∀ y ∈ done, ∃ k, Repr nm nodes k (.var y) ∧ B k ≠ none
  flag : ∀ k, B k ≠ none → ∃ q, Repr nm nodes k q ∧ q ∈ u.subs ∧
    ∀ y ∈ q.vars, y ∈ done ∨ ∃ p ∈ ps, p.size < q.size ∧ y ∈ p.vars

/-- The invariant of the loop. `s0` is the store at its start and `Bd` the
tick count it stays under. -/
def OnceInv (nm : Option Nat → Sym) (s0 : store.Store) (u : Pat) (Bd : Nat)
    (x : store.Store × store.TermId × Bool × Bool) : Prop :=
  Inv x.1 ∧ Extends s0 x.1 ∧ tbl x.1 .A = tbl s0 .A ∧
    if x.2.2.2 = true then
      x.2.2.1 = true ∧ ∃ done ps, OnceGo nm u x.1.nodes.val (tbl x.1 .B) x.2.1.val done ps ∧
        x.1.ticks.val +
          8 * (2 * (pending nm x.1.nodes.val (tbl x.1 .B) u.subs).card + ps.length) + 2 ≤ Bd
    else
      (x.2.2.1 = true ↔ u.vars.Nodup) ∧
        (x.2.2.1 = true → OnceFlags nm u x.1.nodes.val (tbl x.1 .B)) ∧ x.1.ticks.val + 1 ≤ Bd

/-- What the loop leaves. -/
def OncePost (nm : Option Nat → Sym) (s0 : store.Store) (u : Pat) (Bd : Nat)
    (y : Bool × store.Store) : Prop :=
  Inv y.2 ∧ Extends s0 y.2 ∧ tbl y.2 .A = tbl s0 .A ∧ (y.1 = true ↔ u.vars.Nodup) ∧
    (y.1 = true → OnceFlags nm u y.2.nodes.val (tbl y.2 .B)) ∧ y.2.ticks.val ≤ Bd

theorem update_ne_none {B : Nat → Option Nat} {q : Nat} {r : Nat} :
    ∀ k, B k ≠ none → Function.update B q (some r) k ≠ none := by
  intro k hk
  by_cases e : k = q
  · subst e; simp
  · rw [Function.update_of_ne e]; exact hk

theorem once_each_body_spec (hnm : Function.Injective nm) (s0 : store.Store) (u : Pat) (Bd : Nat)
    (hB : 40 * Bd + 100 ≤ Usize.max) {un : Nat} (hu : Repr nm s0.nodes.val un u)
    (hA : RightMemo nm s0.nodes.val (tbl s0 .A) u)
    (s : store.Store) (todo : store.TermId) (ok go : Bool)
    (h : OnceInv nm s0 u Bd (s, todo, ok, go)) :
    sorts.once_each_loop.body s todo ok go ⦃ r =>
      match r with
      | .done y => OncePost nm s0 u Bd y
      | .cont x => OnceInv nm s0 u Bd x ∧ s.ticks.val < x.1.ticks.val ⦄ := by
  unfold sorts.once_each_loop.body
  obtain ⟨hI, hE, hTA, hrest⟩ := h
  cases go with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hrest ⊢
    simp only [WP.spec_ok]
    exact ⟨hI, hE, hTA, hrest.1, hrest.2.1, by have := hrest.2.2; show s.ticks.val ≤ Bd; omega⟩
  | true =>
    simp only [↓reduceIte] at hrest ⊢
    obtain ⟨rfl, done, ps, hG, hc⟩ := hrest
    have hN : NodesOK s.nodes.val := hI.nodesOK
    cases ps with
    | nil =>
      step with uncons_repr s todo hI.toWf (p := Term.sym (nm none)) hG.todo
        (by unfold Room; omega) as ⟨o, s1, hK0, hu0⟩
      have K1 : Kept s s1 1 := hK0.kept hI
      have ht1 := K1.ticks
      have hx1 : Extends s s1 := Extends.of_eq K1.nodes (by omega)
      subst hu0
      simp only [WP.spec_ok]
      have hv : u.vars = done := by simpa using hG.vars
      refine ⟨⟨K1.inv, hE.trans hx1, by rw [K1.tbl, hTA], ?_⟩, by show s.ticks.val < s1.ticks.val; omega⟩
      simp only [Bool.false_eq_true, ↓reduceIte, true_iff, forall_const]
      refine ⟨by rw [hv]; exact hG.nodup, ⟨?_, ?_⟩, by omega⟩
      · intro y hy
        rw [hv] at hy
        rw [K1.nodes, K1.tbl]
        exact hG.seen y hy
      · intro k hk
        rw [K1.tbl] at hk
        obtain ⟨q, hq, hqs, -⟩ := hG.flag k hk
        exact ⟨q, by rw [K1.nodes]; exact hq, hqs⟩
    | cons q rest =>
      step with uncons_repr s todo hI.toWf (p := Term.app q (encList (nm none) rest)) hG.todo
        (by unfold Room; omega) as ⟨o, s1, hK0, hu0⟩
      have K1 : Kept s s1 1 := hK0.kept hI
      have ht1 := K1.ticks
      obtain ⟨qi, ri, rfl, rq, rrest⟩ := hu0
      simp only [List.length_cons] at hc
      have hqs : q ∈ u.subs := hG.sub q List.mem_cons_self
      -- the entry of the subterm in table `A`
      obtain ⟨k0, hk0⟩ := hu.of_subs hqs
      have hk0' : Repr nm s.nodes.val k0 q := hE.repr hk0
      have ek : k0 = qi.val := Repr.inj hnm hN hk0' rq
      obtain ⟨g0, hg0, rg0⟩ := hA q hqs k0 hk0
      rw [ek] at hg0
      simp only
      step with get_spec s1 .A qi K1.inv (by rw [K1.nodes]; exact rq.lt) (by unfold Room; omega)
        as ⟨o1, s2, ho1, K2⟩
      rw [K1.tbl, hTA, hg0] at ho1
      have ht2 := K2.ticks
      cases o1 with
      | none => simp at ho1
      | some g =>
        simp only [Option.map_some, Option.some.injEq] at ho1
        simp only
        step with same_spec s2 g qi K2.inv (by unfold Room; omega) as ⟨b, s3, hb, K3⟩
        have ht3 := K3.ticks
        have hn3 : s3.nodes.val = s.nodes.val := by rw [K3.nodes, K2.nodes, K1.nodes]
        have htb3 : tbl s3 = tbl s := by rw [K3.tbl, K2.tbl, K1.tbl]
        have rg : Repr nm s.nodes.val g.val (q.bind rightSub) := by
          rw [ho1]; exact hE.repr rg0
        have hvars : u.vars = done ++ (q.vars ++ rest.flatMap Term.vars) := by
          simpa using hG.vars
        by_cases e : g.val = qi.val
        · -- no variable: not entered
          have hb' : b = true := by simp [hb, e]
          subst hb'
          have hgr : q.vars = [] := by
            rw [e] at rg
            exact (bind_right_eq_iff q).1 (rg.unique rq)
          simp only [↓reduceIte, WP.spec_ok]
          have hx3 : Extends s s3 := Extends.of_eq hn3 (by omega)
          refine ⟨⟨K3.inv, hE.trans hx3, by rw [htb3, hTA], ?_⟩,
            by show s.ticks.val < s3.ticks.val; omega⟩
          simp only [↓reduceIte, true_and]
          refine ⟨done, rest, ⟨by rw [hn3]; exact rrest,
            fun p hp => hG.sub p (List.mem_cons_of_mem _ hp), by rw [hvars, hgr]; rfl, hG.nodup,
            by rw [hn3, htb3]; exact hG.seen, ?_⟩, ?_⟩
          · intro k hk
            rw [htb3] at hk
            obtain ⟨q', hq', hq's, hall⟩ := hG.flag k hk
            refine ⟨q', by rw [hn3]; exact hq', hq's, fun y hy => ?_⟩
            rcases hall y hy with hd | ⟨p, hp, hlt, hyp⟩
            · exact .inl hd
            · rcases List.mem_cons.1 hp with rfl | hp
              · rw [hgr] at hyp; cases hyp
              · exact .inr ⟨p, hp, hlt, hyp⟩
          · rw [hn3, htb3]
            omega
        · have hb' : b = false := by simp [hb, e]
          subst hb'
          have hng : q.vars ≠ [] := by
            intro hgr
            have := (bind_right_eq_iff q).2 hgr
            rw [this] at rg
            exact e (Repr.inj hnm hN rg rq)
          simp only [Bool.false_eq_true, ↓reduceIte]
          step with get_flag_spec s3 .B qi K3.inv (by rw [hn3]; exact rq.lt)
            (by unfold Room; omega) as ⟨o2, s4, ho2, K4⟩
          rw [htb3] at ho2
          have ht4 := K4.ticks
          have hn4 : s4.nodes.val = s.nodes.val := by rw [K4.nodes, hn3]
          have htb4 : tbl s4 = tbl s := by rw [K4.tbl, htb3]
          cases hfl : tbl s .B qi.val with
          | some fl =>
            -- entered before: a variable occurs twice
            rw [hfl] at ho2
            subst ho2
            simp only [Option.map_some, Option.isSome_some, ↓reduceIte, WP.spec_ok]
            have hx4 : Extends s s4 := Extends.of_eq hn4 (by omega)
            refine ⟨⟨K4.inv, hE.trans hx4, by rw [htb4, hTA], ?_⟩,
              by show s.ticks.val < s4.ticks.val; omega⟩
            simp only [Bool.false_eq_true, ↓reduceIte, false_iff, false_imp_iff, true_and]
            refine ⟨fun hnd => ?_, by omega⟩
            obtain ⟨q', hq', -, hall⟩ := hG.flag qi.val (by rw [hfl]; simp)
            have := hq'.unique rq
            subst this
            obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ hng
            rw [hvars] at hnd
            rcases hall y hy with hd | ⟨p, hp, hlt, hyp⟩
            · exact List.disjoint_of_nodup_append hnd hd (List.mem_append_left _ hy)
            · rcases List.mem_cons.1 hp with rfl | hp
              · omega
              · exact List.disjoint_of_nodup_append hnd.of_append_right hy
                  (List.mem_flatMap.2 ⟨p, hp, hyp⟩)
          | none =>
            rw [hfl] at ho2
            subst ho2
            simp only [Option.map_none, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
            step with set_flag_spec s4 .B qi true K4.inv (by rw [hn4]; exact rq.lt)
              (by unfold Room; omega) as ⟨s5, n5, t5, hI5, tb5, tbo5⟩
            rw [htb4] at tb5
            simp only [↓reduceIte] at tb5
            have hn5 : s5.nodes.val = s.nodes.val := by rw [n5, hn4]
            step with read_spec s5 qi hI5 (by rw [hn5]; exact rq.lt) (by unfold Room; omega)
              as ⟨nd, s6, hnd, K6⟩
            rw [hn5] at hnd
            have ht6 := K6.ticks
            have hn6 : s6.nodes.val = s.nodes.val := by rw [K6.nodes, hn5]
            have hB6 : tbl s6 .B = Function.update (tbl s .B) qi.val (some 1) := by
              rw [K6.tbl, tb5]
            have hA6 : tbl s6 .A = tbl s0 .A := by
              rw [K6.tbl, tbo5 .A (by simp), htb4, hTA]
            have hpend := pending_set_card hnm hN rq hfl hqs 1
            have hmono := update_ne_none (B := tbl s .B) (q := qi.val) (r := 1)
            -- a variable: it is met for the first time
            have hvar : ∀ y, q = Term.var y →
                OnceInv nm s0 u Bd (s6, ri, true, true) ∧ s.ticks.val < s6.ticks.val := by
              rintro y rfl
              have hyd : y ∉ done := by
                intro hmem
                obtain ⟨k, hk, hfk⟩ := hG.seen y hmem
                rw [Repr.inj hnm hN hk rq] at hfk
                exact hfk hfl
              have hx6 : Extends s s6 := Extends.of_eq hn6 (by omega)
              refine ⟨⟨K6.inv, hE.trans hx6, hA6, ?_⟩, by show s.ticks.val < s6.ticks.val; omega⟩
              simp only [↓reduceIte, true_and]
              refine ⟨done ++ [y], rest, ⟨by rw [hn6]; exact rrest,
                fun p hp => hG.sub p (List.mem_cons_of_mem _ hp), ?_, ?_, ?_, ?_⟩, ?_⟩
              · rw [hvars]; simp [Term.vars]
              · exact List.Nodup.append hG.nodup (List.nodup_singleton y)
                  (by simpa using hyd)
              · intro y' hy'
                rw [hn6, hB6]
                rcases List.mem_append.1 hy' with hy' | hy'
                · obtain ⟨k, hk, hfk⟩ := hG.seen y' hy'
                  exact ⟨k, hk, hmono k hfk⟩
                · simp only [List.mem_singleton] at hy'
                  subst hy'
                  exact ⟨qi.val, rq, by simp⟩
              · intro k hk
                rw [hB6] at hk
                rw [hn6]
                by_cases ek' : k = qi.val
                · subst ek'
                  refine ⟨_, rq, hqs, fun y' hy' => .inl ?_⟩
                  simp only [Term.vars, List.mem_singleton] at hy'
                  simp [hy']
                · rw [Function.update_of_ne ek'] at hk
                  obtain ⟨q', hq', hq's, hall⟩ := hG.flag k hk
                  refine ⟨q', hq', hq's, fun y' hy' => ?_⟩
                  rcases hall y' hy' with hd | ⟨p, hp, hlt, hyp⟩
                  · exact .inl (List.mem_append_left _ hd)
                  · rcases List.mem_cons.1 hp with rfl | hp
                    · simp only [Term.vars, List.mem_singleton] at hyp
                      exact .inl (by simp [hyp])
                    · exact .inr ⟨p, hp, hlt, hyp⟩
              · rw [hn6, hB6]
                omega
            cases nd with
            | V0 =>
              obtain ⟨y, hy, -⟩ := rq.of_var hnd trivial
              simp only [WP.spec_ok]
              exact hvar y hy
            | VL a =>
              obtain ⟨y, hy, -⟩ := rq.of_var hnd trivial
              simp only [WP.spec_ok]
              exact hvar y hy
            | VR a =>
              obtain ⟨y, hy, -⟩ := rq.of_var hnd trivial
              simp only [WP.spec_ok]
              exact hvar y hy
            | Sym f =>
              have := rq.of_sym hnd
              subst this
              exact absurd rfl hng
            | Nil =>
              have := rq.of_nil hnd
              subst this
              exact absurd rfl hng
            | App a b =>
              obtain ⟨ta, tb, rfl, ra, rb⟩ := rq.of_app hnd
              simp only
              step with alloc_spec s6 (.App b ri) K6.inv
                ⟨by rw [hn6]; exact rb.lt, by rw [hn6]; exact rrest.lt⟩ (by unfold Room; omega)
                as ⟨l, s7, hI7, ht7, htb7, hx7, hl⟩
              simp only [norm] at hl
              have hx67 : Extends s s7 := (Extends.of_eq hn6 (by omega)).trans hx7
              step with alloc_spec s7 (.App a l) hI7
                ⟨(hx67.repr ra).lt, (List.getElem?_eq_some_iff.1 hl).1⟩ (by unfold Room; omega)
                as ⟨todo1, s8, hI8, ht8, htb8, hx8, htd⟩
              simp only [norm] at htd
              have hx8' : Extends s s8 := hx67.trans hx8
              obtain ⟨more, hmore, -⟩ := hx8'
              have hx8' : Extends s s8 := hx67.trans hx8
              have hB8 : tbl s8 .B = Function.update (tbl s .B) qi.val (some 1) := by
                rw [htb8, htb7, hB6]
              have hsz : ta.size < (Term.app ta tb).size ∧ tb.size < (Term.app ta tb).size := by
                simp only [Term.size]; omega
              refine ⟨⟨hI8, hE.trans hx8', by rw [htb8, htb7, hA6], ?_⟩,
                by show s.ticks.val < s8.ticks.val; omega⟩
              simp only [↓reduceIte, true_and]
              refine ⟨done, ta :: tb :: rest, ⟨?_, ?_, ?_, hG.nodup, ?_, ?_⟩, ?_⟩
              · have rl : Repr nm s7.nodes.val l.val (encList (nm none) (tb :: rest)) :=
                  .app hl (hx67.repr rb) (hx67.repr rrest)
                exact .app htd (hx8'.repr ra) (hx8.repr rl)
              · intro p hp
                simp only [List.mem_cons] at hp
                rcases hp with rfl | rfl | hp
                · exact Term.subs_app_left hqs
                · exact Term.subs_app_right hqs
                · exact hG.sub p (List.mem_cons_of_mem _ hp)
              · rw [hvars]; simp [Term.vars]
              · intro y hy
                obtain ⟨k, hk, hfk⟩ := hG.seen y hy
                exact ⟨k, hx8'.repr hk, by rw [hB8]; exact hmono k hfk⟩
              · intro k hk
                rw [hB8] at hk
                by_cases ek' : k = qi.val
                · subst ek'
                  refine ⟨_, hx8'.repr rq, hqs, fun y hy => .inr ?_⟩
                  simp only [Term.vars, List.mem_append] at hy
                  rcases hy with hy | hy
                  · exact ⟨ta, by simp, hsz.1, hy⟩
                  · exact ⟨tb, by simp, hsz.2, hy⟩
                · rw [Function.update_of_ne ek'] at hk
                  obtain ⟨q', hq', hq's, hall⟩ := hG.flag k hk
                  refine ⟨q', hx8'.repr hq', hq's, fun y hy => ?_⟩
                  rcases hall y hy with hd | ⟨p, hp, hlt, hyp⟩
                  · exact .inl hd
                  · rcases List.mem_cons.1 hp with rfl | hp
                    · simp only [Term.vars, List.mem_append] at hyp
                      rcases hyp with hyp | hyp
                      · exact .inr ⟨ta, by simp, by omega, hyp⟩
                      · exact .inr ⟨tb, by simp, by omega, hyp⟩
                    · exact .inr ⟨p, by simp [hp], hlt, hyp⟩
              · have hp8 : (pending nm s8.nodes.val (tbl s8 .B) u.subs).card ≤
                    (pending nm s.nodes.val (Function.update (tbl s .B) qi.val (some 1))
                      u.subs).card := by
                  rw [hmore, hB8]
                  exact Finset.card_le_card (pending_mono fun _ h => h)
                simp only [List.length_cons]
                omega

/-- The ticks `once_each` may take. -/
def onceCost (t : Pat) : Nat := 8 * (2 * t.subs.card + 1) + 6

/-- `once_each` answers whether no variable occurs twice in the term. Table
`A` holds what `Leaf::Right` makes of each subterm, and is left as it was;
when the answer is yes, table `B` flags the variables of the term and only
subterms of it. -/
theorem once_each_spec (hnm : Function.Injective nm) (s : store.Store) (u : store.TermId)
    {up : Pat} (hI : Inv s) (hu : Repr nm s.nodes.val u.val up)
    (hA : RightMemo nm s.nodes.val (tbl s .A) up) (hroom : Room s (onceCost up)) :
    sorts.once_each s u ⦃ b s' =>
      Inv s' ∧ Extends s s' ∧ tbl s' .A = tbl s .A ∧ (b = true ↔ up.vars.Nodup) ∧
        (b = true → OnceFlags nm up s'.nodes.val (tbl s' .B)) ∧
        s'.ticks.val ≤ s.ticks.val + onceCost up ⦄ := by
  unfold sorts.once_each sorts.once_each_loop
  have hroom' := hroom
  unfold Room at hroom'
  unfold onceCost at hroom'
  step with alloc_spec s .Nil hI trivial (by unfold Room; omega)
    as ⟨nil, s1, hI1, ht1, htb1, hx1, hr1⟩
  simp only [norm] at hr1
  step with clear_spec s1 .B hI1 (by unfold Room; omega) as ⟨s2, n2, t2, hI2, tb2, tbo2⟩
  have hx2 : Extends s s2 := hx1.trans (Extends.of_eq n2 (by omega))
  have hu2 : Repr nm s2.nodes.val u.val up := hx2.repr hu
  step with alloc_spec s2 (.App u nil) hI2
    ⟨hu2.lt, by rw [n2]; exact (List.getElem?_eq_some_iff.1 hr1).1⟩ (by unfold Room; omega)
    as ⟨todo, s3, hI3, ht3, htb3, hx3, htd⟩
  simp only [norm] at htd
  have hx03 : Extends s s3 := hx2.trans hx3
  have hA3 : tbl s3 .A = tbl s .A := by rw [htb3, tbo2 .A (by simp), htb1]
  have hB3 : ∀ k, tbl s3 .B k = none := by rw [htb3]; exact tb2
  let Bd := s.ticks.val + onceCost up
  have hA' : RightMemo nm s3.nodes.val (tbl s3 .A) up := by
    intro q hq k hk
    obtain ⟨k0, hk0⟩ := hu.of_subs hq
    have := Repr.inj hnm hI3.nodesOK (hx03.repr hk0) hk
    subst this
    obtain ⟨g, hg, rg⟩ := hA q hq k0 hk0
    exact ⟨g, by rw [hA3]; exact hg, hx03.repr rg⟩
  have hnil : Repr nm s3.nodes.val nil.val (encList (nm none) []) :=
    hx3.repr (by rw [n2]; exact .nil hr1)
  have hpc := pending_card_le (nm := nm) s3.nodes.val (tbl s3 .B) up.subs
  have hloop := loop.spec_decr_nat
    (fun x : store.Store × store.TermId × Bool × Bool => Bd + 1 - x.1.ticks.val)
    (fun x => OnceInv nm s3 up Bd x)
    (fun y : Bool × store.Store => OncePost nm s3 up Bd y)
    (fun x : store.Store × store.TermId × Bool × Bool =>
      sorts.once_each_loop.body x.1 x.2.1 x.2.2.1 x.2.2.2) (s3, todo, true, true)
    (by
      rintro ⟨y, td, ok, go⟩ hinv
      refine WP.spec_mono (once_each_body_spec hnm s3 up Bd (by unfold Bd onceCost; omega)
        (hx03.repr hu) hA' y td ok go hinv) ?_
      intro r hr
      cases r with
      | done z => exact hr
      | cont x' =>
        obtain ⟨h1, h2⟩ := hr
        refine ⟨h1, ?_⟩
        obtain ⟨-, -, -, h3⟩ := h1
        have : x'.1.ticks.val + 1 ≤ Bd := by
          split at h3
          · obtain ⟨-, d, p, -, hc⟩ := h3; omega
          · exact h3.2.2
        simp only at h2 ⊢
        omega)
    ⟨hI3, Extends.refl s3, rfl, by
      simp only [↓reduceIte, true_and]
      refine ⟨[], [up], ⟨.app htd (hx3.repr hu2) hnil, ?_, by simp, List.nodup_nil, ?_, ?_⟩, ?_⟩
      · intro p hp
        simp only [List.mem_singleton] at hp
        subst hp
        exact Term.self_mem_subs p
      · intro y hy; cases hy
      · intro k hk; exact absurd (hB3 k) hk
      · simp only [List.length_singleton]
        unfold Bd onceCost
        omega⟩
  refine WP.spec_mono hloop ?_
  rintro ⟨b, s'⟩ ⟨hI', hx', hA'', hb, hfl, ht'⟩
  exact ⟨hI', hx03.trans hx', by rw [hA'', hA3], hb, hfl, ht'⟩

end RwLogVerified
