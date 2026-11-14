/-
# A flagged variable outside a subterm: the Rust `any_marked` and `marked_outside`

`any_marked s l` answers whether table `B` flags a variable of a list.

`marked_outside s u t` answers whether a variable that table `B` flags is at
a place of the term at `t` that is not inside an occurrence of the term at
`u`, as an argument or as the whole term: the places `Sorts.outV` lists.
The terms to visit are a list on the store; table `A` flags the ones
visited, so a subterm is visited once however often it occurs, and the
charge is a sum over the distinct subterms of the term (`markedCost`).
-/
import RwLog.Sorts.Fold
import RwLogVerified.Once
import RwLogVerified.Push

open Aeneas Aeneas.Std Result ControlFlow

namespace RwLogVerified

open rwlog_core RwLog

variable {nm : Option Nat → Sym}

/-! ## What the terms without an entry still cost -/

/-- The sum of a weight over the terms of a set without a table entry. -/
noncomputable def owedW (nm : Option Nat → Sym) (nodes : List store.Node) (A : Nat → Option Nat)
    (S : Finset Pat) (w : Pat → Nat) : Nat :=
  (pending nm nodes A S).sum w

theorem owedW_le_sum (nodes : List store.Node) (A : Nat → Option Nat) (S : Finset Pat)
    (w : Pat → Nat) : owedW nm nodes A S w ≤ S.sum w :=
  Finset.sum_le_sum_of_subset fun _ hu => (mem_pending.1 hu).1

theorem owedW_mono {nodes more : List store.Node} {A A' : Nat → Option Nat} {S : Finset Pat}
    (hA : ∀ k, A k ≠ none → A' k ≠ none) (w : Pat → Nat) :
    owedW nm (nodes ++ more) A' S w ≤ owedW nm nodes A S w :=
  Finset.sum_le_sum_of_subset (pending_mono hA)

/-- Giving a term its entry takes its weight off. -/
theorem owedW_set (hnm : Function.Injective nm) {nodes more : List store.Node}
    (hN : NodesOK nodes) {A A' : Nat → Option Nat} {S : Finset Pat} {t : Pat} {q : Nat}
    (hq : Repr nm nodes q t) (hnone : A q = none) (ht : t ∈ S) (hA' : A' q ≠ none)
    (hA : ∀ k, A k ≠ none → A' k ≠ none) (w : Pat → Nat) :
    owedW nm (nodes ++ more) A' S w + w t ≤ owedW nm nodes A S w := by
  have hmem := mem_pending_of_none hnm hN hq hnone ht
  have hsub : pending nm (nodes ++ more) A' S ⊆ (pending nm nodes A S).erase t := by
    intro x hx
    have := pending_after_set (nm := nm) (S := S) (hq.append more) hA' hA hx
    rw [mem_pending] at this
    exact Finset.mem_erase.2 ⟨(Finset.mem_erase.1 this.1).1,
      mem_pending.2 ⟨(Finset.mem_erase.1 this.1).2, this.2⟩⟩
  have h1 := Nat.add_le_add_right (Finset.sum_le_sum_of_subset (f := w) hsub) (w t)
  rw [Finset.sum_erase_add (pending nm nodes A S) w hmem] at h1
  exact h1

/-! ## The places outside a subterm, by arguments -/

theorem outF_unspine (u : Pat) : ∀ (p : Pat) (acc : List Pat),
    Sorts.outF u (unspine p acc).1 ++ (unspine p acc).2.flatMap (Sorts.outV u) =
      Sorts.outF u p ++ acc.flatMap (Sorts.outV u)
  | .var _, _ => rfl
  | .sym _, _ => rfl
  | .app g b, acc => by
    rw [unspine, outF_unspine u g (b :: acc)]
    simp [Sorts.outF, Sorts.outV, List.append_assoc]

/-- A place outside `u` in a term that is not `u` and not a variable is a
place outside `u` in one of its arguments. -/
theorem mem_outV_args {u q : Pat} (hfo : q.firstOrder = true) (hnv : ∀ v, q ≠ .var v)
    (hne : q ≠ u) {y : Nat} :
    y ∈ Sorts.outV u q ↔ ∃ a ∈ (unspine q []).2, y ∈ Sorts.outV u a := by
  obtain ⟨f, hf⟩ := unspine_head q [] hfo hnv
  have h := outF_unspine u q []
  rw [hf] at h
  simp only [Sorts.outF, List.nil_append, List.flatMap_nil, List.append_nil] at h
  rw [Sorts.outV, ite_eq_right hne, ← h, List.mem_flatMap]

theorem outV_self (u : Pat) : Sorts.outV u u = [] := by simp [Sorts.outV]

/-! ## A flagged variable of a list -/

theorem any_marked_loop_spec (hnm : Function.Injective nm) :
    ∀ (xs : List Nat) (s : store.Store) (l : store.TermId),
    Inv s → Repr nm s.nodes.val l.val (encList (nm none) (xs.map Term.var)) →
    Room s (2 * xs.length + 1) →
    sorts.any_marked_loop s false l true ⦃ res s' =>
      Inv s' ∧ s'.nodes.val = s.nodes.val ∧ tbl s' = tbl s ∧
        (s.ticks.val ≤ s'.ticks.val ∧ s'.ticks.val ≤ s.ticks.val + 2 * xs.length + 1) ∧
        (res = true ↔ ∃ x ∈ xs, ∃ k, Repr nm s.nodes.val k (.var x) ∧ tbl s .B k ≠ none) ⦄ := by
  intro xs
  induction xs with
  | nil =>
    intro s l hI hl hroom
    have hroom' := hroom
    unfold Room at hroom'
    unfold sorts.any_marked_loop
    rw [loop]
    simp only [sorts.any_marked_loop.body, ↓reduceIte]
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
    exact ⟨K1.inv, K1.nodes, K1.tbl, by omega, by simp only [List.length_nil]; omega, by simp⟩
  | cons x xs ih =>
    intro s l hI hl hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons] at hroom'
    unfold sorts.any_marked_loop
    rw [loop]
    simp only [sorts.any_marked_loop.body, ↓reduceIte]
    step with uncons_repr s l hI.toWf
      (p := Term.app (.var x) (encList (nm none) (xs.map Term.var))) hl
      (by unfold Room; omega) as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    obtain ⟨v, rest, rfl, rv, rrest⟩ := hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    step with get_flag_spec s1 .B v K1.inv (by rw [K1.nodes]; exact rv.lt)
      (by unfold Room; omega) as ⟨r1, ho1, K2⟩
    obtain ⟨o1, s2⟩ := r1
    simp only at ho1
    simp only at K2
    rw [K1.tbl] at ho1
    have ht2 := K2.ticks
    have hn2 : s2.nodes.val = s.nodes.val := by rw [K2.nodes, K1.nodes]
    have htb2 : tbl s2 = tbl s := by rw [K2.tbl, K1.tbl]
    cases hfl : tbl s .B v.val with
    | none =>
      rw [hfl] at ho1
      subst ho1
      simp only [Option.map_none, uncurry, bind_ok]
      have IH := ih s2 rest K2.inv (by rw [hn2]; exact rrest) (by unfold Room; omega)
      unfold sorts.any_marked_loop at IH
      refine WP.spec_mono IH ?_
      rintro ⟨res, s'⟩ ⟨hI', hn', htb', ⟨hm', ht'⟩, hres'⟩
      refine ⟨hI', by rw [hn', hn2], by rw [htb', htb2], by omega, by simp only [List.length_cons]; omega,
        ?_⟩
      rw [hres', hn2, htb2]
      constructor
      · rintro ⟨y, hy, h⟩
        exact ⟨y, List.mem_cons_of_mem _ hy, h⟩
      · rintro ⟨y, hy, k, hk, hfk⟩
        rcases List.mem_cons.1 hy with rfl | hy
        · rw [Repr.inj hnm hI.nodesOK hk rv] at hfk
          exact absurd hfl hfk
        · exact ⟨y, hy, k, hk, hfk⟩
    | some fl =>
      rw [hfl] at ho1
      subst ho1
      simp only [Option.map_some, uncurry, bind_ok]
      rw [loop]
      simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, WP.spec_ok]
      refine ⟨K2.inv, hn2, htb2, by omega, by simp only [List.length_cons]; omega, ?_⟩
      simp only [true_iff]
      exact ⟨x, List.mem_cons_self, v.val, rv, by rw [hfl]; simp⟩

/-- `any_marked` answers whether table `B` flags a variable of the list. -/
theorem any_marked_spec (hnm : Function.Injective nm) (xs : List Nat) (s : store.Store)
    (l : store.TermId) (hI : Inv s)
    (hl : Repr nm s.nodes.val l.val (encList (nm none) (xs.map Term.var)))
    (hroom : Room s (2 * xs.length + 1)) :
    sorts.any_marked s l ⦃ res s' =>
      Inv s' ∧ s'.nodes.val = s.nodes.val ∧ tbl s' = tbl s ∧
        (s.ticks.val ≤ s'.ticks.val ∧ s'.ticks.val ≤ s.ticks.val + 2 * xs.length + 1) ∧
        (res = true ↔ ∃ x ∈ xs, ∃ k, Repr nm s.nodes.val k (.var x) ∧ tbl s .B k ≠ none) ⦄ := by
  unfold sorts.any_marked
  exact any_marked_loop_spec hnm xs s l hI hl hroom

/-! ## A flagged variable outside a subterm -/

/-- The weight of a subterm in the charge of `marked_outside`. -/
def outW (q : Pat) : Nat := 9 * nargs q + 6

/-- What the loop keeps true while it runs: `ps` are the terms still to
visit, and `M` says which variables are flagged. -/
structure OutGo (nm : Option Nat → Sym) (M : Nat → Prop) (u t : Pat) (nodes : List store.Node)
    (A : Nat → Option Nat) (todo : Nat) (ps : List Pat) : Prop where
  todo : Repr nm nodes todo (encList (nm none) ps)
  sub : ∀ p ∈ ps, p ∈ t.subs ∧ p.firstOrder = true
  out : ∀ p ∈ ps, ∀ y ∈ Sorts.outV u p, y ∈ Sorts.outV u t
  flag : ∀ k, A k ≠ none → ∃ q, Repr nm nodes k q ∧ q ∈ t.subs ∧ q.firstOrder = true ∧ q ≠ u ∧
    (∀ x, q = .var x → ¬ M x) ∧
    ∀ a ∈ (unspine q []).2, a = u ∨ (∃ k', Repr nm nodes k' a ∧ A k' ≠ none) ∨ a ∈ ps
  root : t = u ∨ (∃ k', Repr nm nodes k' t ∧ A k' ≠ none) ∨ t ∈ ps

/-- When nothing is left to visit, no flagged variable is outside. -/
theorem OutGo.closed {M : Nat → Prop} {u t : Pat} {nodes : List store.Node} {A : Nat → Option Nat}
    {todo : Nat} (h : OutGo nm M u t nodes A todo []) : ∀ y ∈ Sorts.outV u t, ¬ M y := by
  have key : ∀ (n : Nat) (q : Pat), q.size = n → (∃ k, Repr nm nodes k q ∧ A k ≠ none) →
      ∀ y ∈ Sorts.outV u q, ¬ M y := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rintro q rfl ⟨k, hk, hAk⟩ y hy
      obtain ⟨q', hq', -, hfo, hne, hvar, hargs⟩ := h.flag k hAk
      have := hq'.unique hk
      subst this
      by_cases hv : ∃ x, q' = .var x
      · obtain ⟨x, rfl⟩ := hv
        rw [Sorts.outV, ite_eq_right hne] at hy
        simp only [Sorts.outF, List.mem_singleton] at hy
        subst hy
        exact hvar y rfl
      · have hnv : ∀ v, q' ≠ .var v := fun v e => hv ⟨v, e⟩
        obtain ⟨a, ha, hya⟩ := (mem_outV_args hfo hnv hne).1 hy
        rcases hargs a ha with rfl | hfa | hps
        · rw [outV_self] at hya; cases hya
        · rcases unspine_mem q' [] a ha with hnil | ⟨-, hlt, -⟩
          · cases hnil
          · exact ih a.size hlt a rfl hfa y hya
        · cases hps
  intro y hy
  rcases h.root with rfl | hft | hps
  · rw [outV_self] at hy; cases hy
  · exact key _ t rfl hft y hy
  · cases hps

/-- The invariant of the loop. -/
def OutInv (nm : Option Nat → Sym) (M : Nat → Prop) (s0 : store.Store) (u t : Pat) (Bd : Nat)
    (x : store.Store × store.TermId × Bool × Bool) : Prop :=
  Inv x.1 ∧ Extends s0 x.1 ∧ tbl x.1 .B = tbl s0 .B ∧
    if x.2.2.2 = true then
      x.2.2.1 = false ∧ ∃ ps, OutGo nm M u t x.1.nodes.val (tbl x.1 .A) x.2.1.val ps ∧
        x.1.ticks.val + owedW nm x.1.nodes.val (tbl x.1 .A) t.subs outW + 3 * ps.length + 2 ≤ Bd
    else
      (x.2.2.1 = true ↔ ∃ y ∈ Sorts.outV u t, M y) ∧ x.1.ticks.val + 1 ≤ Bd

/-- What the loop leaves. -/
def OutPost (M : Nat → Prop) (s0 : store.Store) (u t : Pat) (Bd : Nat)
    (y : Bool × store.Store) : Prop :=
  Inv y.2 ∧ Extends s0 y.2 ∧ tbl y.2 .B = tbl s0 .B ∧
    (y.1 = true ↔ ∃ y' ∈ Sorts.outV u t, M y') ∧ y.2.ticks.val ≤ Bd

theorem marked_outside_body_spec (hnm : Function.Injective nm) (M : Nat → Prop)
    (s0 : store.Store) (u t : Pat) (Bd : Nat) (hB : 40 * Bd + 100 ≤ Usize.max)
    (ui : store.TermId) (hu : Repr nm s0.nodes.val ui.val u) {tn : Nat}
    (ht : Repr nm s0.nodes.val tn t)
    (hM : ∀ k y, Term.var y ∈ t.subs → Repr nm s0.nodes.val k (.var y) →
      (tbl s0 .B k ≠ none ↔ M y))
    (s : store.Store) (todo : store.TermId) (found go : Bool)
    (h : OutInv nm M s0 u t Bd (s, todo, found, go)) :
    sorts.marked_outside_loop.body ui s todo found go ⦃ r =>
      match r with
      | .done y => OutPost M s0 u t Bd y
      | .cont x => OutInv nm M s0 u t Bd x ∧ s.ticks.val < x.1.ticks.val ⦄ := by
  unfold sorts.marked_outside_loop.body
  delta core.option.Option.is_some
  obtain ⟨hI, hE, hTB, hrest⟩ := h
  cases go with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hrest ⊢
    simp only [WP.spec_ok]
    exact ⟨hI, hE, hTB, hrest.1, by have := hrest.2; show s.ticks.val ≤ Bd; omega⟩
  | true =>
    simp only [↓reduceIte] at hrest ⊢
    obtain ⟨rfl, ps, hG, hc⟩ := hrest
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
      refine ⟨⟨K1.inv, hE.trans hx1, by rw [K1.tbl, hTB], ?_⟩,
        by show s.ticks.val < s1.ticks.val; omega⟩
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact ⟨⟨False.elim, fun ⟨y, hy, hm⟩ => hG.closed y hy hm⟩, by omega⟩
    | cons q rest =>
      step with uncons_repr s todo hI.toWf (p := Term.app q (encList (nm none) rest)) hG.todo
        (by unfold Room; omega) as ⟨o, s1, hK0, hu0⟩
      have K1 : Kept s s1 1 := hK0.kept hI
      have ht1 := K1.ticks
      obtain ⟨qi, ri, rfl, rq, rrest⟩ := hu0
      simp only [List.length_cons] at hc
      obtain ⟨hqs, hqfo⟩ := hG.sub q List.mem_cons_self
      have hsubr : ∀ p ∈ rest, p ∈ t.subs ∧ p.firstOrder = true :=
        fun p hp => hG.sub p (List.mem_cons_of_mem _ hp)
      have houtr : ∀ p ∈ rest, ∀ y ∈ Sorts.outV u p, y ∈ Sorts.outV u t :=
        fun p hp => hG.out p (List.mem_cons_of_mem _ hp)
      simp only
      step with same_spec s1 qi ui K1.inv (by unfold Room; omega) as ⟨b, s2, hb, K2⟩
      have ht2 := K2.ticks
      have hn2 : s2.nodes.val = s.nodes.val := by rw [K2.nodes, K1.nodes]
      have htb2 : tbl s2 = tbl s := by rw [K2.tbl, K1.tbl]
      have hx2 : Extends s s2 := Extends.of_eq hn2 (by omega)
      by_cases e : qi.val = ui.val
      · -- an occurrence of the subterm: not entered
        have hb' : b = true := by simp [hb, e]
        subst hb'
        have hqu : q = u := by rw [e] at rq; exact rq.unique (hE.repr hu)
        simp only [↓reduceIte, bind_ok, uncurry, WP.spec_ok]
        refine ⟨⟨K2.inv, hE.trans hx2, by rw [htb2, hTB], ?_⟩,
          by show s.ticks.val < s2.ticks.val; omega⟩
        simp only [↓reduceIte, true_and]
        refine ⟨rest, ⟨by rw [hn2]; exact rrest, hsubr, houtr, ?_, ?_⟩, ?_⟩
        · intro k hk
          rw [htb2] at hk
          obtain ⟨q', hq', h1, h2, h3, h4, h5⟩ := hG.flag k hk
          refine ⟨q', by rw [hn2]; exact hq', h1, h2, h3, h4, fun a ha => ?_⟩
          rw [hn2, htb2]
          rcases h5 a ha with h | h | h
          · exact .inl h
          · exact .inr (.inl h)
          · rcases List.mem_cons.1 h with rfl | h
            · exact .inl hqu
            · exact .inr (.inr h)
        · rw [hn2, htb2]
          rcases hG.root with h | h | h
          · exact .inl h
          · exact .inr (.inl h)
          · rcases List.mem_cons.1 h with rfl | h
            · exact .inl hqu
            · exact .inr (.inr h)
        · rw [hn2, htb2]; omega
      · have hb' : b = false := by simp [hb, e]
        subst hb'
        have hqu : q ≠ u := by
          rintro rfl
          exact e (Repr.inj hnm hN rq (hE.repr hu))
        simp only [Bool.false_eq_true, ↓reduceIte]
        step with get_flag_spec s2 .A qi K2.inv (by rw [hn2]; exact rq.lt)
          (by unfold Room; omega) as ⟨r1, ho1, K3⟩
        obtain ⟨o1, s3⟩ := r1
        simp only at ho1
        simp only at K3
        rw [htb2] at ho1
        have ht3 := K3.ticks
        have hn3 : s3.nodes.val = s.nodes.val := by rw [K3.nodes, hn2]
        have htb3 : tbl s3 = tbl s := by rw [K3.tbl, htb2]
        have hx3 : Extends s s3 := Extends.of_eq hn3 (by omega)
        cases hfl : tbl s .A qi.val with
        | some fl =>
          -- visited before
          rw [hfl] at ho1
          subst ho1
          simp only [Option.map_some, uncurry]
          simp only [bind_ok, Option.isSome_some]
          simp only [uncurry, ↓reduceIte, WP.spec_ok]
          have hfq : ∃ k', Repr nm s.nodes.val k' q ∧ tbl s .A k' ≠ none :=
            ⟨qi.val, rq, by rw [hfl]; simp⟩
          refine ⟨⟨K3.inv, hE.trans hx3, by rw [htb3, hTB], ?_⟩,
            by show s.ticks.val < s3.ticks.val; omega⟩
          simp only [↓reduceIte, true_and]
          refine ⟨rest, ⟨by rw [hn3]; exact rrest, hsubr, houtr, ?_, ?_⟩, ?_⟩
          · intro k hk
            rw [htb3] at hk
            obtain ⟨q', hq', h1, h2, h3, h4, h5⟩ := hG.flag k hk
            refine ⟨q', by rw [hn3]; exact hq', h1, h2, h3, h4, fun a ha => ?_⟩
            rw [hn3, htb3]
            rcases h5 a ha with h | h | h
            · exact .inl h
            · exact .inr (.inl h)
            · rcases List.mem_cons.1 h with rfl | h
              · exact .inr (.inl hfq)
              · exact .inr (.inr h)
          · rw [hn3, htb3]
            rcases hG.root with h | h | h
            · exact .inl h
            · exact .inr (.inl h)
            · rcases List.mem_cons.1 h with rfl | h
              · exact .inr (.inl hfq)
              · exact .inr (.inr h)
          · rw [hn3, htb3]; omega
        | none =>
          rw [hfl] at ho1
          subst ho1
          simp only [Option.map_none, uncurry]
          simp only [bind_ok, Option.isSome_none]
          simp only [uncurry, Bool.false_eq_true, ↓reduceIte]
          step with set_flag_spec s3 .A qi true K3.inv (by rw [hn3]; exact rq.lt)
            (by unfold Room; omega) as ⟨s4, n4, t4, hI4, tb4, tbo4⟩
          rw [htb3] at tb4
          simp only [↓reduceIte] at tb4
          have hn4 : s4.nodes.val = s.nodes.val := by rw [n4, hn3]
          have hB4 : tbl s4 .B = tbl s0 .B := by rw [tbo4 .B (by simp), htb3, hTB]
          have hmono := update_ne_none (B := tbl s .A) (q := qi.val) (r := 1)
          have hfq' : Function.update (tbl s .A) qi.val (some 1) qi.val ≠ none := by simp
          step with is_var_w s4 qi hI4.toWf (by rw [hn4]; exact rq) (by unfold Room; omega)
            as ⟨b1, s5, hb1, hK5⟩
          have K5 : Kept s4 s5 1 := hK5.kept hI4
          have ht5 := K5.ticks
          have hn5 : s5.nodes.val = s.nodes.val := by rw [K5.nodes, hn4]
          have hA5 : tbl s5 .A = Function.update (tbl s .A) qi.val (some 1) := by
            rw [K5.tbl, tb4]
          have hB5 : tbl s5 .B = tbl s0 .B := by rw [K5.tbl, hB4]
          -- what holds of the terms flagged before, with the new flag
          have hold : ∀ (nodes' : List store.Node) (ps' : List Pat),
              (∀ k p, Repr nm s.nodes.val k p → Repr nm nodes' k p) →
              (∀ a ∈ rest, a ∈ ps') → ∀ k, k ≠ qi.val → tbl s .A k ≠ none →
              ∃ q', Repr nm nodes' k q' ∧ q' ∈ t.subs ∧ q'.firstOrder = true ∧ q' ≠ u ∧
                (∀ x, q' = .var x → ¬ M x) ∧
                ∀ a ∈ (unspine q' []).2, a = u ∨
                  (∃ k', Repr nm nodes' k' a ∧
                    Function.update (tbl s .A) qi.val (some 1) k' ≠ none) ∨ a ∈ ps' := by
            intro nodes' ps' hrep hps k _ hk
            obtain ⟨q', hq', h1, h2, h3, h4, h5⟩ := hG.flag k hk
            refine ⟨q', hrep _ _ hq', h1, h2, h3, h4, fun a ha => ?_⟩
            rcases h5 a ha with h | ⟨k', hk', hfk'⟩ | h
            · exact .inl h
            · exact .inr (.inl ⟨k', hrep _ _ hk', hmono k' hfk'⟩)
            · rcases List.mem_cons.1 h with rfl | h
              · exact .inr (.inl ⟨qi.val, hrep _ _ rq, hfq'⟩)
              · exact .inr (.inr (hps a h))
          have hroot : ∀ (nodes' : List store.Node) (ps' : List Pat),
              (∀ k p, Repr nm s.nodes.val k p → Repr nm nodes' k p) →
              (∀ a ∈ rest, a ∈ ps') →
              t = u ∨ (∃ k', Repr nm nodes' k' t ∧
                Function.update (tbl s .A) qi.val (some 1) k' ≠ none) ∨ t ∈ ps' := by
            intro nodes' ps' hrep hps
            rcases hG.root with h | ⟨k', hk', hfk'⟩ | h
            · exact .inl h
            · exact .inr (.inl ⟨k', hrep _ _ hk', hmono k' hfk'⟩)
            · rcases List.mem_cons.1 h with rfl | h
              · exact .inr (.inl ⟨qi.val, hrep _ _ rq, hfq'⟩)
              · exact .inr (.inr (hps t h))
          have hw : owedW nm s.nodes.val (Function.update (tbl s .A) qi.val (some 1)) t.subs
              outW + outW q ≤ owedW nm s.nodes.val (tbl s .A) t.subs outW := by
            have := owedW_set hnm (more := []) hN rq hfl hqs hfq' hmono outW
            rwa [List.append_nil] at this
          unfold outW at hw hc
          by_cases hv : ∃ x, q = .var x
          · have hb1' : b1 = true := hb1.2 hv
            subst hb1'
            obtain ⟨x, rfl⟩ := hv
            simp only [↓reduceIte]
            step with get_flag_spec s5 .B qi K5.inv (by rw [hn5]; exact rq.lt)
              (by unfold Room; omega) as ⟨o2, s6, ho2, K6⟩
            have ht6 := K6.ticks
            have hn6 : s6.nodes.val = s.nodes.val := by rw [K6.nodes, hn5]
            have hx6 : Extends s s6 := Extends.of_eq hn6 (by omega)
            have hMx : tbl s5 .B qi.val ≠ none ↔ M x := by
              obtain ⟨k0, hk0⟩ := ht.of_subs hqs
              have := Repr.inj hnm hN (hE.repr hk0) rq
              subst this
              rw [hB5]
              exact hM _ x hqs hk0
            have hxo : x ∈ Sorts.outV u (.var x) := by
              rw [Sorts.outV, ite_eq_right hqu]; simp [Sorts.outF]
            cases hfb : tbl s5 .B qi.val with
            | some fl =>
              rw [hfb] at ho2
              subst ho2
              simp only [Option.map_some, Option.isSome_some, ↓reduceIte, WP.spec_ok]
              refine ⟨⟨K6.inv, hE.trans hx6, by rw [K6.tbl, hB5], ?_⟩,
                by show s.ticks.val < s6.ticks.val; omega⟩
              simp only [Bool.false_eq_true, ↓reduceIte, true_iff]
              exact ⟨⟨x, hG.out _ List.mem_cons_self x hxo, hMx.1 (by rw [hfb]; simp)⟩, by omega⟩
            | none =>
              rw [hfb] at ho2
              subst ho2
              simp only [Option.map_none, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
                WP.spec_ok]
              have hnM : ¬ M x := fun hm => hMx.2 hm hfb
              refine ⟨⟨K6.inv, hE.trans hx6, by rw [K6.tbl, hB5], ?_⟩,
                by show s.ticks.val < s6.ticks.val; omega⟩
              simp only [↓reduceIte, true_and]
              have hA6 : tbl s6 .A = Function.update (tbl s .A) qi.val (some 1) := by
                rw [K6.tbl, hA5]
              refine ⟨rest, ⟨by rw [hn6]; exact rrest, hsubr, houtr, ?_, ?_⟩, ?_⟩
              · intro k hk
                rw [hA6] at hk
                rw [hn6, hA6]
                by_cases ek : k = qi.val
                · subst ek
                  refine ⟨_, rq, hqs, hqfo, hqu, ?_, ?_⟩
                  · intro x' hx'
                    cases hx'
                    exact hnM
                  · intro a ha
                    simp [unspine] at ha
                · rw [Function.update_of_ne ek] at hk
                  exact hold _ rest (fun _ _ h => h) (fun _ h => h) k ek hk
              · rw [hn6, hA6]
                exact hroot _ rest (fun _ _ h => h) (fun _ h => h)
              · rw [hn6, hA6]
                unfold outW
                omega
          · have hb1' : b1 = false := by
              cases b1 with
              | false => rfl
              | true => exact absurd (hb1.1 rfl) hv
            subst hb1'
            have hnv : ∀ v, q ≠ .var v := fun v e' => hv ⟨v, e'⟩
            simp only [Bool.false_eq_true, ↓reduceIte]
            have hlen := unspine_length q []
            simp only [List.length_nil, Nat.add_zero] at hlen
            step with spine_spec s5 qi K5.inv.toWf (by rw [hn5]; exact rq) (by unfold Room; omega)
              as ⟨x6, s6, hR6, _, rargs⟩
            obtain ⟨head, args⟩ := x6
            simp only at rargs ⊢
            have ht6 := hR6.ticks
            have hI6 : Inv s6 := ⟨hR6.wf, by rw [hR6.stk]; exact K5.inv.empty⟩
            have hx5 : Extends s s5 := Extends.of_eq hn5 (by omega)
            have hx6 : Extends s s6 := hx5.trans hR6.ext
            step with append_keep_spec (unspine q []).2 s6 args ri hI6 rargs (hx6.repr rrest)
              (by rw [hlen]; unfold Room; omega) as ⟨todo1, s7, hI7, hx7, rtodo, ht7, htb7⟩
            rw [hlen] at ht7
            have h56 : s5.ticks.val ≤ s6.ticks.val := by
              obtain ⟨m, -, h⟩ := hR6.ext
              omega
            have h67 : s6.ticks.val ≤ s7.ticks.val := by
              obtain ⟨m, -, h⟩ := hx7
              omega
            have hx7' : Extends s s7 := hx6.trans hx7
            have hA7 : tbl s7 .A = Function.update (tbl s .A) qi.val (some 1) := by
              rw [htb7, hR6.tbl, hA5]
            have hB7 : tbl s7 .B = tbl s0 .B := by rw [htb7, hR6.tbl, hB5]
            refine ⟨⟨hI7, hE.trans hx7', hB7, ?_⟩, by show s.ticks.val < s7.ticks.val; omega⟩
            simp only [↓reduceIte, true_and]
            refine ⟨(unspine q []).2 ++ rest, ⟨rtodo, ?_, ?_, ?_, ?_⟩, ?_⟩
            · intro p hp
              rcases List.mem_append.1 hp with hp | hp
              · rcases unspine_mem q [] p hp with hnil | ⟨h1, -, h3⟩
                · cases hnil
                · exact ⟨Term.subs_trans hqs h1, h3 hqfo⟩
              · exact hsubr p hp
            · intro p hp y hy
              rcases List.mem_append.1 hp with hp | hp
              · exact hG.out q List.mem_cons_self y
                  ((mem_outV_args hqfo hnv hqu).2 ⟨p, hp, hy⟩)
              · exact houtr p hp y hy
            · intro k hk
              rw [hA7] at hk
              rw [hA7]
              by_cases ek : k = qi.val
              · subst ek
                exact ⟨_, hx7'.repr rq, hqs, hqfo, hqu, fun x hx => absurd hx (hnv x),
                  fun a ha => .inr (.inr (List.mem_append_left _ ha))⟩
              · rw [Function.update_of_ne ek] at hk
                exact hold _ _ (fun _ _ h => hx7'.repr h)
                  (fun _ h => List.mem_append_right _ h) k ek hk
            · rw [hA7]
              exact hroot _ _ (fun _ _ h => hx7'.repr h) (fun _ h => List.mem_append_right _ h)
            · obtain ⟨more, hmore, -⟩ := hx7'
              have := owedW_mono (nm := nm) (nodes := s.nodes.val) (more := more)
                (A := Function.update (tbl s .A) qi.val (some 1))
                (A' := Function.update (tbl s .A) qi.val (some 1)) (S := t.subs)
                (fun _ h => h) outW
              unfold outW at this ⊢
              rw [hmore, hA7]
              simp only [List.length_append, hlen]
              omega

/-- The ticks `marked_outside` may take. -/
def markedCost (t : Pat) : Nat := (t.subs.sum outW) + 9

/-- `marked_outside` answers whether a flagged variable is at a place of the
term outside the occurrences of the subterm. `M` says which variables table
`B` flags; the table is left as it was. -/
theorem marked_outside_spec (hnm : Function.Injective nm) (M : Nat → Prop) (s : store.Store)
    (u t : store.TermId) {up tp : Pat} (hI : Inv s) (hu : Repr nm s.nodes.val u.val up)
    (ht : Repr nm s.nodes.val t.val tp) (hfo : tp.firstOrder = true)
    (hM : ∀ k y, Repr nm s.nodes.val k (.var y) → (tbl s .B k ≠ none ↔ M y))
    (hroom : Room s (markedCost tp)) :
    sorts.marked_outside s u t ⦃ b s' =>
      Inv s' ∧ Extends s s' ∧ tbl s' .B = tbl s .B ∧
        (b = true ↔ ∃ y ∈ Sorts.outV up tp, M y) ∧
        s'.ticks.val ≤ s.ticks.val + markedCost tp ⦄ := by
  unfold sorts.marked_outside sorts.marked_outside_loop
  have hroom' := hroom
  unfold Room at hroom'
  unfold markedCost at hroom'
  step with alloc_spec s .Nil hI trivial (by unfold Room; omega)
    as ⟨nil, s1, hI1, ht1, htb1, hx1, hr1⟩
  simp only [norm] at hr1
  step with clear_spec s1 .A hI1 (by unfold Room; omega) as ⟨s2, n2, t2, hI2, tb2, tbo2⟩
  have hx2 : Extends s s2 := hx1.trans (Extends.of_eq n2 (by omega))
  have ht2 : Repr nm s2.nodes.val t.val tp := hx2.repr ht
  step with alloc_spec s2 (.App t nil) hI2
    ⟨ht2.lt, by rw [n2]; exact (List.getElem?_eq_some_iff.1 hr1).1⟩ (by unfold Room; omega)
    as ⟨todo, s3, hI3, ht3, htb3, hx3, htd⟩
  simp only [norm] at htd
  have hx03 : Extends s s3 := hx2.trans hx3
  have hB3 : tbl s3 .B = tbl s .B := by rw [htb3, tbo2 .B (by simp), htb1]
  have hA3 : ∀ k, tbl s3 .A k = none := by rw [htb3]; exact tb2
  let Bd := s.ticks.val + markedCost tp
  have hM3 : ∀ k y, Term.var y ∈ tp.subs → Repr nm s3.nodes.val k (.var y) →
      (tbl s3 .B k ≠ none ↔ M y) := by
    intro k y hy hk
    obtain ⟨k1, hk1⟩ := ht.of_subs hy
    have := Repr.inj hnm hI3.nodesOK (hx03.repr hk1) hk
    subst this
    rw [hB3]
    exact hM _ y hk1
  have hnil : Repr nm s3.nodes.val nil.val (encList (nm none) []) :=
    hx3.repr (by rw [n2]; exact .nil hr1)
  have hsum := owedW_le_sum (nm := nm) s3.nodes.val (tbl s3 .A) tp.subs outW
  have hloop := loop.spec_decr_nat
    (fun x : store.Store × store.TermId × Bool × Bool => Bd + 1 - x.1.ticks.val)
    (fun x => OutInv nm M s3 up tp Bd x)
    (fun y : Bool × store.Store => OutPost M s3 up tp Bd y)
    (fun x : store.Store × store.TermId × Bool × Bool =>
      sorts.marked_outside_loop.body u x.1 x.2.1 x.2.2.1 x.2.2.2) (s3, todo, false, true)
    (by
      rintro ⟨y, td, fd, go⟩ hinv
      refine WP.spec_mono (marked_outside_body_spec hnm M s3 up tp Bd
        (by unfold Bd markedCost; omega) u (hx03.repr hu) (hx03.repr ht) hM3 y td fd go hinv) ?_
      intro r hr
      cases r with
      | done z => exact hr
      | cont x' =>
        obtain ⟨h1, h2⟩ := hr
        refine ⟨h1, ?_⟩
        obtain ⟨-, -, -, h3⟩ := h1
        have : x'.1.ticks.val + 1 ≤ Bd := by
          split at h3
          · obtain ⟨-, p, -, hc⟩ := h3; omega
          · exact h3.2
        simp only at h2 ⊢
        omega)
    ⟨hI3, Extends.refl s3, rfl, by
      simp only [↓reduceIte, true_and]
      refine ⟨[tp], ⟨.app htd (hx3.repr ht2) hnil, ?_, ?_, ?_, .inr (.inr (by simp))⟩, ?_⟩
      · intro p hp
        simp only [List.mem_singleton] at hp
        subst hp
        exact ⟨Term.self_mem_subs p, hfo⟩
      · intro p hp y hy
        simp only [List.mem_singleton] at hp
        subst hp
        exact hy
      · intro k hk; exact absurd (hA3 k) hk
      · simp only [List.length_singleton]
        unfold Bd markedCost
        omega⟩
  refine WP.spec_mono hloop ?_
  rintro ⟨b, s'⟩ ⟨hI', hx', hB', hb, ht'⟩
  exact ⟨hI', hx03.trans hx', by rw [hB', hB3], hb, ht'⟩

end RwLogVerified
