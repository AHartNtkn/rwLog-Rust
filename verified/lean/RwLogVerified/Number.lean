/-
# Numbering the variables of a store, on the store

`sorts::conj_at` is the conjunction an entry list gives a variable
(`conjOf`). `sorts::uppers` is the conjunction of every sort that holds of
all members of a conjunction but some ground terms (`Sorts.Hold`).
`sorts::firsts` lists the variables of a pattern in the order they first
occur (`Sorts.firsts`). `sorts::renumber` renames the pattern and the
exclusions of a store by these places and gives each variable the sorts
that hold of all its values: what `Sorts.ofTight` assembles the normal
store from (`ofTight_abs`).
-/
import RwLogVerified.Tight
import RwLog.Sorts.Norm

open Aeneas Aeneas.Std Result

namespace RwLogVerified

open rwlog_core RwLog

variable {nm : Option Nat → RwLog.Sym}

/-! ## The conjunction of a variable among the entries -/

theorem cpat_empty (z : Sym) (U : List Name) : cpat z U ∅ = namesPat z [] := by
  unfold cpat
  congr 1
  induction U with
  | nil => exact conjList_nil _
  | cons x U ih => rw [conjList_cons_neg (by simp)]; exact ih

theorem conj_at_loop_spec {U : List Name} (v : store.TermId) (x : Nat) :
    ∀ (L : List (Nat × Sorts.Conj)) (s : store.Store) (c es : store.TermId),
    Inv s → VarAt s.nodes.val v.val x → Repr nm s.nodes.val es.val (encVarEntries nm U L) →
    Repr nm s.nodes.val c.val (cpat (nm none) U ∅) → Room s (3 * L.length + 1) →
    sorts.conj_at_loop s v c es true ⦃ r s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + 3 * L.length + 1 ∧
        Repr nm s'.nodes.val r.val (cpat (nm none) U (conjOf L x)) ⦄ := by
  intro L
  induction L with
  | nil =>
    intro s c es hI hv hes hc hroom
    have hroom' := hroom
    unfold Room at hroom'
    unfold sorts.conj_at_loop
    rw [loop]
    simp only [sorts.conj_at_loop.body, ↓reduceIte]
    step with uncons_repr s es hI.toWf (p := Term.sym (nm none)) hes (by unfold Room; omega)
      as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    subst hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    have hx1 : Extends s s1 := Extends.of_eq K1.nodes (by omega)
    simp only [uncurry, bind_ok]
    rw [loop]
    simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, WP.spec_ok]
    exact ⟨K1.inv, hx1, by simp only [List.length_nil]; omega, hx1.repr hc⟩
  | cons en L ih =>
    intro s c es hI hv hes hc hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons] at hroom'
    unfold sorts.conj_at_loop
    rw [loop]
    simp only [sorts.conj_at_loop.body, ↓reduceIte]
    step with uncons_repr s es hI.toWf (p := Term.app (varEntry nm U en) (encVarEntries nm U L))
      hes (by unfold Room; omega) as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    obtain ⟨e, rest, rfl, re, rrest⟩ := hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    have hx1 : Extends s s1 := Extends.of_eq K1.nodes (by omega)
    step with uncons_repr s1 e K1.inv.toWf
      (p := Term.app (Term.var en.1) (cpat (nm none) U en.2)) (hx1.repr re)
      (by unfold Room; omega) as ⟨r1, hK1', hu1⟩
    obtain ⟨o1, s2⟩ := r1
    simp only at hu1
    simp only at hK1'
    obtain ⟨vi, ci, rfl, rv, rc⟩ := hu1
    have K2 := hK1'.kept K1.inv
    have ht2 := K2.ticks
    have hx2 : Extends s s2 := hx1.trans (Extends.of_eq K2.nodes (by omega))
    have hvv : VarAt s2.nodes.val vi.val en.1 := by
      rw [K2.nodes]
      cases rv with
      | var h => exact h
    step with same_spec s2 vi v K2.inv (by unfold Room; omega) as ⟨r2, hb, hK2⟩
    obtain ⟨b, s3⟩ := r2
    simp only at hb hK2
    have K3 := hK2
    have ht3 := K3.ticks
    have hx3 : Extends s s3 := hx2.trans (Extends.of_eq K3.nodes (by omega))
    subst hb
    by_cases hq : vi.val = v.val
    · have hxe : en.1 = x := by
        rw [hq] at hvv
        exact hvv.unique (hx2.varAt hv)
      simp only [hq, decide_true, ↓reduceIte, uncurry, bind_ok]
      rw [loop]
      simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, WP.spec_ok]
      refine ⟨K3.inv, hx3, by simp only [List.length_cons]; omega, ?_⟩
      rw [conjOf_cons, ite_pos' hxe.symm, K3.nodes, K2.nodes]
      exact rc
    · have hxe : x ≠ en.1 := by
        rintro rfl
        exact hq (hvv.inj K2.inv.nodesOK (hx2.varAt hv))
      simp only [hq, decide_false, Bool.false_eq_true, ↓reduceIte, uncurry, bind_ok]
      have IH := ih s3 c rest K3.inv (hx3.varAt hv) (hx3.repr rrest) (hx3.repr hc)
        (by unfold Room; omega)
      unfold sorts.conj_at_loop at IH
      refine WP.spec_mono IH ?_
      rintro ⟨r, s'⟩ ⟨hI', hx', ht', hr'⟩
      refine ⟨hI', hx3.trans hx', by simp only [List.length_cons]; omega, ?_⟩
      rw [conjOf_cons, ite_neg' hxe]
      exact hr'

/-- `conj_at` is the conjunction the entries give the variable. -/
theorem conj_at_spec {U : List Name} (s : store.Store) (es v : store.TermId) {x : Nat}
    (L : List (Nat × Sorts.Conj)) (hI : Inv s) (hv : VarAt s.nodes.val v.val x)
    (hes : Repr nm s.nodes.val es.val (encVarEntries nm U L)) (hroom : Room s (3 * L.length + 2)) :
    sorts.conj_at s es v ⦃ r s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + 3 * L.length + 2 ∧
        Repr nm s'.nodes.val r.val (cpat (nm none) U (conjOf L x)) ⦄ := by
  unfold sorts.conj_at
  have hroom' := hroom
  unfold Room at hroom'
  step with alloc_spec s .Nil hI trivial (by unfold Room; omega)
    as ⟨c, s1, hI1, ht1, htb1, hx1, hr1⟩
  have rc : Repr nm s1.nodes.val c.val (cpat (nm none) U ∅) := by
    rw [cpat_empty]; exact .nil hr1
  refine WP.spec_mono (conj_at_loop_spec v x L s1 c es hI1 (hx1.varAt hv) (hx1.repr hes) rc
    (by unfold Room; omega)) ?_
  rintro ⟨r, s'⟩ ⟨hI', hx', ht', hr'⟩
  exact ⟨hI', hx1.trans hx', by omega, hr'⟩

/-! ## The sorts that hold of all members but some -/

/-- The ticks the loop of `uppers` may take over `n` names, when one test
takes `K`. -/
def uppersLoopCost (K : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => K + 2 + uppersLoopCost K n

theorem uppers_loop_spec {S : Sorts} {sp : Pat} {U : List Name} (hC : Ctx nm S sp U)
    (hS : S.WellFormed) {r q : Nat} (hr : ∀ d, (Sorts.reachSet S d).card ≤ r)
    (hq : ∀ d m, (Sorts.reachGSet S (d, some m)).card ≤ q)
    (c : Sorts.Conj) (G : List GTerm) (hc : Sub U c) (decls names ci g : store.TermId) :
    ∀ (ns : List Name) (s : store.Store) (nsi out : store.TermId) (acc : List Name),
    Inv s → Repr nm s.nodes.val decls.val sp →
    Repr nm s.nodes.val names.val (namesPat (nm none) U) →
    Repr nm s.nodes.val ci.val (cpat (nm none) U c) →
    Repr nm s.nodes.val g.val (encList (nm none) (G.map GTerm.toPat)) →
    Repr nm s.nodes.val nsi.val (namesPat (nm none) ns) → (∀ n ∈ ns, n ∈ Sorts.names S) →
    Repr nm s.nodes.val out.val (namesPat (nm none) acc) →
    Room s (uppersLoopCost (inclButAll S U.length r q (Sorts.sumSize G)) ns.length) →
    sorts.uppers_loop nsi s decls names ci g out ⦃ res s' =>
      Inv s' ∧ Extends s s' ∧
        s'.ticks.val ≤ s.ticks.val +
          uppersLoopCost (inclButAll S U.length r q (Sorts.sumSize G)) ns.length ∧
        Repr nm s'.nodes.val res.val
          (namesPat (nm none) (conjList ns (fun n => Sorts.Hold S c n G) ++ acc)) ⦄ := by
  intro ns
  induction ns with
  | nil =>
    intro s nsi out acc hI hde hU hci hg hns hsub ho hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_nil, uppersLoopCost] at hroom'
    unfold sorts.uppers_loop
    rw [loop]
    simp only [sorts.uppers_loop.body]
    step with uncons_repr s nsi hI.toWf (p := Term.sym (nm none)) hns (by unfold Room; omega)
      as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    subst hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    have hx1 : Extends s s1 := Extends.of_eq K1.nodes (by omega)
    have hfin : Inv s1 ∧ Extends s s1 ∧
        s1.ticks.val ≤ s.ticks.val +
          uppersLoopCost (inclButAll S U.length r q (Sorts.sumSize G)) ([] : List Name).length ∧
        Repr nm s1.nodes.val out.val
          (namesPat (nm none) (conjList [] (fun n => Sorts.Hold S c n G) ++ acc)) := by
      refine ⟨K1.inv, hx1, by simp only [List.length_nil, uppersLoopCost]; omega, ?_⟩
      rw [conjList_nil, List.nil_append]
      exact hx1.repr ho
    step*
  | cons n ns ih =>
    intro s nsi out acc hI hde hU hci hg hns hsub ho hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons, uppersLoopCost] at hroom'
    unfold sorts.uppers_loop
    rw [loop]
    simp only [sorts.uppers_loop.body]
    step with uncons_repr s nsi hI.toWf
      (p := Term.app (Term.sym n) (namesPat (nm none) ns)) hns (by unfold Room; omega)
      as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    obtain ⟨ni, rest, rfl, rn, rrest⟩ := hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    have hx1 : Extends s s1 := Extends.of_eq K1.nodes (by omega)
    have hnS : n ∈ Sorts.names S := hsub n List.mem_cons_self
    step with included_but_spec hC hS hr hq c n G hc (hC.nz n hnS) s1 decls names ci ni g K1.inv
      (hx1.repr hde) (hx1.repr hU) (hx1.repr hci) (hx1.repr rn) (hx1.repr hg)
      (by unfold Room; omega) as ⟨r2, hI2, hx2, ht2, hb⟩
    obtain ⟨b, s2⟩ := r2
    simp only at hI2 hx2 ht2 hb
    have hx02 := hx1.trans hx2
    have hsub' : ∀ m ∈ ns, m ∈ Sorts.names S := fun m hm => hsub m (List.mem_cons_of_mem _ hm)
    cases b with
    | true =>
      have hH : Sorts.Hold S c n G := hb.1 rfl
      simp only [uncurry, ↓reduceIte]
      step with alloc_spec s2 (.App ni out) hI2 ⟨(hx02.repr rn).lt, (hx02.repr ho).lt⟩
        (by unfold Room; omega) as ⟨r3, hI3, ht3, htb3, hx3, hr3⟩
      obtain ⟨out1, s3⟩ := r3
      simp only [norm] at hI3 ht3 htb3 hx3 hr3
      simp only [uncurry, bind_ok]
      have hx03 := hx02.trans hx3
      have ro : Repr nm s3.nodes.val out1.val (namesPat (nm none) (n :: acc)) :=
        .app hr3 (hx03.repr rn) (hx03.repr ho)
      have IH := ih s3 rest out1 (n :: acc) hI3 (hx03.repr hde) (hx03.repr hU) (hx03.repr hci)
        (hx03.repr hg) (hx03.repr rrest) hsub' ro (by unfold Room; omega)
      unfold sorts.uppers_loop at IH
      refine WP.spec_mono IH ?_
      rintro ⟨res, s'⟩ ⟨hI', hx', ht', hr'⟩
      refine ⟨hI', hx03.trans hx', by simp only [List.length_cons, uppersLoopCost]; omega, ?_⟩
      rw [conjList_cons_pos hH, List.append_assoc]
      exact hr'
    | false =>
      have hH : ¬ Sorts.Hold S c n G := fun h => by simpa using hb.2 h
      simp only [Bool.false_eq_true, ↓reduceIte, uncurry, bind_ok]
      have IH := ih s2 rest out acc hI2 (hx02.repr hde) (hx02.repr hU) (hx02.repr hci)
        (hx02.repr hg) (hx02.repr rrest) hsub' (hx02.repr ho) (by unfold Room; omega)
      unfold sorts.uppers_loop at IH
      refine WP.spec_mono IH ?_
      rintro ⟨res, s'⟩ ⟨hI', hx', ht', hr'⟩
      refine ⟨hI', hx02.trans hx', by simp only [List.length_cons, uppersLoopCost]; omega, ?_⟩
      rw [conjList_cons_neg hH]
      exact hr'

/-- The ticks `uppers` may take. -/
def uppersCost (S : Sorts) (u r q N : Nat) : Nat :=
  uppersLoopCost (inclButAll S u r q N) u + 1

/-- `uppers` is the conjunction of the sorts that every member of the
conjunction, but for the ground terms of the list, is in. -/
theorem uppers_spec {S : Sorts} {sp : Pat} {U : List Name} (hC : Ctx nm S sp U)
    (hS : S.WellFormed) (hUS : ∀ n ∈ U, n ∈ Sorts.names S) {r q : Nat}
    (hr : ∀ d, (Sorts.reachSet S d).card ≤ r)
    (hq : ∀ d m, (Sorts.reachGSet S (d, some m)).card ≤ q)
    (c c' : Sorts.Conj) (G : List GTerm) (hc : Sub U c)
    (hc' : ∀ n ∈ U, n ∈ c' ↔ Sorts.Hold S c n G)
    (s : store.Store) (decls names ci g : store.TermId) (hI : Inv s)
    (hde : Repr nm s.nodes.val decls.val sp)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (hci : Repr nm s.nodes.val ci.val (cpat (nm none) U c))
    (hg : Repr nm s.nodes.val g.val (encList (nm none) (G.map GTerm.toPat)))
    (hroom : Room s (uppersCost S U.length r q (Sorts.sumSize G))) :
    sorts.uppers s decls names ci g ⦃ res s' =>
      Inv s' ∧ Extends s s' ∧
        s'.ticks.val ≤ s.ticks.val + uppersCost S U.length r q (Sorts.sumSize G) ∧
        Repr nm s'.nodes.val res.val (cpat (nm none) U c') ⦄ := by
  unfold sorts.uppers
  have hroom' := hroom
  unfold Room at hroom'
  simp only [uppersCost] at hroom'
  step with alloc_spec s .Nil hI trivial (by unfold Room; omega)
    as ⟨out, s1, hI1, ht1, htb1, hx1, hr1⟩
  have ro : Repr nm s1.nodes.val out.val (namesPat (nm none) []) := .nil hr1
  refine WP.spec_mono (uppers_loop_spec hC hS hr hq c G hc decls names ci g U s1 names out []
    hI1 (hx1.repr hde) (hx1.repr hU) (hx1.repr hci) (hx1.repr hg) (hx1.repr hU) hUS ro
    (by unfold Room; omega)) ?_
  rintro ⟨res, s'⟩ ⟨hI', hx', ht', hr'⟩
  refine ⟨hI', hx1.trans hx', by simp only [uppersCost]; omega, ?_⟩
  rw [List.append_nil] at hr'
  unfold cpat
  rw [conjList_congr hc']
  exact hr'

/-! ## The variables of a term in the order they first occur -/

theorem firsts_append (A R : List Nat) :
    Sorts.firsts (A ++ R) =
      R.foldl (fun F x => if x ∈ F then F else F ++ [x]) (Sorts.firsts A) := by
  simp [Sorts.firsts, List.foldl_append]

theorem firsts_absorb {A M : List Nat} (h : ∀ v ∈ M, v ∈ A) :
    Sorts.firsts (A ++ M) = Sorts.firsts A := by
  induction M using List.reverseRecOn with
  | nil => simp
  | append_singleton M x ih =>
    rw [← List.append_assoc, Sorts.firsts_snoc, ih fun v hv => h v (by simp [hv])]
    exact ite_pos' (((Sorts.firsts_spec A).2.1 x).2 (h x (by simp))) _ _

/-- Variables that occurred already do not change the list. -/
theorem firsts_drop {A M : List Nat} (R : List Nat) (h : ∀ v ∈ M, v ∈ A) :
    Sorts.firsts (A ++ (M ++ R)) = Sorts.firsts (A ++ R) := by
  rw [← List.append_assoc, firsts_append, firsts_absorb h, ← firsts_append]

theorem firsts_fix_snoc {A : List Nat} {x : Nat} (h : Sorts.firsts A = A) (hx : x ∉ A) :
    Sorts.firsts (A ++ [x]) = A ++ [x] := by
  rw [Sorts.firsts_snoc, h, ite_neg' hx]

/-- The variable `v` of the term `t` has been listed, or is in a term of the
stack that is smaller than `t` and has only terms smaller than `t` above
it. -/
def Cov (acc : List Nat) (ps : List Pat) (t : Pat) (v : Nat) : Prop :=
  v ∈ acc ∨ ∃ pre c post, ps = pre ++ c :: post ∧ v ∈ c.vars ∧ c.size < t.size ∧
    ∀ d ∈ pre, d.size < t.size

theorem Cov.pop {acc acc' : List Nat} {ps : List Pat} {c0 t : Pat} {v : Nat}
    (h : Cov acc (c0 :: ps) t v) (hsub : ∀ w ∈ acc, w ∈ acc') (hc : ∀ w ∈ c0.vars, w ∈ acc') :
    Cov acc' ps t v := by
  rcases h with h | ⟨pre, c, post, e, hv, hc', hpre⟩
  · exact .inl (hsub v h)
  · cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact .inl (hc v hv)
    | cons d pre =>
      simp only [List.cons_append, List.cons.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact .inr ⟨pre, c, post, rfl, hv, hc', fun d' hd' => hpre d' (List.mem_cons_of_mem _ hd')⟩

theorem Cov.app {acc : List Nat} {ps : List Pat} {a b t : Pat} {v : Nat}
    (h : Cov acc (Term.app a b :: ps) t v) : Cov acc (a :: b :: ps) t v := by
  rcases h with h | ⟨pre, c, post, e, hv, hc', hpre⟩
  · exact .inl h
  · cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      simp only [Term.size] at hc'
      simp only [Term.vars, List.mem_append] at hv
      rcases hv with hv | hv
      · exact .inr ⟨[], a, _, rfl, hv, by omega, by simp⟩
      · refine .inr ⟨[a], b, _, rfl, hv, by omega, fun d hd => ?_⟩
        simp only [List.mem_singleton] at hd
        subst hd
        omega
    | cons d pre =>
      simp only [List.cons_append, List.cons.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      have hd := hpre _ List.mem_cons_self
      simp only [Term.size] at hd
      refine .inr ⟨a :: b :: pre, c, post, rfl, hv, hc', fun d' hd' => ?_⟩
      simp only [List.mem_cons] at hd'
      rcases hd' with rfl | rfl | hd'
      · omega
      · omega
      · exact hpre d' (List.mem_cons_of_mem _ hd')

theorem Cov.top {acc : List Nat} {ps : List Pat} {t : Pat} {v : Nat}
    (h : Cov acc (t :: ps) t v) : v ∈ acc := by
  rcases h with h | ⟨pre, c, post, e, -, hc', hpre⟩
  · exact h
  · cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      omega
    | cons d pre =>
      simp only [List.cons_append, List.cons.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      have := hpre _ List.mem_cons_self
      omega

/-- The state of the walk of `firsts`: the stack holds the terms `ps`, and
`acc` are the variables listed so far, in order. A listed variable is
flagged, the variables of a flagged term are listed or come up before
anything that is not smaller than the term, and listing what the stack
still holds after `acc` gives the first occurrences of the term walked. -/
structure FSt (nm : Option Nat → Sym) (n0 : List store.Node) (tp : Pat)
    (Bt : Nat → Option Nat) (st : List store.Frame) (acc : List Nat) (ps : List Pat) : Prop where
  frames : List.Forall₂ (fun f t => Repr nm n0 (fkey f) t ∧ t ∈ tp.subs) st ps
  accfl : ∀ v ∈ acc, ∃ k, Repr nm n0 k (.var v) ∧ Bt k ≠ none
  fix : Sorts.firsts acc = acc
  cov : ∀ k t, Bt k ≠ none → Repr nm n0 k t → ∀ v ∈ t.vars, Cov acc ps t v
  goal : Sorts.firsts (acc ++ ps.flatMap Term.vars) = Sorts.firsts tp.vars

variable {n0 : List store.Node} {tp : Pat} {Bt : Nat → Option Nat}

/-- The node of the top frame is flagged already. -/
theorem FSt.hit {fr : store.Frame} {st : List store.Frame} {tq : Pat} {ps : List Pat}
    {acc : List Nat} (h : FSt nm n0 tp Bt (fr :: st) acc (tq :: ps))
    (hq : Repr nm n0 (fkey fr) tq) (hfl : Bt (fkey fr) ≠ none) : FSt nm n0 tp Bt st acc ps := by
  have hin : ∀ v ∈ tq.vars, v ∈ acc := fun v hv => (h.cov _ _ hfl hq v hv).top
  obtain ⟨-, hfr⟩ := List.forall₂_cons.1 h.frames
  refine ⟨hfr, h.accfl, h.fix,
    fun k t hk hr v hv => (h.cov k t hk hr v hv).pop (fun _ h => h) hin, ?_⟩
  rw [← h.goal, List.flatMap_cons, firsts_drop _ hin]

/-- The node of the top frame is flagged, and the stack and the list
change. -/
theorem FSt.set {fr : store.Frame} {st : List store.Frame} {tq : Pat} {ps : List Pat}
    {acc : List Nat} (h : FSt nm n0 tp Bt (fr :: st) acc (tq :: ps))
    (hq : Repr nm n0 (fkey fr) tq) (r : Nat) {st' : List store.Frame} {acc' : List Nat}
    {ps' : List Pat}
    (hfr : List.Forall₂ (fun f t => Repr nm n0 (fkey f) t ∧ t ∈ tp.subs) st' ps')
    (hnew : ∀ v ∈ acc', v ∈ acc ∨ tq = .var v) (hfix : Sorts.firsts acc' = acc')
    (hself : ∀ v ∈ tq.vars, Cov acc' ps' tq v)
    (hold : ∀ t v, Cov acc (tq :: ps) t v → Cov acc' ps' t v)
    (hgoal : acc' ++ ps'.flatMap Term.vars = acc ++ (tq :: ps).flatMap Term.vars) :
    FSt nm n0 tp (Function.update Bt (fkey fr) (some r)) st' acc' ps' := by
  have hgrow : ∀ k, Bt k ≠ none → Function.update Bt (fkey fr) (some r) k ≠ none := by
    intro k hk
    by_cases e : k = fkey fr
    · rw [e]; simp
    · rw [Function.update_of_ne e]; exact hk
  refine ⟨hfr, fun v hv => ?_, hfix, fun k t hk hr v hv => ?_, by rw [hgoal]; exact h.goal⟩
  · rcases hnew v hv with hv | rfl
    · obtain ⟨k, hk, hfl⟩ := h.accfl v hv
      exact ⟨k, hk, hgrow k hfl⟩
    · exact ⟨fkey fr, hq, by simp⟩
  · by_cases e : k = fkey fr
    · subst e
      rw [hr.unique hq] at hv ⊢
      exact hself v hv
    · rw [Function.update_of_ne e] at hk
      exact hold t v (h.cov k t hk hr v hv)

/-- The invariant of the loop of `firsts`. `s0` is the store at its start
and `Bd` the tick count it stays under. -/
def FInv (nm : Option Nat → Sym) (s0 : store.Store) (tp : Pat) (Bd : Nat) (s : store.Store)
    (out : store.TermId) : Prop :=
  Wf s ∧ Extends s0 s ∧ ∃ acc ps, FSt nm s0.nodes.val tp (tbl s .B) (stk s) acc ps ∧
    Repr nm s.nodes.val out.val (encList (nm none) (acc.reverse.map Term.var)) ∧
    s.ticks.val + 1 + 2 * (stk s).length +
      8 * (pending nm s0.nodes.val (tbl s .B) tp.subs).card ≤ Bd

def FDone (nm : Option Nat → Sym) (s0 : store.Store) (tp : Pat) (Bd : Nat) (s : store.Store)
    (out : store.TermId) : Prop :=
  Wf s ∧ stk s = [] ∧ Extends s0 s ∧
    Repr nm s.nodes.val out.val
      (encList (nm none) ((Sorts.firsts tp.vars).reverse.map Term.var)) ∧
    s.ticks.val ≤ Bd

def FBodyPost (nm : Option Nat → Sym) (s0 : store.Store) (tp : Pat) (Bd : Nat) (t0 : Nat) :
    ControlFlow (store.Store × store.TermId) (store.Store × store.TermId) → Prop
  | .done x => FDone nm s0 tp Bd x.1 x.2 ∧ t0 ≤ x.1.ticks.val
  | .cont x => FInv nm s0 tp Bd x.1 x.2 ∧ t0 < x.1.ticks.val

theorem firsts_body_spec (hnm : Function.Injective nm) (s0 : store.Store) (tp : Pat) (Bd : Nat)
    (hB : 40 * Bd + 100 ≤ Usize.max) (hN : NodesOK s0.nodes.val) (s : store.Store)
    (out : store.TermId) (h : FInv nm s0 tp Bd s out) :
    sorts.firsts_loop.body s out ⦃ r => FBodyPost nm s0 tp Bd s.ticks.val r ⦄ := by
  unfold sorts.firsts_loop.body
  obtain ⟨hW, hE, acc, ps, hF, hout, hc⟩ := h
  obtain ⟨more, hmore, -⟩ := id hE
  step with pop_w s hW (by unfold Room; omega) as ⟨o, s1, e1, e2, e3, hW1, eo, est⟩
  cases hst : stk s with
  | nil =>
    rw [hst] at eo est hF hc
    simp only [List.head?_nil, List.tail_nil] at eo est
    subst eo
    simp only [WP.spec_ok, FBodyPost]
    have hps : ps = [] := by
      cases hF.frames
      rfl
    subst hps
    have hacc : acc = Sorts.firsts tp.vars := by
      have := hF.goal
      simp only [List.flatMap_nil, List.append_nil] at this
      rw [hF.fix] at this
      exact this
    simp only [List.length_nil] at hc
    refine ⟨⟨hW1, est, hE.trans (Extends.of_eq e1 (by omega)), ?_, by omega⟩, by omega⟩
    rw [e1, ← hacc]
    exact hout
  | cons fr st =>
    rw [hst] at eo est hF hc
    simp only [List.head?_cons, List.tail_cons] at eo est
    subst eo
    simp only [List.length_cons] at hc
    obtain ⟨tq, ps', ⟨hq, htq⟩, hfr', rfl⟩ := List.forall₂_cons_left_iff.1 hF.frames
    have hqs : fkey fr < s.nodes.val.length := by
      rw [hmore, List.length_append]
      have := hq.lt
      omega
    simp only [node_of_eq]
    step with get_flag_w s1 .B (fid fr) hW1 (by rw [e1, fid_val]; exact hqs)
      (by unfold Room; omega) as ⟨o1, s2, ho1, hK2⟩
    rw [e2, fid_val] at ho1
    have ht2 := hK2.ticks
    have hn2 : s2.nodes.val = s.nodes.val := by rw [hK2.nodes, e1]
    have htb2 : tbl s2 = tbl s := by rw [hK2.tbl, e2]
    have hstk2 : stk s2 = st := by rw [hK2.stk, est]
    cases hBq : tbl s .B (fkey fr) with
    | some w =>
      rw [hBq] at ho1
      simp only [Option.map_some] at ho1
      subst ho1
      simp only [WP.spec_ok, FBodyPost]
      refine ⟨⟨hK2.wf, hE.trans (Extends.of_eq hn2 (by omega)), acc, ps', ?_,
        by rw [hn2]; exact hout, ?_⟩, by omega⟩
      · rw [htb2, hstk2]
        exact hF.hit hq (by rw [hBq]; simp)
      · rw [htb2, hstk2]; omega
    | none =>
      rw [hBq] at ho1
      simp only [Option.map_none] at ho1
      subst ho1
      simp only
      have hP := pending_set_card hnm hN hq hBq htq 1
      step with set_flag_w s2 .B (fid fr) true hK2.wf (by rw [hn2, fid_val]; exact hqs)
        (by unfold Room; omega) as ⟨s3, g1, g2, g3, g4, g5, g6⟩
      rw [htb2, fid_val] at g4
      simp only [↓reduceIte] at g4
      have hn3 : s3.nodes.val = s.nodes.val := by rw [g1, hn2]
      have hstk3 : stk s3 = st := by rw [g6, hstk2]
      step with read_w s3 (fid fr) g3 (by rw [hn3, fid_val]; exact hqs)
        (by unfold Room; omega) as ⟨nd, s4, hnd, hK4⟩
      rw [hn3, fid_val, hmore, List.getElem?_append_left hq.lt] at hnd
      have ht4 := hK4.ticks
      have hn4 : s4.nodes.val = s.nodes.val := by rw [hK4.nodes, hn3]
      have hB4 : tbl s4 .B = Function.update (tbl s .B) (fkey fr) (some 1) := by
        rw [hK4.tbl, g4]
      have hstk4 : stk s4 = st := by rw [hK4.stk, hstk3]
      have hx4 : Extends s0 s4 := hE.trans (Extends.of_eq hn4 (by omega))
      -- a symbol or the end of a list: nothing to list
      have hsym : tq.vars = [] → FBodyPost nm s0 tp Bd s.ticks.val (.cont (s4, out)) := by
        intro hv0
        simp only [FBodyPost]
        refine ⟨⟨hK4.wf, hx4, acc, ps', ?_, by rw [hn4]; exact hout, ?_⟩, by omega⟩
        · rw [hB4, hstk4]
          refine hF.set hq 1 hfr' (fun v hv => .inl hv) hF.fix ?_
            (fun t v hc => hc.pop (fun _ h => h) (by rw [hv0]; simp)) (by simp [hv0])
          rw [hv0]
          intro v hv
          cases hv
        · rw [hB4, hstk4]; omega
      -- a variable: it is listed
      have hvar : ∀ x, tq = Term.var x →
          (do
            let (out1, s5) ← store.Store.alloc s4 (store.Node.App (fid fr) out)
            ok (ControlFlow.cont (s5, out1) :
              ControlFlow (store.Store × store.TermId) (store.Store × store.TermId))) ⦃ r =>
            FBodyPost nm s0 tp Bd s.ticks.val r ⦄ := by
        intro x hx
        subst hx
        have hxacc : x ∉ acc := by
          intro hmem
          obtain ⟨k, hk, hfl⟩ := hF.accfl x hmem
          rw [Repr.inj hnm hN hk hq] at hfl
          exact hfl hBq
        step with alloc_w s4 (.App (fid fr) out) hK4.wf
          ⟨by rw [hn4, fid_val]; exact hqs, by rw [hn4]; exact hout.lt⟩
          (by unfold Room; omega) as ⟨out1, s5, hW5, ht5, htb5, hx5, hid, hst5⟩
        simp only [norm] at hid
        simp only [FBodyPost]
        have ra : Repr nm s5.nodes.val (fid fr).val (.var x) := by
          rw [fid_val]
          exact (hx4.trans hx5).repr hq
        refine ⟨⟨hW5, hx4.trans hx5, acc ++ [x], ps', ?_, ?_, ?_⟩, by omega⟩
        · rw [htb5, hB4, hst5, hstk4]
          refine hF.set hq 1 hfr' (fun v hv => ?_) (firsts_fix_snoc hF.fix hxacc)
            (fun v hv => .inl ?_) (fun t v hc => hc.pop (fun w hw => by simp [hw]) (by simp [Term.vars]))
            (by simp [Term.vars])
          · simp only [List.mem_append, List.mem_singleton] at hv
            rcases hv with hv | rfl
            · exact .inl hv
            · exact .inr rfl
          · simp only [Term.vars, List.mem_singleton] at hv
            simp [hv]
        · rw [List.reverse_append]
          simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
            List.map_cons, encList]
          exact .app hid ra (hx5.repr (by rw [hn4]; exact hout))
        · rw [htb5, hB4, hst5, hstk4]; omega
      cases nd with
      | V0 =>
        cases hq with
        | var hv => exact hvar _ rfl
        | sym h => rw [hnd] at h; cases h
        | nil h => rw [hnd] at h; cases h
        | app h _ _ => rw [hnd] at h; cases h
      | VL a =>
        cases hq with
        | var hv => exact hvar _ rfl
        | sym h => rw [hnd] at h; cases h
        | nil h => rw [hnd] at h; cases h
        | app h _ _ => rw [hnd] at h; cases h
      | VR a =>
        cases hq with
        | var hv => exact hvar _ rfl
        | sym h => rw [hnd] at h; cases h
        | nil h => rw [hnd] at h; cases h
        | app h _ _ => rw [hnd] at h; cases h
      | Sym g =>
        simp only [WP.spec_ok]
        cases hq with
        | var hv => obtain ⟨m, hm, hvn⟩ := hv.node; rw [hnd] at hm; cases hm; exact hvn.elim
        | sym h => exact hsym rfl
        | nil h => exact hsym rfl
        | app h _ _ => rw [hnd] at h; cases h
      | Nil =>
        simp only [WP.spec_ok]
        cases hq with
        | var hv => obtain ⟨m, hm, hvn⟩ := hv.node; rw [hnd] at hm; cases hm; exact hvn.elim
        | sym h => exact hsym rfl
        | nil h => exact hsym rfl
        | app h _ _ => rw [hnd] at h; cases h
      | App a b =>
        obtain ⟨ta, tb, e, ha, hb⟩ := hq.of_app hnd
        subst e
        simp only
        step with push_w s4 (.Visit b b) hK4.wf (by unfold Room; omega)
          as ⟨s5, b1, b2, b3, hW5, b5⟩
        step with push_w s5 (.Visit a a) hW5 (by unfold Room; omega)
          as ⟨s6, c1, c2, c3, hW6, c5⟩
        have hstk6 : stk s6 = .Visit a a :: .Visit b b :: st := by rw [c5, b5, hstk4]
        have hn6 : s6.nodes.val = s.nodes.val := by rw [c1, b1, hn4]
        simp only [FBodyPost]
        refine ⟨⟨hW6, hE.trans (Extends.of_eq hn6 (by omega)), acc, ta :: tb :: ps', ?_,
          by rw [hn6]; exact hout, ?_⟩, by omega⟩
        · rw [c2, b2, hB4, hstk6]
          refine hF.set hq 1
            (.cons ⟨ha, Term.subs_trans htq (by simp [Term.subs, Term.self_mem_subs])⟩
              (.cons ⟨hb, Term.subs_trans htq (by simp [Term.subs, Term.self_mem_subs])⟩ hfr'))
            (fun v hv => .inl hv) hF.fix (fun v hv => ?_) (fun t v hc => hc.app)
            (by simp [Term.vars])
          simp only [Term.vars, List.mem_append] at hv
          rcases hv with hv | hv
          · exact .inr ⟨[], ta, tb :: ps', rfl, hv, by simp only [Term.size]; omega, by simp⟩
          · refine .inr ⟨[ta], tb, ps', rfl, hv, by simp only [Term.size]; omega, fun d hd => ?_⟩
            simp only [List.mem_singleton] at hd
            subst hd
            simp only [Term.size]
            omega
        · rw [c2, b2, hB4, hstk6]
          simp only [List.length_cons]
          omega

theorem firsts_loop_spec (hnm : Function.Injective nm) (s0 : store.Store) (out : store.TermId)
    (tp : Pat) (Bd : Nat) (hB : 40 * Bd + 100 ≤ Usize.max) (hN : NodesOK s0.nodes.val)
    (h : FInv nm s0 tp Bd s0 out) :
    sorts.firsts_loop s0 out ⦃ x => FDone nm s0 tp Bd x.1 x.2 ⦄ := by
  unfold sorts.firsts_loop
  exact loop.spec_decr_nat
    (fun x : store.Store × store.TermId => Bd + 1 - x.1.ticks.val)
    (fun x => FInv nm s0 tp Bd x.1 x.2)
    (fun x : store.Store × store.TermId => FDone nm s0 tp Bd x.1 x.2)
    (fun x : store.Store × store.TermId => sorts.firsts_loop.body x.1 x.2) (s0, out)
    (by
      rintro ⟨y, o⟩ hinv
      refine WP.spec_mono (firsts_body_spec hnm s0 tp Bd hB hN y o hinv) ?_
      intro r hr
      cases r with
      | done z => exact hr.1
      | cont z =>
        obtain ⟨h1, h2⟩ := hr
        have hc := h1.2.2
        obtain ⟨acc, ps, -, -, hc⟩ := hc
        exact ⟨h1, by simp only at h2 ⊢; omega⟩)
    h

/-- The ticks `firsts` may take. -/
def firstsCost (t : Pat) : Nat := 8 * t.subs.card + 2 * (Sorts.firsts t.vars).length + 8

/-- `firsts` lists the variables of the term, once each, in the order they
first occur. -/
theorem firsts_spec (hnm : Function.Injective nm) (s : store.Store) (t : store.TermId)
    {tp : Pat} (hI : Inv s) (ht : Repr nm s.nodes.val t.val tp) (hroom : Room s (firstsCost tp)) :
    sorts.firsts s t ⦃ r s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + firstsCost tp ∧
        Repr nm s'.nodes.val r.val
          (encList (nm none) ((Sorts.firsts tp.vars).map Term.var)) ⦄ := by
  unfold sorts.firsts
  have hroom' := hroom
  unfold Room at hroom'
  simp only [firstsCost] at hroom'
  step with clear_w s .B hI.toWf (by unfold Room; omega) as ⟨s1, c1, c2, c3, c4, c5, c6⟩
  step with alloc_w s1 .Nil c3 trivial (by unfold Room; omega)
    as ⟨out, s2, hW2, ht2, htb2, hx2, hid, hst2⟩
  step with push_w s2 (.Visit t t) hW2 (by unfold Room; omega) as ⟨s3, p1, p2, p3, hW3, p5⟩
  have hx1 : Extends s s1 := Extends.of_eq c1 (by omega)
  have hx3 : Extends s s3 := (hx1.trans hx2).trans (Extends.of_eq p1 (by omega))
  have hBn : ∀ k, tbl s3 .B k = none := by
    intro k
    rw [p2, htb2]
    exact c4 k
  have hpc := pending_card_le (nm := nm) s3.nodes.val (tbl s3 .B) tp.subs
  have hstk3 : stk s3 = [.Visit t t] := by rw [p5, hst2, c6, hI.empty]
  have hinv : FInv nm s3 tp (s3.ticks.val + 3 + 8 * tp.subs.card) s3 out := by
    refine ⟨hW3, Extends.of_eq rfl (by omega), [], [tp], ⟨?_, ?_, rfl, ?_, by simp⟩, ?_, ?_⟩
    · rw [hstk3]
      exact .cons ⟨hx3.repr ht, Term.self_mem_subs tp⟩ .nil
    · intro v hv
      cases hv
    · intro k t' hk
      exact absurd (hBn k) hk
    · rw [p1]
      exact .nil hid
    · rw [hstk3]
      simp only [List.length_singleton]
      omega
  step with firsts_loop_spec hnm s3 out tp (s3.ticks.val + 3 + 8 * tp.subs.card) (by omega)
    hW3.nodesOK hinv as ⟨s4, out1, hD⟩
  obtain ⟨hW4, hst4, hx4, hr4, ht4⟩ := hD
  step with rev_spec ((Sorts.firsts tp.vars).reverse.map Term.var) s4 out1 hW4 hr4
    (by simp only [List.length_map, List.length_reverse]; unfold Room; omega) as ⟨r, s5, hR, hr5⟩
  simp only [List.length_map, List.length_reverse] at hR
  have ht5 := hR.ticks
  refine ⟨⟨hR.wf, by rw [hR.stk]; exact hst4⟩, (hx3.trans hx4).trans hR.ext,
    by simp only [firstsCost]; omega, ?_⟩
  simpa [List.map_reverse] using hr5

/-! ## The sorts of each variable -/

theorem conjOf_sub {U : List Name} {L : List (Nat × Sorts.Conj)} (h : ∀ p ∈ L, Sub U p.2)
    (v : Nat) : Sub U (conjOf L v) := by
  induction L with
  | nil =>
    intro n hn
    simp [conjOf_nil] at hn
  | cons e L ih =>
    rw [conjOf_cons]
    by_cases hv : v = e.1
    · rw [ite_pos' hv]
      exact h e List.mem_cons_self
    · rw [ite_neg' hv]
      exact ih fun p hp => h p (List.mem_cons_of_mem _ hp)

/-- The declared sorts that hold of all values of the variable `v`: the
members of its conjunction among the entries `L` without the terms the
exclusions `X` exclude it from. -/
def upConj (S : Sorts) (L : List (Nat × Sorts.Conj)) (X : List (Eqns Nat)) (v : Nat) :
    Sorts.Conj :=
  (Sorts.names S).filter fun n => Sorts.inclBut S (conjOf L v) n (Sorts.gone X v)

/-- The ticks the first loop of `renumber` may take: for each variable the
search among `l` entries, the excluded terms, and the test of each sort. -/
def conjsCost (nm : Option Nat → RwLog.Sym) (S : Sorts) (u r q l : Nat) (X : List (Eqns Nat)) :
    List Nat → Nat
  | [] => 1
  | v :: R => 3 * l + goneCost nm v X + uppersCost S u r q (Sorts.sumSize (Sorts.gone X v)) + 4 +
      conjsCost nm S u r q l X R

theorem renumber_loop_spec (hnm : Function.Injective nm) {S : Sorts} {sp : Pat} {U : List Name}
    (hC : Ctx nm S sp U) (hS : S.WellFormed) (hUS : ∀ n ∈ U, n ∈ Sorts.names S) {r q : Nat}
    (hr : ∀ d, (Sorts.reachSet S d).card ≤ r)
    (hq : ∀ d m, (Sorts.reachGSet S (d, some m)).card ≤ q)
    (decls names x es : store.TermId) (X : List (Eqns Nat)) (L : List (Nat × Sorts.Conj))
    (hsub : ∀ p ∈ L, Sub U p.2) :
    ∀ (R : List Nat) (s : store.Store) (l cs : store.TermId) (acc : List Pat),
    Inv s → Repr nm s.nodes.val decls.val sp →
    Repr nm s.nodes.val names.val (namesPat (nm none) U) →
    Repr nm s.nodes.val x.val (encX nm X) →
    Repr nm s.nodes.val es.val (encVarEntries nm U L) →
    Repr nm s.nodes.val l.val (encList (nm none) (R.map Term.var)) →
    Repr nm s.nodes.val cs.val (encList (nm none) acc) →
    Room s (conjsCost nm S U.length r q L.length X R) →
    sorts.renumber_loop l s decls names x es cs ⦃ s' res =>
      Inv s' ∧ Extends s s' ∧
        s'.ticks.val ≤ s.ticks.val + conjsCost nm S U.length r q L.length X R ∧
        Repr nm s'.nodes.val res.val
          (encList (nm none)
            ((R.map fun v => cpat (nm none) U (upConj S L X v)).reverse ++ acc)) ⦄ := by
  intro R
  induction R with
  | nil =>
    intro s l cs acc hI hde hU hx hes hl hcs hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [conjsCost] at hroom'
    unfold sorts.renumber_loop
    rw [loop]
    simp only [sorts.renumber_loop.body]
    step with uncons_repr s l hI.toWf (p := Term.sym (nm none)) hl (by unfold Room; omega)
      as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    subst hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    have hx1 : Extends s s1 := Extends.of_eq K1.nodes (by omega)
    have hfin : Inv s1 ∧ Extends s s1 ∧
        s1.ticks.val ≤ s.ticks.val + conjsCost nm S U.length r q L.length X [] ∧
        Repr nm s1.nodes.val cs.val
          (encList (nm none)
            ((([] : List Nat).map fun v => cpat (nm none) U (upConj S L X v)).reverse ++ acc)) :=
      ⟨K1.inv, hx1, by simp only [conjsCost]; omega, hx1.repr hcs⟩
    step*
  | cons v R ih =>
    intro s l cs acc hI hde hU hx hes hl hcs hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [conjsCost] at hroom'
    unfold sorts.renumber_loop
    rw [loop]
    simp only [sorts.renumber_loop.body]
    step with uncons_repr s l hI.toWf
      (p := Term.app (Term.var v) (encList (nm none) (R.map Term.var))) hl
      (by unfold Room; omega) as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    obtain ⟨vi, rest, rfl, rv, rrest⟩ := hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    have hx1 : Extends s s1 := Extends.of_eq K1.nodes (by omega)
    have hvv : VarAt s1.nodes.val vi.val v := by
      rw [K1.nodes]
      cases rv with
      | var h => exact h
    step with conj_at_spec (U := U) s1 es vi L K1.inv hvv (hx1.repr hes)
      (by unfold Room; omega) as ⟨r1, hI2, hx2, ht2, rc⟩
    obtain ⟨c, s2⟩ := r1
    simp only at hI2 hx2 ht2 rc
    have hx02 := hx1.trans hx2
    step with gone_spec hnm s2 x vi hI2 (hx2.varAt hvv) (hx02.repr hx) (by unfold Room; omega)
      as ⟨r2, hI3, hx3, ht3, rg⟩
    obtain ⟨g, s3⟩ := r2
    simp only at hI3 hx3 ht3 rg
    have hx03 := hx02.trans hx3
    step with uppers_spec hC hS hUS hr hq (conjOf L v) (upConj S L X v) (Sorts.gone X v)
      (conjOf_sub hsub v)
      (fun n hn => by
        simp only [upConj, Finset.mem_filter, hUS n hn, true_and]
        exact (Sorts.hold_iff_inclBut hS _ _ _).symm)
      s3 decls names c g hI3 (hx03.repr hde) (hx03.repr hU) (hx3.repr rc) rg
      (by unfold Room; omega) as ⟨r3, hI4, hx4, ht4, ru⟩
    obtain ⟨u, s4⟩ := r3
    simp only at hI4 hx4 ht4 ru
    have hx04 := hx03.trans hx4
    step with alloc_spec s4 (.App u cs) hI4 ⟨ru.lt, (hx04.repr hcs).lt⟩
      (by unfold Room; omega) as ⟨r4, hI5, ht5, htb5, hx5, hr5⟩
    obtain ⟨cs1, s5⟩ := r4
    simp only [norm] at hI5 ht5 htb5 hx5 hr5
    simp only [uncurry, bind_ok]
    have hx05 := hx04.trans hx5
    have rcs : Repr nm s5.nodes.val cs1.val
        (encList (nm none) (cpat (nm none) U (upConj S L X v) :: acc)) :=
      .app hr5 (hx5.repr ru) (hx05.repr hcs)
    have IH := ih s5 rest cs1 (cpat (nm none) U (upConj S L X v) :: acc) hI5 (hx05.repr hde)
      (hx05.repr hU) (hx05.repr hx) (hx05.repr hes) (hx05.repr rrest) rcs
      (by unfold Room; omega)
    unfold sorts.renumber_loop at IH
    refine WP.spec_mono IH ?_
    rintro ⟨s', res⟩ ⟨hI', hx', ht', hr'⟩
    refine ⟨hI', hx05.trans hx', by simp only [conjsCost]; omega, ?_⟩
    simpa using hr'

/-! ## The table of the new variables -/

/-- The ticks the second loop of `renumber` may take over `k` variables,
the first of which gets the variable `n`. -/
def numCost : Nat → Nat → Nat
  | _, 0 => 1
  | n, k + 1 => succCost n + 2 + numCost (n + 1) k

/-- Table `B` after the loop: each variable of the list has its place from
`n` on, and no other entry has changed. -/
structure NumPost (nodes : List store.Node) (B B' : Nat → Option Nat) (R : List Nat) (n : Nat) :
    Prop where
  set : ∀ i v, R[i]? = some v → ∃ q u, VarAt nodes q v ∧ B' q = some u ∧ VarAt nodes u (n + i)
  keep : ∀ q, (∀ v ∈ R, ¬ VarAt nodes q v) → B' q = B q

theorem number_loop_spec :
    ∀ (R : List Nat) (s : store.Store) (l place : store.TermId) (n : Nat),
    Inv s → R.Nodup → Repr nm s.nodes.val l.val (encList (nm none) (R.map Term.var)) →
    VarAt s.nodes.val place.val n → Room s (numCost n R.length) →
    sorts.number_loop l s place ⦃ place' s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + numCost n R.length ∧
        tbl s' .A = tbl s .A ∧ NumPost s'.nodes.val (tbl s .B) (tbl s' .B) R n ∧
        VarAt s'.nodes.val place'.val (n + R.length) ⦄ := by
  intro R
  induction R with
  | nil =>
    intro s l place n hI hnd hl hp hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_nil, numCost] at hroom'
    unfold sorts.number_loop
    rw [loop]
    simp only [sorts.number_loop.body]
    step with uncons_repr s l hI.toWf (p := Term.sym (nm none)) hl (by unfold Room; omega)
      as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    subst hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    have hfin : Inv s1 ∧ Extends s s1 ∧
        s1.ticks.val ≤ s.ticks.val + numCost n ([] : List Nat).length ∧
        tbl s1 .A = tbl s .A ∧ NumPost s1.nodes.val (tbl s .B) (tbl s1 .B) [] n ∧
        VarAt s1.nodes.val place.val (n + ([] : List Nat).length) :=
      ⟨K1.inv, Extends.of_eq K1.nodes (by omega), by simp only [List.length_nil, numCost]; omega,
        by rw [hK0.tbl], ⟨fun i v h => by simp at h, fun q _ => by rw [hK0.tbl]⟩,
        by rw [K1.nodes]; simpa using hp⟩
    step*
  | cons v R ih =>
    intro s l place n hI hnd hl hp hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons, numCost] at hroom'
    rw [List.nodup_cons] at hnd
    unfold sorts.number_loop
    rw [loop]
    simp only [sorts.number_loop.body]
    step with uncons_repr s l hI.toWf
      (p := Term.app (Term.var v) (encList (nm none) (R.map Term.var))) hl
      (by unfold Room; omega) as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    obtain ⟨vi, rest, rfl, rv, rrest⟩ := hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    have hx1 : Extends s s1 := Extends.of_eq K1.nodes (by omega)
    have hvv : VarAt s1.nodes.val vi.val v := by
      rw [K1.nodes]
      cases rv with
      | var h => exact h
    step with set_spec s1 .B vi place K1.inv hvv.lt (by unfold Room; omega)
      as ⟨s2, g1, g2, g3, g4, g5⟩
    rw [hK0.tbl] at g4
    have hx2 : Extends s s2 := hx1.trans (Extends.of_eq g1 (by omega))
    step with var_succ_spec s2 place g3 (hx2.varAt hp) (by unfold Room; omega)
      as ⟨r3, hI3, hx3, htb3, hp3, ht3⟩
    obtain ⟨place1, s3⟩ := r3
    simp only at hI3 hx3 htb3 hp3 ht3
    simp only [uncurry, bind_ok]
    have hx03 := hx2.trans hx3
    have IH := ih s3 rest place1 (n + 1) hI3 hnd.2 (hx03.repr rrest) hp3 (by unfold Room; omega)
    unfold sorts.number_loop at IH
    refine WP.spec_mono IH ?_
    rintro ⟨place', s'⟩ ⟨hI', hx', ht', hA', hN, hp'⟩
    have hB3 : tbl s3 .B = Function.update (tbl s .B) vi.val (some place.val) := by
      rw [htb3, g4]
    have hvs' : VarAt s'.nodes.val vi.val v := hx'.varAt (hx3.varAt (by rw [g1]; exact hvv))
    refine ⟨hI', hx03.trans hx', by simp only [List.length_cons, numCost]; omega, ?_,
      ⟨?_, ?_⟩, by
        rw [List.length_cons, show n + (R.length + 1) = n + 1 + R.length by omega]
        exact hp'⟩
    · rw [hA', htb3, g5 .A (by simp), hK0.tbl]
    · intro i w hi
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        subst hi
        refine ⟨vi.val, place.val, hvs', ?_, hx'.varAt (hx3.varAt (hx2.varAt hp))⟩
        rw [hN.keep vi.val fun w hw hva => hnd.1 (by rw [hvs'.unique hva]; exact hw), hB3]
        simp
      | succ i =>
        simp only [List.getElem?_cons_succ] at hi
        obtain ⟨q', u', h1, h2, h3⟩ := hN.set i w hi
        exact ⟨q', u', h1, h2, by rw [show n + (i + 1) = n + 1 + i by omega]; exact h3⟩
    · intro q' hq'
      rw [hN.keep q' fun w hw => hq' w (List.mem_cons_of_mem _ hw), hB3]
      refine Function.update_of_ne ?_ _ _
      rintro rfl
      exact hq' v List.mem_cons_self hvs'

/-- Each variable of the list becomes the variable of its place; any other
stays. -/
def numSub (F : List Nat) (v : Nat) : Pat := if v ∈ F then .var (F.idxOf v) else .var v

/-- `number` sets table `B` to the substitution that numbers the variables
of a list by their places, and returns the variable after the last place. -/
theorem number_spec (F : List Nat) (hFnd : F.Nodup) (s : store.Store) (vs : store.TermId)
    (hI : Inv s) (hvs : Repr nm s.nodes.val vs.val (encList (nm none) (F.map Term.var)))
    (hroom : Room s (numCost 0 F.length + 2)) :
    sorts.number s vs ⦃ next s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + numCost 0 F.length + 2 ∧
        tbl s' .A = tbl s .A ∧ VarAt s'.nodes.val next.val F.length ∧
        LeafOK nm s'.nodes.val (tbl s' .B) term.Leaf.Map (numSub F) ⦄ := by
  unfold sorts.number
  have hroom' := hroom
  unfold Room at hroom'
  step with clear_spec s .B hI (by unfold Room; omega) as ⟨s5, c1, c2, c3, c4, c5⟩
  have hx05 : Extends s s5 := Extends.of_eq c1 (by omega)
  step with alloc_spec s5 .V0 c3 trivial (by unfold Room; omega)
    as ⟨place, s6, hI6, ht6, htb6, hx6, hr6⟩
  simp only [norm] at hr6
  have hx06 := hx05.trans hx6
  refine WP.spec_mono (number_loop_spec (nm := nm) F s6 vs place 0 hI6 hFnd (hx06.repr hvs)
    (.zero hr6) (by unfold Room; omega)) ?_
  rintro ⟨next, s7⟩ ⟨hI7, hx7, ht7, hA7, hN, hp7⟩
  have hB6 : ∀ k, tbl s6 .B k = none := by
    intro k
    rw [htb6]
    exact c4 k
  refine ⟨hI7, hx06.trans hx7, by omega, by rw [hA7, htb6, c5 .A (by simp)],
    by simpa using hp7, fun k u hk => ?_, fun v hv => ?_⟩
  · by_cases hin : ∃ v ∈ F, VarAt s7.nodes.val k v
    · obtain ⟨v, hvF, hva⟩ := hin
      obtain ⟨i, hi, e⟩ := List.getElem_of_mem hvF
      obtain ⟨q', u', h1, h2, h3⟩ := hN.set i v (by rw [List.getElem?_eq_getElem hi, e])
      rw [hva.inj hI7.nodesOK h1, h2] at hk
      cases hk
      refine ⟨v, hva, ?_⟩
      have hidx : F.idxOf v = i := by rw [← e]; exact hFnd.idxOf_getElem i hi
      simp only [numSub, hvF, ↓reduceIte, hidx]
      simpa using Repr.var (nm := nm) h3
    · rw [hN.keep k fun v hv hva => hin ⟨v, hv, hva⟩, hB6] at hk
      cases hk
  · by_cases hvF : v ∈ F
    · obtain ⟨i, hi, e⟩ := List.getElem_of_mem hvF
      obtain ⟨q', u', h1, h2, -⟩ := hN.set i v (by rw [List.getElem?_eq_getElem hi, e])
      rw [hv q' h1] at h2
      cases h2
    · simp [numSub, hvF]

/-! ## `sorts::renumber` -/

theorem bind_numSub {F : List Nat} {t : Pat} (h : ∀ v ∈ t.vars, v ∈ F) :
    t.bind (numSub F) = t.rename fun v => F.idxOf v :=
  Term.bind_congr fun v hv => by simp [numSub, h v hv]

theorem encEqs_bind (σ : Nat → Pat) (E : Eqns Nat) :
    (encEqs nm E).bind σ = encEqs nm (E.map fun p => (p.1.bind σ, p.2.bind σ)) := by
  induction E with
  | nil => rfl
  | cons p E ih => simp only [encEqs, Term.bind_app, List.map_cons, ih]

/-- On exclusions whose variables are all in the list, the substitution is
the renaming of the specification. -/
theorem encX_numSub {F : List Nat} {X : List (Eqns Nat)}
    (h : ∀ E ∈ X, ∀ p ∈ E, (∀ v ∈ p.1.vars, v ∈ F) ∧ ∀ v ∈ p.2.vars, v ∈ F) :
    (encX nm X).bind (numSub F) = encX nm (X.map (Eqns.ren fun v => F.idxOf v)) := by
  simp only [encX, encList_bind, List.map_map]
  congr 1
  refine List.map_congr_left fun E hE => ?_
  simp only [Function.comp_apply, encEqs_bind, Eqns.ren]
  congr 1
  refine List.map_congr_left fun p hp => ?_
  rw [bind_numSub (h E hE p hp).1, bind_numSub (h E hE p hp).2]

/-- The ticks `renumber` may take. -/
noncomputable def renumberCost (nm : Option Nat → RwLog.Sym) (S : Sorts) (u r q : Nat) (T : Pat)
    (X : List (Eqns Nat)) (L : List (Nat × Sorts.Conj)) : Nat :=
  firstsCost T + conjsCost nm S u r q L.length X (Sorts.firsts T.vars) +
    2 * (Sorts.firsts T.vars).length + numCost 0 (Sorts.firsts T.vars).length +
    14 * (T.subs ∪ (encX nm X).subs).card + 16

/-- `renumber` gives the pattern and the exclusions with each variable of
the pattern replaced by the variable of the place it first occurs at, and
for each of these variables, in that order, the declared sorts that hold of
all its values. -/
theorem renumber_spec (hnm : Function.Injective nm) {S : Sorts} {sp : Pat} {U : List Name}
    (hC : Ctx nm S sp U) (hS : S.WellFormed) (hUS : ∀ n ∈ U, n ∈ Sorts.names S) {r q : Nat}
    (hr : ∀ d, (Sorts.reachSet S d).card ≤ r)
    (hq : ∀ d m, (Sorts.reachGSet S (d, some m)).card ≤ q)
    (s : store.Store) (decls names t x es : store.TermId) (T : Pat) (X : List (Eqns Nat))
    (L : List (Nat × Sorts.Conj)) (hI : Inv s) (hde : Repr nm s.nodes.val decls.val sp)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (ht : Repr nm s.nodes.val t.val T) (hx : Repr nm s.nodes.val x.val (encX nm X))
    (hes : Repr nm s.nodes.val es.val (encVarEntries nm U L)) (hsub : ∀ p ∈ L, Sub U p.2)
    (hroom : Room s (renumberCost nm S U.length r q T X L)) :
    sorts.renumber s decls names t x es ⦃ res s' =>
      Inv s' ∧ Extends s s' ∧
        s'.ticks.val ≤ s.ticks.val + renumberCost nm S U.length r q T X L ∧
        Repr nm s'.nodes.val res.1.val (T.bind (numSub (Sorts.firsts T.vars))) ∧
        Repr nm s'.nodes.val res.2.1.val ((encX nm X).bind (numSub (Sorts.firsts T.vars))) ∧
        Repr nm s'.nodes.val res.2.2.val
          (encList (nm none)
            ((Sorts.firsts T.vars).map fun v => cpat (nm none) U (upConj S L X v))) ⦄ := by
  unfold sorts.renumber
  have hroom' := hroom
  unfold Room at hroom'
  simp only [renumberCost] at hroom'
  obtain ⟨hFnd, -, -⟩ := Sorts.firsts_spec T.vars
  generalize hFe : Sorts.firsts T.vars = F at hroom' hFnd ⊢
  have hfc : firstsCost T = 8 * T.subs.card + 2 * F.length + 8 := by rw [firstsCost, hFe]
  step with firsts_spec hnm s t hI ht (by unfold Room; omega) as ⟨vs, s1, hI1, hx1, ht1, rvs⟩
  rw [hFe] at rvs
  step with alloc_spec s1 .Nil hI1 trivial (by unfold Room; omega)
    as ⟨cs, s2, hI2, ht2, htb2, hx2, hr2⟩
  have hx02 := hx1.trans hx2
  step with renumber_loop_spec hnm hC hS hUS hr hq decls names x es X L hsub F s2 vs cs []
    hI2 (hx02.repr hde) (hx02.repr hU) (hx02.repr hx) (hx02.repr hes) (hx2.repr rvs) (.nil hr2)
    (by unfold Room; omega) as ⟨s3, cs1, hI3, hx3, ht3, rcs⟩
  rw [List.append_nil] at rcs
  have hx03 := hx02.trans hx3
  step with rev_spec ((F.map fun v => cpat (nm none) U (upConj S L X v)).reverse) s3 cs1
    hI3.toWf rcs (by simp only [List.length_reverse, List.length_map]; unfold Room; omega)
    as ⟨cs2, s4, hR, rcs2⟩
  simp only [List.length_reverse, List.length_map] at hR
  rw [List.reverse_reverse] at rcs2
  have ht4 := hR.ticks
  have hI4 : Inv s4 := ⟨hR.wf, by rw [hR.stk]; exact hI3.empty⟩
  have hx04 := hx03.trans hR.ext
  step with number_spec (nm := nm) F hFnd s4 vs hI4 (((hx2.trans hx3).trans hR.ext).repr rvs)
    (by unfold Room; omega) as ⟨nx, s7, hI7, hx7, ht7, hA7, hnx7, hleaf7⟩
  have hx07 := hx04.trans hx7
  step with clear_spec s7 .A hI7 (by unfold Room; omega) as ⟨s8, d1, d2, d3, d4, d5⟩
  have hx08 : Extends s s8 := hx07.trans (Extends.of_eq d1 (by omega))
  have hleaf : LeafOK nm s8.nodes.val (tbl s8 .B) term.Leaf.Map (numSub F) := by
    rw [d1, d5 .B (by simp)]
    exact hleaf7
  have hpc := pending_card_le (nm := nm) s8.nodes.val (tbl s8 .A) (T.subs ∪ (encX nm X).subs)
  step with rebuild_spec hnm s8 .Map t (t := T) (σ := numSub F) (T.subs ∪ (encX nm X).subs) d3
    (hx08.repr ht) hleaf (by intro k v hk; rw [d4] at hk; cases hk)
    Finset.subset_union_left (by unfold Room; omega) as ⟨t1, s9, h9⟩
  have hc9 := h9.cost
  step with rebuild_spec hnm s9 .Map x (t := encX nm X) (σ := numSub F)
    (T.subs ∪ (encX nm X).subs) h9.inv ((hx08.trans h9.ext).repr hx)
    (by rw [h9.tblB]; exact hleaf.extends h9.ext) h9.memo Finset.subset_union_right
    (by unfold Room; omega) as ⟨x1, s10, h10⟩
  have hc10 := h10.cost
  refine ⟨h10.inv, (hx08.trans h9.ext).trans h10.ext, by simp only [renumberCost, hFe]; omega,
    h10.ext.repr h9.repr, h10.repr, ?_⟩
  exact h10.ext.repr (h9.ext.repr ((Extends.of_eq d1 (by omega)).repr (hx7.repr rcs2)))

/-- What `renumber` returns are the pattern, the sorts and the exclusions
that `Sorts.ofTight` assembles the normal store from. -/
theorem ofTight_abs {S : Sorts} {st : TSt} (hok : st.OK) :
    Sorts.ofTight S st.abs =
      Sorts.assembled S (st.T.rename fun v => (Sorts.firsts st.T.vars).idxOf v)
        ((Sorts.firsts st.T.vars).map (upConj S st.L st.X))
        (st.X.map (Eqns.ren fun v => (Sorts.firsts st.T.vars).idxOf v)) := by
  unfold Sorts.ofTight upConj
  simp only [hok.conj]
  rfl

/-- The list of the exclusions of the normal store of a tight store, on what
`renumber` returns. -/
theorem ofTightXs_abs {S : Sorts} {st : TSt} (hok : st.OK) :
    Sorts.ofTightXs S st.abs =
      Sorts.antichain
        (Sorts.covers ((Sorts.firsts st.T.vars).map (upConj S st.L st.X)).length)
        (Sorts.normExs S ⟨st.T.rename fun v => (Sorts.firsts st.T.vars).idxOf v,
          (Sorts.firsts st.T.vars).map (upConj S st.L st.X), ∅⟩
          (st.X.map (Eqns.ren fun v => (Sorts.firsts st.T.vars).idxOf v))) := by
  unfold Sorts.ofTightXs upConj
  simp only [hok.conj]
  rfl

end RwLogVerified
