/-
# The steps of the fold

The loops `sorts::fold` is made of besides the search for the free subterms:
`seed` puts the variable of each free subterm found in table `A`, `conjs_at`
lists the conjunctions the entries give the variables of a list, and
`moved_all` reads the equations of the exclusions back from their lists of
values.
-/
import RwLogVerified.FreeSubs
import RwLogVerified.Assemble
import RwLogVerified.Prune

open Aeneas Aeneas.Std Result

namespace RwLogVerified

open rwlog_core RwLog

variable {nm : Option Nat → Sym}

/-! ## Seeding the table -/

/-- The loop of `seed` gives the first of each pair an entry with the second:
an entry of table `A` afterwards was there before or is of a pair, and the
first of each pair has one. -/
theorem seed_loop_spec (hnm : Function.Injective nm) :
    ∀ (P : List (Pat × Pat)) (s : store.Store) (l : store.TermId), Inv s →
    Repr nm s.nodes.val l.val (encList (nm none) (P.map fun p => .app p.1 p.2)) →
    Room s (3 * P.length + 1) →
    sorts.seed_loop l s ⦃ s' =>
      Inv s' ∧ s'.nodes.val = s.nodes.val ∧ s'.ticks.val ≤ s.ticks.val + 3 * P.length + 1 ∧
        s.ticks.val ≤ s'.ticks.val ∧ tbl s' .B = tbl s .B ∧
        (∀ k v, tbl s' .A k = some v → tbl s .A k = some v ∨
          ∃ p ∈ P, Repr nm s.nodes.val k p.1 ∧ Repr nm s.nodes.val v p.2) ∧
        (∀ k, tbl s .A k ≠ none → tbl s' .A k ≠ none) ∧
        ∀ p ∈ P, ∀ k, Repr nm s.nodes.val k p.1 → tbl s' .A k ≠ none ⦄ := by
  intro P
  induction P with
  | nil =>
    intro s l hI hl hroom
    have hroom' := hroom
    unfold Room at hroom'
    unfold sorts.seed_loop
    rw [loop]
    simp only [sorts.seed_loop.body]
    step with uncons_repr s l hI.toWf (p := Term.sym (nm none)) hl (by unfold Room; omega)
      as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    subst hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    simp only [uncurry, bind_ok, WP.spec_ok]
    refine ⟨K1.inv, K1.nodes, by simp only [List.length_nil]; omega, by omega, by rw [K1.tbl],
      fun k v h => .inl (by rw [K1.tbl] at h; exact h), fun k h => by rw [K1.tbl]; exact h,
      fun p hp => by cases hp⟩
  | cons p0 P ih =>
    intro s l hI hl hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons] at hroom'
    unfold sorts.seed_loop
    rw [loop]
    simp only [sorts.seed_loop.body]
    step with uncons_repr s l hI.toWf
      (p := Term.app (.app p0.1 p0.2) (encList (nm none) (P.map fun p => .app p.1 p.2))) hl
      (by unfold Room; omega) as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    obtain ⟨p1, rest, rfl, rp1, rrest⟩ := hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    step with uncons_repr s1 p1 K1.inv.toWf (p := Term.app p0.1 p0.2)
      (by rw [K1.nodes]; exact rp1) (by unfold Room; omega) as ⟨r1, hK1, hu1⟩
    obtain ⟨o1, s2⟩ := r1
    simp only at hu1
    simp only at hK1
    obtain ⟨u, w, rfl, ru, rw'⟩ := hu1
    rw [K1.nodes] at ru rw'
    have K2 := hK1.kept K1.inv
    have ht2 := K2.ticks
    have hn2 : s2.nodes.val = s.nodes.val := by rw [K2.nodes, K1.nodes]
    step with set_spec s2 .A u w K2.inv (by rw [hn2]; exact ru.lt) (by unfold Room; omega)
      as ⟨s3, g1, g2, hI3, gA, gO⟩
    have hn3 : s3.nodes.val = s.nodes.val := by rw [g1, hn2]
    have hA2 : tbl s2 = tbl s := by rw [K2.tbl, K1.tbl]
    simp only [uncurry]
    have IH := ih s3 rest hI3 (by rw [hn3]; exact rrest) (by unfold Room; omega)
    unfold sorts.seed_loop at IH
    refine WP.spec_mono IH ?_
    rintro s' ⟨hI', hn', ht', hm', hB', h1, h2, h3⟩
    rw [hn3] at h1 h3
    rw [gA, hA2] at h1 h2
    refine ⟨hI', by rw [hn', hn3], by simp only [List.length_cons]; omega, by omega,
      by rw [hB', gO .B (by simp), hA2], fun k v hk => ?_, fun k hk => ?_, fun p hp k hk => ?_⟩
    · rcases h1 k v hk with h | ⟨p, hp, hk1, hk2⟩
      · by_cases e : k = u.val
        · subst e
          simp only [Function.update_self, Option.some.injEq] at h
          subst h
          exact .inr ⟨p0, List.mem_cons_self, ru, rw'⟩
        · rw [Function.update_of_ne e] at h
          exact .inl h
      · exact .inr ⟨p, List.mem_cons_of_mem _ hp, hk1, hk2⟩
    · refine h2 k ?_
      by_cases e : k = u.val
      · subst e; simp
      · rw [Function.update_of_ne e]; exact hk
    · rcases List.mem_cons.1 hp with rfl | hp
      · refine h2 k ?_
        have e : k = u.val := Repr.inj hnm hI.nodesOK hk ru
        subst e
        simp
      · exact h3 p hp k hk

/-- `seed` leaves in table `A` an entry with the second of a pair for the
first of each pair, and nothing else. -/
theorem seed_spec (hnm : Function.Injective nm) (P : List (Pat × Pat)) (s : store.Store)
    (l : store.TermId) (hI : Inv s)
    (hl : Repr nm s.nodes.val l.val (encList (nm none) (P.map fun p => .app p.1 p.2)))
    (hroom : Room s (3 * P.length + 2)) :
    sorts.seed s l ⦃ s' =>
      Inv s' ∧ s'.nodes.val = s.nodes.val ∧ s'.ticks.val ≤ s.ticks.val + 3 * P.length + 2 ∧
        s.ticks.val ≤ s'.ticks.val ∧ tbl s' .B = tbl s .B ∧
        (∀ k v, tbl s' .A k = some v →
          ∃ p ∈ P, Repr nm s.nodes.val k p.1 ∧ Repr nm s.nodes.val v p.2) ∧
        ∀ p ∈ P, ∀ k, Repr nm s.nodes.val k p.1 → tbl s' .A k ≠ none ⦄ := by
  unfold sorts.seed
  have hroom' := hroom
  unfold Room at hroom'
  step with clear_spec s .A hI (by unfold Room; omega) as ⟨s1, c1, c2, hI1, c4, c5⟩
  refine WP.spec_mono (seed_loop_spec hnm P s1 l hI1 (by rw [c1]; exact hl)
    (by unfold Room; omega)) ?_
  rintro s' ⟨hI', hn', ht', hm', hB', h1, -, h3⟩
  rw [c1] at h1 h3
  refine ⟨hI', by rw [hn', c1], by omega, by omega, by rw [hB', c5 .B (by simp)],
    fun k v hk => ?_, h3⟩
  rcases h1 k v hk with h | h
  · rw [c4 k] at h; cases h
  · exact h

/-! ## The conjunctions of a list of variables -/

theorem conjs_at_loop_spec {U : List Name} (L : List (Nat × Sorts.Conj)) :
    ∀ (K : List Nat) (s : store.Store) (l es out : store.TermId) (O : List Pat), Inv s →
    Repr nm s.nodes.val l.val (encList (nm none) (K.map Term.var)) →
    Repr nm s.nodes.val es.val (encVarEntries nm U L) →
    Repr nm s.nodes.val out.val (encList (nm none) O) →
    Room s (K.length * (3 * L.length + 4) + 1) →
    sorts.conjs_at_loop l s es out ⦃ s' r =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + K.length * (3 * L.length + 4) + 1 ∧
        Repr nm s'.nodes.val r.val
          (encList (nm none) ((K.map fun k => cpat (nm none) U (conjOf L k)).reverse ++ O)) ⦄ := by
  intro K
  induction K with
  | nil =>
    intro s l es out O hI hl hes ho hroom
    have hroom' := hroom
    unfold Room at hroom'
    unfold sorts.conjs_at_loop
    rw [loop]
    simp only [sorts.conjs_at_loop.body]
    step with uncons_repr s l hI.toWf (p := Term.sym (nm none)) hl (by unfold Room; omega)
      as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    subst hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    simp only [uncurry, bind_ok, WP.spec_ok]
    exact ⟨K1.inv, Extends.of_eq K1.nodes (by omega), by simp only [List.length_nil]; omega,
      by rw [K1.nodes]; simpa using ho⟩
  | cons k0 K ih =>
    intro s l es out O hI hl hes ho hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at hroom'
    unfold sorts.conjs_at_loop
    rw [loop]
    simp only [sorts.conjs_at_loop.body]
    step with uncons_repr s l hI.toWf
      (p := Term.app (.var k0) (encList (nm none) (K.map Term.var))) hl
      (by unfold Room; omega) as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    obtain ⟨v, rest, rfl, rv, rrest⟩ := hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    have hx1 : Extends s s1 := Extends.of_eq K1.nodes (by omega)
    have hvar : VarAt s1.nodes.val v.val k0 := by
      have := hx1.repr rv
      cases this with
      | var h => exact h
    step with conj_at_spec s1 es v L K1.inv hvar (hx1.repr hes) (by unfold Room; omega)
      as ⟨r1, hI2, hx2, ht2, rc⟩
    obtain ⟨c, s2⟩ := r1
    simp only at hI2 hx2 ht2 rc
    have hx02 : Extends s s2 := hx1.trans hx2
    step with alloc_spec s2 (.App c out) hI2 ⟨rc.lt, (hx02.repr ho).lt⟩
      (by unfold Room; omega) as ⟨r2, hI3, ht3, htb3, hx3, hid3⟩
    obtain ⟨out1, s3⟩ := r2
    simp only [norm] at hI3 ht3 htb3 hx3 hid3
    have hx03 : Extends s s3 := hx02.trans hx3
    have ro : Repr nm s3.nodes.val out1.val
        (encList (nm none) (cpat (nm none) U (conjOf L k0) :: O)) :=
      .app hid3 (hx3.repr rc) (hx03.repr ho)
    simp only [uncurry, bind_ok]
    have IH := ih s3 rest es out1 (cpat (nm none) U (conjOf L k0) :: O) hI3 (hx03.repr rrest)
      (hx03.repr hes) ro (by unfold Room; omega)
    unfold sorts.conjs_at_loop at IH
    refine WP.spec_mono IH ?_
    rintro ⟨s', res⟩ ⟨hI', hx', ht', hres'⟩
    refine ⟨hI', hx03.trans hx', ?_, ?_⟩
    · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega
    · simpa using hres'

/-- The ticks `conjs_at` may take. -/
def conjsAtCost (k l : Nat) : Nat := k * (3 * l + 4) + 2 * k + 4

/-- `conjs_at` lists the conjunctions the entries give the variables of a
list. -/
theorem conjs_at_spec {U : List Name} (L : List (Nat × Sorts.Conj)) (K : List Nat)
    (s : store.Store) (es l : store.TermId) (hI : Inv s)
    (hes : Repr nm s.nodes.val es.val (encVarEntries nm U L))
    (hl : Repr nm s.nodes.val l.val (encList (nm none) (K.map Term.var)))
    (hroom : Room s (conjsAtCost K.length L.length)) :
    sorts.conjs_at s es l ⦃ r s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + conjsAtCost K.length L.length ∧
        Repr nm s'.nodes.val r.val
          (encList (nm none) (K.map fun k => cpat (nm none) U (conjOf L k))) ⦄ := by
  unfold sorts.conjs_at
  have hroom' := hroom
  unfold Room conjsAtCost at hroom'
  step with alloc_spec s .Nil hI trivial (by unfold Room; omega)
    as ⟨out, s1, hI1, ht1, htb1, hx1, hr1⟩
  simp only [norm] at hr1
  step with conjs_at_loop_spec (U := U) L K s1 l es out [] hI1 (hx1.repr hl) (hx1.repr hes)
    (.nil hr1) (by unfold Room; omega) as ⟨s2, out1, hI2, hx2, ht2, ro⟩
  rw [List.append_nil] at ro
  have hlen : (K.map fun k => cpat (nm none) U (conjOf L k)).reverse.length = K.length := by simp
  refine WP.spec_mono (rev_spec (nm := nm) _ s2 out1 hI2.toWf ro
    (by rw [hlen]; unfold Room; omega)) ?_
  rintro ⟨r, s'⟩ ⟨hR, hr⟩
  rw [hlen] at hR
  have ht3 := hR.ticks
  refine ⟨⟨hR.wf, by rw [hR.stk]; exact hI2.empty⟩, (hx1.trans hx2).trans hR.ext, ?_, ?_⟩
  · unfold conjsAtCost; omega
  · simpa using hr

/-! ## The equations of the exclusions -/

/-- The equations a list of values has for the variables it gives a value
other than themselves. -/
def movedVals (B : List Pat) : Eqns Nat := movedOf ((List.range B.length).zip B)

theorem moved_all_loop_spec (hnm : Function.Injective nm) (n : Nat) :
    ∀ (Ys : List (List Pat)) (s : store.Store) (xs vs out : store.TermId) (O : List Pat),
    Inv s → (∀ B ∈ Ys, B.length = n) →
    Repr nm s.nodes.val xs.val (encLL nm Ys) →
    Repr nm s.nodes.val vs.val (encList (nm none) (varsTo n)) →
    Repr nm s.nodes.val out.val (encList (nm none) O) →
    Room s (Ys.length * (7 * n + 6) + 1) →
    sorts.moved_all_loop xs s vs out ⦃ r s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + Ys.length * (7 * n + 6) + 1 ∧
        Repr nm s'.nodes.val r.val
          (encList (nm none) ((Ys.map fun B => encEqs nm (movedVals B)).reverse ++ O)) ⦄ := by
  intro Ys
  induction Ys with
  | nil =>
    intro s xs vs out O hI hlen hx hvs ho hroom
    have hroom' := hroom
    unfold Room at hroom'
    unfold sorts.moved_all_loop
    rw [loop]
    simp only [sorts.moved_all_loop.body]
    step with uncons_repr s xs hI.toWf (p := Term.sym (nm none)) hx (by unfold Room; omega)
      as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    subst hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    simp only [uncurry, bind_ok, WP.spec_ok]
    exact ⟨K1.inv, Extends.of_eq K1.nodes (by omega), by simp only [List.length_nil]; omega,
      by rw [K1.nodes]; simpa using ho⟩
  | cons B Ys ih =>
    intro s xs vs out O hI hlen hx hvs ho hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at hroom'
    have hBn : B.length = n := hlen B List.mem_cons_self
    unfold sorts.moved_all_loop
    rw [loop]
    simp only [sorts.moved_all_loop.body]
    step with uncons_repr s xs hI.toWf
      (p := Term.app (encList (nm none) B) (encLL nm Ys)) hx
      (by unfold Room; omega) as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    obtain ⟨vals, rest, rfl, rvals, rrest⟩ := hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    have hx1 : Extends s s1 := Extends.of_eq K1.nodes (by omega)
    have hzl : ((List.range B.length).zip B).length = n := by simp [hBn]
    have e1 : ((List.range B.length).zip B).map (fun q => Term.var q.1) = varsTo n := by
      rw [← hBn]
      unfold varsTo
      have : ((List.range B.length).zip B).map Prod.fst = List.range B.length := by
        rw [← List.unzip_fst, List.unzip_zip (by simp)]
      conv_rhs => rw [← this]
      rw [List.map_map]
      rfl
    have e2 : ((List.range B.length).zip B).map Prod.snd = B := by
      rw [← List.unzip_snd, List.unzip_zip (by simp)]
    step with moved_spec hnm ((List.range B.length).zip B) s1 vs vals K1.inv
      (by rw [e1]; exact hx1.repr hvs) (by rw [e2]; exact hx1.repr rvals)
      (by rw [hzl]; unfold Room; omega) as ⟨r1, hI2, hx2, ht2, rm⟩
    obtain ⟨m, s2⟩ := r1
    simp only at hI2 hx2 ht2 rm
    rw [hzl] at ht2
    have hx02 : Extends s s2 := hx1.trans hx2
    step with alloc_spec s2 (.App m out) hI2 ⟨rm.lt, (hx02.repr ho).lt⟩
      (by unfold Room; omega) as ⟨r2, hI3, ht3, htb3, hx3, hid3⟩
    obtain ⟨out1, s3⟩ := r2
    simp only [norm] at hI3 ht3 htb3 hx3 hid3
    have hx03 : Extends s s3 := hx02.trans hx3
    have ro : Repr nm s3.nodes.val out1.val
        (encList (nm none) (encEqs nm (movedVals B) :: O)) :=
      .app hid3 (hx3.repr rm) (hx03.repr ho)
    simp only [uncurry, bind_ok]
    have IH := ih s3 rest vs out1 (encEqs nm (movedVals B) :: O) hI3
      (fun B' hB' => hlen B' (List.mem_cons_of_mem _ hB')) (hx03.repr rrest) (hx03.repr hvs) ro
      (by unfold Room; omega)
    unfold sorts.moved_all_loop at IH
    refine WP.spec_mono IH ?_
    rintro ⟨res, s'⟩ ⟨hI', hx', ht', hres'⟩
    refine ⟨hI', hx03.trans hx', ?_, ?_⟩
    · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega
    · simpa using hres'

/-- The ticks `moved_all` may take. -/
def movedAllCost (n y : Nat) : Nat := y * (7 * n + 6) + 2

/-- `moved_all` reads the equations of each exclusion back from its list of
values; the first exclusion comes last. -/
theorem moved_all_spec (hnm : Function.Injective nm) (n : Nat) (Ys : List (List Pat))
    (s : store.Store) (vs xs : store.TermId) (hI : Inv s) (hlen : ∀ B ∈ Ys, B.length = n)
    (hvs : Repr nm s.nodes.val vs.val (encList (nm none) (varsTo n)))
    (hx : Repr nm s.nodes.val xs.val (encLL nm Ys))
    (hroom : Room s (movedAllCost n Ys.length)) :
    sorts.moved_all s vs xs ⦃ r s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + movedAllCost n Ys.length ∧
        Repr nm s'.nodes.val r.val (encX nm (Ys.reverse.map movedVals)) ⦄ := by
  unfold sorts.moved_all
  have hroom' := hroom
  unfold Room movedAllCost at hroom'
  step with alloc_spec s .Nil hI trivial (by unfold Room; omega)
    as ⟨out, s1, hI1, ht1, htb1, hx1, hr1⟩
  simp only [norm] at hr1
  refine WP.spec_mono (moved_all_loop_spec hnm n Ys s1 xs vs out [] hI1 hlen (hx1.repr hx)
    (hx1.repr hvs) (.nil hr1) (by unfold Room; omega)) ?_
  rintro ⟨r, s'⟩ ⟨hI', hx', ht', hr⟩
  refine ⟨hI', hx1.trans hx', by unfold movedAllCost; omega, ?_⟩
  simpa [encX, List.map_reverse, Function.comp_def] using hr

end RwLogVerified
