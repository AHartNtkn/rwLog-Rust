/-
# The sorts of a subterm

`sorts::sorts_of` returns the conjunction of the declared sorts that hold of
every instance of a first-order pattern with its variables in the
conjunctions a list of entries gives them: for each name, the sort is pushed
down the pattern, and the name is kept when every atom reached is a sort its
variable has. This is `Sorts.clo` of the specification: `push_sort` returns
nothing exactly when `Sorts.push` does, and otherwise its atoms are the
atoms of `Sorts.push` (`push_comes`).
-/
import RwLogVerified.Among
import RwLogVerified.PushComes
import RwLogVerified.Number

open Aeneas Aeneas.Std Result

namespace RwLogVerified

open rwlog_core RwLog

variable {nm : Option Nat → Sym}

theorem conjList_length_le (U : List Name) (F : Name → Prop) :
    (conjList U F).length ≤ U.length := by
  unfold conjList
  rw [List.length_reverse]
  exact List.length_filter_le _ _

/-- The ticks one atom may take. -/
def atomCost (U : List Name) (L : List (Nat × Sorts.Conj)) : Nat :=
  3 * L.length + 2 * U.length + 5

/-- `atoms_hold` answers whether every atom of the list is a sort the
entries give its variable. -/
theorem atoms_hold_loop_spec (hnm : Function.Injective nm) {U : List Name}
    (L : List (Nat × Sorts.Conj)) :
    ∀ (A : Sorts.Atoms) (s : store.Store) (es l : store.TermId), Inv s →
    Repr nm s.nodes.val es.val (encVarEntries nm U L) →
    Repr nm s.nodes.val l.val (encList (nm none) (A.map atomPat)) → (∀ a ∈ A, a.2 ∈ U) →
    Room s (A.length * atomCost U L + 1) →
    sorts.atoms_hold_loop s es true l true ⦃ b s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + A.length * atomCost U L + 1 ∧
        (b = true ↔ ∀ a ∈ A, a.2 ∈ conjOf L a.1) ⦄ := by
  intro A
  induction A with
  | nil =>
    intro s es l hI hes hl hU hroom
    have hroom' := hroom
    unfold Room at hroom'
    unfold sorts.atoms_hold_loop
    rw [loop]
    simp only [sorts.atoms_hold_loop.body, ↓reduceIte]
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
    exact ⟨K1.inv, Extends.of_eq K1.nodes (by omega), by simp only [List.length_nil]; omega,
      by simp⟩
  | cons a A ih =>
    intro s es l hI hes hl hU hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at hroom'
    have hac : atomCost U L = 3 * L.length + 2 * U.length + 5 := rfl
    unfold sorts.atoms_hold_loop
    rw [loop]
    simp only [sorts.atoms_hold_loop.body, ↓reduceIte]
    step with uncons_repr s l hI.toWf (p := Term.app (atomPat a) (encList (nm none) (A.map atomPat)))
      hl (by unfold Room; omega) as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    obtain ⟨ai, rest, rfl, ra, rrest⟩ := hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    step with uncons_repr s1 ai K1.inv.toWf (p := Term.app (.var a.1) (.sym a.2))
      (by rw [K1.nodes]; exact ra) (by unfold Room; omega) as ⟨r1, hK1, hu1⟩
    obtain ⟨o1, s2⟩ := r1
    simp only at hu1
    simp only at hK1
    obtain ⟨v, n, rfl, rv, rn⟩ := hu1
    have K2 := hK1.kept K1.inv
    have ht2 := K2.ticks
    have hn2 : s2.nodes.val = s.nodes.val := by rw [K2.nodes, K1.nodes]
    have hx2 : Extends s s2 := Extends.of_eq hn2 (by omega)
    have hv : VarAt s2.nodes.val v.val a.1 := by
      rw [K2.nodes]
      cases rv with
      | var h => exact h
    step with conj_at_spec s2 es v L K2.inv hv (hx2.repr hes) (by unfold Room; omega)
      as ⟨r2, hI3, hx3, ht3, rc⟩
    obtain ⟨c, s3⟩ := r2
    simp only at hI3 hx3 ht3 rc
    have hlen := conjList_length_le U (· ∈ conjOf L a.1)
    unfold cpat namesPat at rc
    step with among_spec hnm ((conjList U (· ∈ conjOf L a.1)).map fun n => (.sym n : Pat)) s3 n c
      (tn := .sym a.2) hI3 ((hx2.trans hx3).repr (by rw [K1.nodes] at rn; exact rn)) rc
      (by simp only [List.length_map]; unfold Room; omega) as ⟨r3, hI4, hn4, htb4, ht4, hm4, hres⟩
    obtain ⟨b, s4⟩ := r3
    simp only [List.length_map] at hI4 hn4 htb4 ht4 hm4 hres
    have hx4 : Extends s s4 := (hx2.trans hx3).trans (Extends.of_eq hn4 hm4)
    have hin : (Term.sym a.2 : Pat) ∈ (conjList U (· ∈ conjOf L a.1)).map (fun n => (.sym n : Pat))
        ↔ a.2 ∈ conjOf L a.1 := by
      simp only [List.mem_map, Term.sym.injEq, exists_eq_right, mem_conjList]
      exact ⟨fun h => h.2, fun h => ⟨hU a List.mem_cons_self, h⟩⟩
    by_cases hmem : a.2 ∈ conjOf L a.1
    · have hb : b = true := by rw [hres]; simpa using hin.2 hmem
      subst hb
      simp only [↓reduceIte, uncurry, bind_ok]
      have IH := ih s4 es rest hI4 (hx4.repr hes) (hx4.repr rrest)
        (fun a' ha' => hU a' (List.mem_cons_of_mem _ ha')) (by unfold Room; omega)
      unfold sorts.atoms_hold_loop at IH
      refine WP.spec_mono IH ?_
      rintro ⟨res, s'⟩ ⟨hI', hx', ht', hres'⟩
      refine ⟨hI', hx4.trans hx', by
        simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega, ?_⟩
      rw [hres']
      simp [hmem]
    · have hb : b = false := by
        rw [hres]
        simpa using fun h => hmem (hin.1 h)
      subst hb
      simp only [Bool.false_eq_true, ↓reduceIte, uncurry, bind_ok]
      rw [loop]
      simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, WP.spec_ok]
      refine ⟨hI4, hx4, by simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega, ?_⟩
      simp only [Bool.false_eq_true, false_iff]
      exact fun h => hmem (h a List.mem_cons_self)

/-- A declared sort holds of the instances of the pattern with its variables
in the conjunctions of the entries: its push-down is within them. -/
def CloAt (S : Sorts) (L : List (Nat × Sorts.Conj)) (u : Pat) (n : Name) : Prop :=
  ∃ ats, Sorts.push S n u = some ats ∧ ∀ a ∈ ats, a.2 ∈ conjOf L a.1

/-- The ticks one name may take in `sorts_of`. -/
noncomputable def cloStep (S : Sorts) (U : List Name) (L : List (Nat × Sorts.Conj))
    (u : Pat) : Nat :=
  pushCost S U.toFinset u + U.length * u.subs.card * atomCost U L + 3

theorem clo_atoms_length_le {U : List Name} {u : Pat} {A : Sorts.Atoms} (hnd : A.Nodup)
    (hA : ∀ a ∈ A, a.2 ∈ U.toFinset ∧ Term.var a.1 ∈ u.subs) :
    A.length ≤ U.length * u.subs.card := by
  have h1 : A.length = A.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
  have h2 : A.toFinset.card ≤ (U.toFinset ×ˢ u.subs).card := by
    refine Finset.card_le_card_of_injOn (fun a => (a.2, (Term.var a.1 : Pat))) ?_ ?_
    · intro a ha
      have := hA a (List.mem_toFinset.1 (Finset.mem_coe.1 ha))
      exact Finset.mem_coe.2 (Finset.mem_product.2 this)
    · rintro ⟨x, m⟩ - ⟨y, m'⟩ - h
      simp only [Prod.mk.injEq, Term.var.injEq] at h
      rw [h.1, h.2]
  rw [Finset.card_product] at h2
  have h3 := List.toFinset_card_le U
  have h4 : U.toFinset.card * u.subs.card ≤ U.length * u.subs.card :=
    Nat.mul_le_mul_right _ h3
  omega

theorem sorts_of_loop_spec (hnm : Function.Injective nm) (S : Sorts) {sp : Pat}
    (hS : SortsAt (nm none) S sp) {U : List Name}
    (hNs : ∀ m ∈ U, ∀ f k ks, Sorts.step S m f k = some ks →
      ∀ m', some m' ∈ ks → m' ∈ U ∧ m' ≠ nm none)
    (L : List (Nat × Sorts.Conj)) (u : Pat) (hfo : u.firstOrder = true) :
    ∀ (ns : List Name) (s : store.Store) (names decls es ui out : store.TermId)
      (acc : List Name), Inv s →
    Repr nm s.nodes.val names.val (namesPat (nm none) ns) → (∀ n ∈ ns, n ∈ U) →
    Repr nm s.nodes.val decls.val sp → Repr nm s.nodes.val es.val (encVarEntries nm U L) →
    Repr nm s.nodes.val ui.val u → Repr nm s.nodes.val out.val (namesPat (nm none) acc) →
    Room s (ns.length * cloStep S U L u + 1) →
    sorts.sorts_of_loop names s decls es ui out ⦃ r s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + ns.length * cloStep S U L u + 1 ∧
        Repr nm s'.nodes.val r.val (namesPat (nm none) (conjList ns (CloAt S L u) ++ acc)) ⦄ := by
  intro ns
  induction ns with
  | nil =>
    intro s names decls es ui out acc hI hl hU hd hes hu ho hroom
    have hroom' := hroom
    unfold Room at hroom'
    unfold sorts.sorts_of_loop
    rw [loop]
    simp only [sorts.sorts_of_loop.body]
    step with uncons_repr s names hI.toWf (p := Term.sym (nm none)) hl (by unfold Room; omega)
      as ⟨r0, hK0, hu0⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu0
    simp only at hK0
    subst hu0
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    simp only [uncurry, bind_ok, WP.spec_ok]
    exact ⟨K1.inv, Extends.of_eq K1.nodes (by omega), by simp only [List.length_nil]; omega,
      by rw [K1.nodes]; simpa [conjList_nil] using ho⟩
  | cons x ns ih =>
    intro s names decls es ui out acc hI hl hU hd hes hu ho hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at hroom'
    have hcs : cloStep S U L u =
        pushCost S U.toFinset u + U.length * u.subs.card * atomCost U L + 3 := rfl
    have hxU : x ∈ U := hU x List.mem_cons_self
    have hU' : ∀ n ∈ ns, n ∈ U := fun n hn => hU n (List.mem_cons_of_mem _ hn)
    unfold sorts.sorts_of_loop
    rw [loop]
    simp only [sorts.sorts_of_loop.body]
    unfold namesPat at hl
    step with uncons_repr s names hI.toWf
      (p := Term.app (.sym x) (encList (nm none) (ns.map fun n => (.sym n : Pat)))) hl
      (by unfold Room; omega) as ⟨r0, hK0, hu0⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu0
    simp only at hK0
    obtain ⟨n, rest, rfl, rn, rrest⟩ := hu0
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    have hx1 : Extends s s1 := Extends.of_eq K1.nodes (by omega)
    step with push_sort_exact hnm S hS U.toFinset u hfo (List.mem_toFinset.2 hxU)
      (fun m hm f k ks hs m' hm' => by
        obtain ⟨h1, h2⟩ := hNs m (List.mem_toFinset.1 hm) f k ks hs m' hm'
        exact ⟨List.mem_toFinset.2 h1, h2⟩)
      s1 decls n ui K1.inv (hx1.repr hd) (hx1.repr rn) (hx1.repr hu) (by unfold Room; omega)
      as ⟨r1, hI2, hx2, _, ht2, hpost⟩
    obtain ⟨o1, s2⟩ := r1
    simp only at hI2 hx2 ht2 hpost
    have hx02 : Extends s s2 := hx1.trans hx2
    have hpc := (push_comes (S := S) u.size u x (Nat.le_refl _) hfo)
    cases o1 with
    | none =>
      simp only at hpost
      have hnF : ¬ CloAt S L u x := by
        rintro ⟨ats, hp, -⟩
        exact (hpc.1 ats hp).2 hpost.2
      simp only [uncurry, bind_ok]
      have IH := ih s2 rest decls es ui out acc hI2 (hx02.repr rrest) hU' (hx02.repr hd)
        (hx02.repr hes) (hx02.repr hu) (hx02.repr ho) (by unfold Room; omega)
      unfold sorts.sorts_of_loop at IH
      refine WP.spec_mono IH ?_
      rintro ⟨res, s'⟩ ⟨hI', hx', ht', hres'⟩
      refine ⟨hI', hx02.trans hx', by
        simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega, ?_⟩
      rw [conjList_cons_neg hnF]
      exact hres'
    | some atoms =>
      simp only at hpost
      obtain ⟨A, rA, hAn, hAU, hAC, -, hnf⟩ := hpost
      have hAlen := clo_atoms_length_le hAn hAU
      have hAc : A.length * atomCost U L ≤ U.length * u.subs.card * atomCost U L :=
        Nat.mul_le_mul_right _ hAlen
      step with atoms_hold_loop_spec hnm L A s2 es atoms hI2 (hx02.repr hes) rA
        (fun a ha => List.mem_toFinset.1 (hAU a ha).1) (by unfold Room; omega)
        as ⟨r2, hI3, hx3, ht3, hb⟩
      obtain ⟨b, s3⟩ := r2
      simp only at hI3 hx3 ht3 hb
      have hx03 : Extends s s3 := hx02.trans hx3
      have hF : CloAt S L u x ↔ ∀ a ∈ A, a.2 ∈ conjOf L a.1 := by
        cases hp : Sorts.push S x u with
        | none => exact absurd (hpc.2 hp) hnf
        | some ats =>
          have hm := (hpc.1 ats hp).1
          constructor
          · rintro ⟨ats', hp', h⟩ a ha
            rw [hp] at hp'
            cases hp'
            exact h a ((hm a).2 ((hAC a).1 ha))
          · intro h
            exact ⟨ats, hp, fun a ha => h a ((hAC a).2 ((hm a).1 ha))⟩
      by_cases hbt : b = true
      · subst hbt
        have hFx : CloAt S L u x := hF.2 (hb.1 rfl)
        simp only [uncurry, ↓reduceIte]
        step with alloc_spec s3 (.App n out) hI3 ⟨(hx03.repr rn).lt, (hx03.repr ho).lt⟩
          (by unfold Room; omega) as ⟨r3, hI4, ht4, htb4, hx4, hid⟩
        obtain ⟨out1, s4⟩ := r3
        simp only [norm] at hI4 ht4 htb4 hx4 hid
        simp only [uncurry, bind_ok]
        have hx04 : Extends s s4 := hx03.trans hx4
        have hout1 : Repr nm s4.nodes.val out1.val (namesPat (nm none) (x :: acc)) :=
          .app hid (hx04.repr rn) (hx04.repr ho)
        have IH := ih s4 rest decls es ui out1 (x :: acc) hI4 (hx04.repr rrest) hU'
          (hx04.repr hd) (hx04.repr hes) (hx04.repr hu) hout1 (by unfold Room; omega)
        unfold sorts.sorts_of_loop at IH
        refine WP.spec_mono IH ?_
        rintro ⟨res, s'⟩ ⟨hI', hx', ht', hres'⟩
        refine ⟨hI', hx04.trans hx', by
          simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega, ?_⟩
        have e : conjList (x :: ns) (CloAt S L u) ++ acc = conjList ns (CloAt S L u) ++ x :: acc := by
          simp [conjList_cons_pos hFx]
        rw [e]
        exact hres'
      · have hbf : b = false := by cases b <;> simp_all
        subst hbf
        have hnF : ¬ CloAt S L u x := fun h => by
          have := hb.2 (hF.1 h)
          cases this
        simp only [uncurry, Bool.false_eq_true, ↓reduceIte, bind_ok]
        have IH := ih s3 rest decls es ui out acc hI3 (hx03.repr rrest) hU' (hx03.repr hd)
          (hx03.repr hes) (hx03.repr hu) (hx03.repr ho) (by unfold Room; omega)
        unfold sorts.sorts_of_loop at IH
        refine WP.spec_mono IH ?_
        rintro ⟨res, s'⟩ ⟨hI', hx', ht', hres'⟩
        refine ⟨hI', hx03.trans hx', by
          simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega, ?_⟩
        rw [conjList_cons_neg hnF]
        exact hres'

/-- The ticks `sorts_of` may take. -/
noncomputable def cloCost (S : Sorts) (U : List Name) (L : List (Nat × Sorts.Conj))
    (u : Pat) : Nat :=
  U.length * cloStep S U L u + 2

/-- `sorts_of` returns the conjunction of the names whose push-down on the
pattern is within the conjunctions of the entries. -/
theorem sorts_of_spec (hnm : Function.Injective nm) (S : Sorts) {sp : Pat}
    (hS : SortsAt (nm none) S sp) {U : List Name}
    (hNs : ∀ m ∈ U, ∀ f k ks, Sorts.step S m f k = some ks →
      ∀ m', some m' ∈ ks → m' ∈ U ∧ m' ≠ nm none)
    (L : List (Nat × Sorts.Conj)) {u : Pat} (hfo : u.firstOrder = true)
    (s : store.Store) (decls names es ui : store.TermId) (hI : Inv s)
    (hd : Repr nm s.nodes.val decls.val sp)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (hes : Repr nm s.nodes.val es.val (encVarEntries nm U L))
    (hu : Repr nm s.nodes.val ui.val u) (hroom : Room s (cloCost S U L u)) :
    sorts.sorts_of s decls names es ui ⦃ r s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + cloCost S U L u ∧
        Repr nm s'.nodes.val r.val (namesPat (nm none) (conjList U (CloAt S L u))) ⦄ := by
  unfold sorts.sorts_of
  have hroom' := hroom
  unfold Room cloCost at hroom'
  step with alloc_spec s .Nil hI trivial (by unfold Room; omega)
    as ⟨out, s1, hI1, ht1, htb1, hx1, hid⟩
  simp only [norm] at hid
  refine WP.spec_mono (sorts_of_loop_spec hnm S hS hNs L u hfo U s1 names decls es ui out [] hI1
    (hx1.repr hU) (fun _ h => h) (hx1.repr hd) (hx1.repr hes) (hx1.repr hu) (.nil hid)
    (by unfold Room; omega)) ?_
  rintro ⟨r, s'⟩ ⟨hI', hx', ht', hr⟩
  refine ⟨hI', hx1.trans hx', by unfold cloCost; omega, ?_⟩
  simpa using hr

end RwLogVerified
