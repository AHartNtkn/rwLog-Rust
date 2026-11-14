/-
# The sorts as the constraint domain, on the store

A representative on the store is a normal store as `sorts::normal` returns
it. Each operation of the domain states a problem with the solutions of its
arguments and takes its normal store: `dom::one` the problem of
`Sorts.Rep.one`, and `dom::compose` and `dom::meet` that of `Sorts.Rep.two`
with the variables of the two arguments sent to the even and to the odd
numbers. A problem with the same solutions has the same normal store
(`Sorts.Rep.den_one`, `Sorts.Rep.den_two`, `Sorts.Prob.norm_congr`).
-/
import RwLogVerified.Normal
import RwLog.Sorts.Dom

open Aeneas Aeneas.Std Result

namespace RwLogVerified

open rwlog_core RwLog

variable {nm : Option Nat → RwLog.Sym}

/-! ## The sorts and the exclusions of a representative, as a problem has them -/

/-- The sorted patterns that say the pattern `v` is in each sort of a list,
in front of a list. -/
def sortedOnto (ns : List Name) (v : Pat) (out : List (Name × Pat)) : List (Name × Pat) :=
  (ns.map fun n => (n, v)).reverse ++ out

/-- The sorted patterns that say each pattern of a list is in each sort of
its conjunction, in front of a list. -/
noncomputable def atomsOnto (U : List Name) :
    List Sorts.Conj → List Pat → List (Name × Pat) → List (Name × Pat)
  | c :: cs, v :: vs, out => atomsOnto U cs vs (sortedOnto (conjList U (· ∈ c)) v out)
  | _, _, out => out

/-- The equations of each variable of a list with its value. -/
def valEqns (vs vals : List Pat) : Eqns Nat := vs.zip vals

/-- Each list of values as the equations of the variables with them, in
front of a list. -/
def exclsOnto (vs : List Pat) (X : List (List Pat)) (out : List (Eqns Nat)) : List (Eqns Nat) :=
  (X.map (valEqns vs)).reverse ++ out

theorem mem_atomsOnto {U : List Name} {a : Name × Pat} :
    ∀ {cs : List Sorts.Conj} {vs : List Pat} {out : List (Name × Pat)},
      a ∈ atomsOnto U cs vs out ↔ a ∈ out ∨
        ∃ (i : Nat) (h : i < cs.length) (h' : i < vs.length), a.2 = vs[i] ∧ a.1 ∈ U ∧ a.1 ∈ cs[i]
  | [], vs, out => by simp [atomsOnto]
  | c :: cs, [], out => by simp [atomsOnto]
  | c :: cs, v :: vs, out => by
    rw [atomsOnto, mem_atomsOnto (cs := cs)]
    simp only [sortedOnto, List.mem_append, List.mem_reverse, List.mem_map, mem_conjList]
    constructor
    · rintro ((⟨n, ⟨hU, hn⟩, rfl⟩ | h) | ⟨i, h, h', e, hU, hn⟩)
      · exact .inr ⟨0, by simp, by simp, rfl, hU, hn⟩
      · exact .inl h
      · exact .inr ⟨i + 1, by simpa using h, by simpa using h', by simpa using e, hU, by simpa using hn⟩
    · rintro (h | ⟨i, h, h', e, hU, hn⟩)
      · exact .inl (.inr h)
      · cases i with
        | zero =>
          refine .inl (.inl ⟨a.1, ⟨hU, by simpa using hn⟩, ?_⟩)
          simp only [List.getElem_cons_zero] at e
          rw [← e]
        | succ i =>
          exact .inr ⟨i, by simpa using h, by simpa using h', by simpa using e, hU, by simpa using hn⟩

/-- The sorts and the exclusions of a normal store, written as a problem
has them and with the variables renamed, hold of a substitution exactly
when it is, on the variables as renamed, a solution of the store. -/
theorem parts_sol {S : Sorts} {U : List Name} (hU : ∀ n ∈ Sorts.names S, n ∈ U) {r : Sorts.Raw}
    (hr : r.Normal S) {Y : List Sorts.Binds} (hY : Y.toFinset = r.x) (f : Nat → Nat)
    (σ : Nat → GTerm) :
    ((∀ a ∈ atomsOnto U r.c ((varsTo r.c.length).map (Term.rename f)) [],
        Sorts.mem S a.1 (a.2.bind σ) = true) ∧
      ∀ E ∈ exclsOnto ((varsTo r.c.length).map (Term.rename f))
        ((Y.map (vals r.c.length)).map (List.map (Term.rename f))) [], ¬ Eqns.Unifies σ E) ↔
      σ ∘ f ∈ r.store.Sol S := by
  rw [← r.sol_shift f σ]
  refine and_congr ?_ ?_
  · constructor
    · intro h a ha
      obtain ⟨v, hv, ha⟩ := List.mem_flatMap.1 ha
      obtain ⟨n, hn, rfl⟩ := List.mem_map.1 ha
      have hv := List.mem_range.1 hv
      have hn := (Finset.mem_sort _).1 hn
      refine h _ (mem_atomsOnto.2 (.inr ⟨v, hv, by simpa using hv, by simp [varsTo, Term.rename],
        hU n (((hr.up v hv n).1 hn).1), ?_⟩))
      simpa [Sorts.Raw.conj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv] using hn
    · intro h a ha
      rcases mem_atomsOnto.1 ha with ha | ⟨v, hv, hv', e, -, hn⟩
      · simp at ha
      · refine h _ (List.mem_flatMap.2 ⟨v, List.mem_range.2 hv, List.mem_map.2 ⟨a.1,
          (Finset.mem_sort _).2 ?_, ?_⟩⟩)
        · simpa [Sorts.Raw.conj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv] using hn
        · ext
          · rfl
          · rw [e]; simp [varsTo, Term.rename]
  · have key : ∀ θ ∈ r.x, Eqns.Unifies σ (valEqns ((varsTo r.c.length).map (Term.rename f))
        ((vals r.c.length θ).map (Term.rename f))) ↔
        Eqns.Unifies σ (Eqns.ren f (Sorts.eqnsOf θ)) := by
      intro θ hθ
      have hpre := (hr.ex θ hθ).toPre
      rw [Sorts.unifies_ren]
      have hall : Eqns.Unifies σ (valEqns ((varsTo r.c.length).map (Term.rename f))
          ((vals r.c.length θ).map (Term.rename f))) ↔
          ∀ i, i < r.c.length → (σ ∘ f) i = (PSubst.apply θ i).bind (σ ∘ f) := by
        unfold Eqns.Unifies valEqns
        constructor
        · intro h i hi
          have := h ((Term.var i : Pat).rename f, (PSubst.apply θ i).rename f) (by
            rw [List.mem_iff_getElem]
            exact ⟨i, by simpa [vals, varsTo] using hi, by simp [vals, varsTo]⟩)
          rw [RwLog.rename_bind, RwLog.rename_bind] at this
          exact this
        · intro h p hp
          obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hp
          have hi' : i < r.c.length := by simpa [vals, varsTo] using hi
          have := h i hi'
          simp only [vals, varsTo, List.getElem_zip, List.getElem_map, List.getElem_range]
          rw [RwLog.rename_bind, RwLog.rename_bind]
          exact this
      rw [hall]
      constructor
      · intro h p hp
        obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hp
        have := h b.1 (hpre.dom b hb)
        rw [Sorts.apply_of_mem hpre.sorted hb] at this
        simpa [Term.bind] using this
      · intro h i _
        by_cases hi : ∀ b ∈ θ, b.1 ≠ i
        · rw [Sorts.apply_of_not_mem hi]; rfl
        · push Not at hi
          obtain ⟨b, hb, rfl⟩ := hi
          rw [Sorts.apply_of_mem hpre.sorted hb]
          have := h (Term.var b.1, b.2) (List.mem_map.2 ⟨b, hb, rfl⟩)
          simpa [Term.bind] using this
    have hmem : ∀ θ, θ ∈ Y ↔ θ ∈ r.x := fun θ => by rw [← hY, List.mem_toFinset]
    constructor
    · intro h E hE hu
      obtain ⟨θ, hθ, rfl⟩ := List.mem_map.1 hE
      have hθ' : θ ∈ r.x := (Finset.mem_sort _).1 hθ
      refine h _ ?_ ((key θ hθ').2 hu)
      simp only [exclsOnto, List.append_nil, List.mem_reverse, List.mem_map]
      exact ⟨_, ⟨_, ⟨θ, (hmem θ).2 hθ', rfl⟩, rfl⟩, rfl⟩
    · intro h E hE hu
      simp only [exclsOnto, List.append_nil, List.mem_reverse, List.mem_map] at hE
      obtain ⟨_, ⟨_, ⟨θ, hθ, rfl⟩, rfl⟩, rfl⟩ := hE
      exact h _ (List.mem_map.2 ⟨θ, (Finset.mem_sort _).2 ((hmem θ).1 hθ), rfl⟩)
        ((key θ ((hmem θ).1 hθ)).1 hu)

/-! ## The sorts and the exclusions written on the store -/

theorem encEqs_eq (E : Eqns Nat) :
    encEqs nm E = encList (nm none) (E.map fun p => Term.app p.1 p.2) := by
  induction E with
  | nil => rfl
  | cons p E ih => simp only [encEqs, List.map_cons, encList, ih]

/-- The loop of `sorted_onto` puts the sorted patterns in front. -/
theorem sorted_onto_loop_spec (v : store.TermId) (vp : Pat) :
    ∀ (ns : List Name) (s : store.Store) (c out : store.TermId) (O : List (Name × Pat)),
    Inv s → Repr nm s.nodes.val c.val (namesPat (nm none) ns) → Repr nm s.nodes.val v.val vp →
    Repr nm s.nodes.val out.val (encList (nm none) (O.map ppair)) →
    Room s (3 * ns.length + 1) →
    dom.sorted_onto_loop c s v out ⦃ out' s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + 3 * ns.length + 1 ∧
        Repr nm s'.nodes.val out'.val
          (encList (nm none) ((sortedOnto ns vp O).map ppair)) ⦄ := by
  intro ns
  induction ns with
  | nil =>
    intro s c out O hI hc hv hout hroom
    have hroom' := hroom
    unfold Room at hroom'
    unfold dom.sorted_onto_loop
    rw [loop]
    simp only [dom.sorted_onto_loop.body]
    step with uncons_repr s c hI.toWf (p := Term.sym (nm none)) hc (by unfold Room; omega)
      as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    subst hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    have hfin : Inv s1 ∧ Extends s s1 ∧
        s1.ticks.val ≤ s.ticks.val + 3 * ([] : List Name).length + 1 ∧
        Repr nm s1.nodes.val out.val
          (encList (nm none) ((sortedOnto [] vp O).map ppair)) :=
      ⟨K1.inv, Extends.of_eq K1.nodes (by omega), by simp only [List.length_nil]; omega,
        by rw [K1.nodes]; simpa [sortedOnto] using hout⟩
    step*
  | cons n ns ih =>
    intro s c out O hI hc hv hout hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons] at hroom'
    unfold dom.sorted_onto_loop
    rw [loop]
    simp only [dom.sorted_onto_loop.body]
    step with uncons_repr s c hI.toWf
      (p := Term.app (Term.sym n) (namesPat (nm none) ns)) hc
      (by unfold Room; omega) as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    obtain ⟨ni, rest, rfl, rn, rrest⟩ := hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    have hx1 : Extends s s1 := Extends.of_eq K1.nodes (by omega)
    step with alloc_spec s1 (.App ni v) K1.inv ⟨(hx1.repr rn).lt, (hx1.repr hv).lt⟩
      (by unfold Room; omega) as ⟨r3, hI3, ht3, htb3, hx3, hr3⟩
    obtain ⟨e, s3⟩ := r3
    simp only [norm] at hI3 ht3 htb3 hx3 hr3
    have hx03 := hx1.trans hx3
    have re : Repr nm s3.nodes.val e.val (ppair (n, vp)) :=
      .app hr3 (hx03.repr rn) (hx03.repr hv)
    step with alloc_spec s3 (.App e out) hI3 ⟨re.lt, (hx03.repr hout).lt⟩
      (by unfold Room; omega) as ⟨r4, hI4, ht4, htb4, hx4, hr4⟩
    obtain ⟨out1, s4⟩ := r4
    simp only [norm] at hI4 ht4 htb4 hx4 hr4
    have hx04 := hx03.trans hx4
    have hout1 : Repr nm s4.nodes.val out1.val
        (encList (nm none) (((n, vp) :: O).map ppair)) :=
      .app hr4 (hx4.repr re) (hx04.repr hout)
    simp only [uncurry, bind_ok]
    have IH := ih s4 rest out1 ((n, vp) :: O) hI4 (hx04.repr rrest) (hx04.repr hv) hout1
      (by unfold Room; omega)
    unfold dom.sorted_onto_loop at IH
    refine WP.spec_mono IH ?_
    rintro ⟨out', s'⟩ ⟨hI', hx', ht', hr'⟩
    refine ⟨hI', hx04.trans hx', by simp only [List.length_cons]; omega, ?_⟩
    simpa [sortedOnto] using hr'

/-- The loop of `atoms_onto` puts the sorted patterns of each variable in
front. -/
theorem atoms_onto_loop_spec (U : List Name) :
    ∀ (Cs : List Sorts.Conj) (s : store.Store) (out cs vs : store.TermId) (Vs : List Pat)
      (O : List (Name × Pat)),
    Inv s → Repr nm s.nodes.val cs.val (encList (nm none) (Cs.map (cpat (nm none) U))) →
    Repr nm s.nodes.val vs.val (encList (nm none) Vs) →
    Repr nm s.nodes.val out.val (encList (nm none) (O.map ppair)) → Cs.length ≤ Vs.length →
    Room s (Cs.length * (3 * U.length + 3) + 1) →
    dom.atoms_onto_loop s out cs vs true ⦃ out' s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + Cs.length * (3 * U.length + 3) + 1 ∧
        Repr nm s'.nodes.val out'.val
          (encList (nm none) ((atomsOnto U Cs Vs O).map ppair)) ⦄ := by
  intro Cs
  induction Cs with
  | nil =>
    intro s out cs vs Vs O hI hcs hvs hout hlen hroom
    have hroom' := hroom
    unfold Room at hroom'
    unfold dom.atoms_onto_loop
    rw [loop]
    simp only [dom.atoms_onto_loop.body, ↓reduceIte]
    step with uncons_repr s cs hI.toWf (p := Term.sym (nm none)) hcs (by unfold Room; omega)
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
    refine ⟨K1.inv, Extends.of_eq K1.nodes (by omega), by simp only [List.length_nil]; omega, ?_⟩
    rw [K1.nodes]
    simpa [atomsOnto] using hout
  | cons c Cs ih =>
    intro s out cs vs Vs O hI hcs hvs hout hlen hroom
    cases Vs with
    | nil => simp at hlen
    | cons vp Vs =>
      have hroom' := hroom
      unfold Room at hroom'
      simp only [List.length_cons, Nat.add_mul] at hroom' hlen
      have hcl := length_conjList_le U (· ∈ c)
      unfold dom.atoms_onto_loop
      rw [loop]
      simp only [dom.atoms_onto_loop.body, ↓reduceIte]
      step with uncons_repr s cs hI.toWf
        (p := Term.app (cpat (nm none) U c) (encList (nm none) (Cs.map (cpat (nm none) U)))) hcs
        (by unfold Room; omega) as ⟨r0, hK0, hu⟩
      obtain ⟨o, s1⟩ := r0
      simp only at hu
      simp only at hK0
      obtain ⟨ci, crest, rfl, rc, rcrest⟩ := hu
      have K1 := hK0.kept hI
      have ht1 := K1.ticks
      step with uncons_repr s1 vs K1.inv.toWf (p := Term.app vp (encList (nm none) Vs))
        (by rw [K1.nodes]; exact hvs) (by unfold Room; omega) as ⟨r1, hK1', hu1⟩
      obtain ⟨o1, s2⟩ := r1
      simp only at hu1
      simp only at hK1'
      obtain ⟨vi, vrest, rfl, rv, rvrest⟩ := hu1
      rw [K1.nodes] at rv rvrest
      have K2 := hK1'.kept K1.inv
      have ht2 := K2.ticks
      have hn2 : s2.nodes.val = s.nodes.val := by rw [K2.nodes, K1.nodes]
      have hx2 : Extends s s2 := Extends.of_eq hn2 (by omega)
      simp only [uncurry]
      step with sorted_onto_loop_spec vi vp (conjList U (· ∈ c)) s2 ci out O K2.inv
        (hx2.repr rc) (hx2.repr rv) (hx2.repr hout) (by unfold Room; omega)
        as ⟨r3, hI3, hx3, ht3, hr3⟩
      obtain ⟨out1, s3⟩ := r3
      simp only at hI3 hx3 ht3 hr3
      have hx03 := hx2.trans hx3
      simp only [uncurry, bind_ok]
      have IH := ih s3 out1 crest vrest Vs _ hI3 (hx03.repr rcrest) (hx03.repr rvrest)
        hr3 (by omega) (by unfold Room; omega)
      unfold dom.atoms_onto_loop at IH
      refine WP.spec_mono IH ?_
      rintro ⟨out', s'⟩ ⟨hI', hx', ht', hr'⟩
      refine ⟨hI', hx03.trans hx', by simp only [List.length_cons, Nat.add_mul]; omega, ?_⟩
      simpa [atomsOnto] using hr'

/-- `atoms_onto` puts in front of a list the sorted patterns that say each
variable is in each sort of its conjunction. -/
theorem atoms_onto_spec (U : List Name) (Cs : List Sorts.Conj) (Vs : List Pat)
    (O : List (Name × Pat)) (s : store.Store) (cs vs out : store.TermId) (hI : Inv s)
    (hcs : Repr nm s.nodes.val cs.val (encList (nm none) (Cs.map (cpat (nm none) U))))
    (hvs : Repr nm s.nodes.val vs.val (encList (nm none) Vs))
    (hout : Repr nm s.nodes.val out.val (encList (nm none) (O.map ppair)))
    (hlen : Cs.length ≤ Vs.length) (hroom : Room s (Cs.length * (3 * U.length + 3) + 1)) :
    dom.atoms_onto s cs vs out ⦃ out' s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + Cs.length * (3 * U.length + 3) + 1 ∧
        Repr nm s'.nodes.val out'.val
          (encList (nm none) ((atomsOnto U Cs Vs O).map ppair)) ⦄ := by
  unfold dom.atoms_onto
  exact atoms_onto_loop_spec U Cs s out cs vs Vs O hI hcs hvs hout hlen hroom

/-- The loop of `eqns_of` puts the equation of each variable with its value
in front. -/
theorem eqns_of_loop_spec :
    ∀ (Vs : List Pat) (s : store.Store) (out vs l : store.TermId) (Ps : List Pat)
      (O : Eqns Nat),
    Inv s → Repr nm s.nodes.val vs.val (encList (nm none) Vs) →
    Repr nm s.nodes.val l.val (encList (nm none) Ps) →
    Repr nm s.nodes.val out.val (encEqs nm O) → Vs.length ≤ Ps.length →
    Room s (4 * Vs.length + 1) →
    dom.eqns_of_loop s out vs l true ⦃ s' out' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + 4 * Vs.length + 1 ∧
        Repr nm s'.nodes.val out'.val (encEqs nm ((Vs.zip Ps).reverse ++ O)) ⦄ := by
  intro Vs
  induction Vs with
  | nil =>
    intro s out vs l Ps O hI hvs hl hout hlen hroom
    have hroom' := hroom
    unfold Room at hroom'
    unfold dom.eqns_of_loop
    rw [loop]
    simp only [dom.eqns_of_loop.body, ↓reduceIte]
    step with uncons_repr s vs hI.toWf (p := Term.sym (nm none)) hvs (by unfold Room; omega)
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
    refine ⟨K1.inv, Extends.of_eq K1.nodes (by omega), by simp only [List.length_nil]; omega, ?_⟩
    rw [K1.nodes]
    simpa using hout
  | cons vp Vs ih =>
    intro s out vs l Ps O hI hvs hl hout hlen hroom
    cases Ps with
    | nil => simp at hlen
    | cons p Ps =>
      have hroom' := hroom
      unfold Room at hroom'
      simp only [List.length_cons] at hroom' hlen
      unfold dom.eqns_of_loop
      rw [loop]
      simp only [dom.eqns_of_loop.body, ↓reduceIte]
      step with uncons_repr s vs hI.toWf (p := Term.app vp (encList (nm none) Vs)) hvs
        (by unfold Room; omega) as ⟨r0, hK0, hu⟩
      obtain ⟨o, s1⟩ := r0
      simp only at hu
      simp only at hK0
      obtain ⟨vi, vrest, rfl, rv, rvrest⟩ := hu
      have K1 := hK0.kept hI
      have ht1 := K1.ticks
      step with uncons_repr s1 l K1.inv.toWf (p := Term.app p (encList (nm none) Ps))
        (by rw [K1.nodes]; exact hl) (by unfold Room; omega) as ⟨r1, hK1', hu1⟩
      obtain ⟨o1, s2⟩ := r1
      simp only at hu1
      simp only at hK1'
      obtain ⟨pi, lrest, rfl, rp, rlrest⟩ := hu1
      rw [K1.nodes] at rp rlrest
      have K2 := hK1'.kept K1.inv
      have ht2 := K2.ticks
      have hn2 : s2.nodes.val = s.nodes.val := by rw [K2.nodes, K1.nodes]
      have hx2 : Extends s s2 := Extends.of_eq hn2 (by omega)
      simp only [uncurry]
      step with alloc_spec s2 (.App vi pi) K2.inv
        ⟨by rw [hn2]; exact rv.lt, by rw [hn2]; exact rp.lt⟩
        (by unfold Room; omega) as ⟨r3, hI3, ht3, htb3, hx3, hr3⟩
      obtain ⟨e, s3⟩ := r3
      simp only [norm] at hI3 ht3 htb3 hx3 hr3
      have hx03 := hx2.trans hx3
      have re : Repr nm s3.nodes.val e.val (Term.app vp p) :=
        .app hr3 (hx03.repr rv) (hx03.repr rp)
      step with alloc_spec s3 (.App e out) hI3 ⟨re.lt, (hx03.repr hout).lt⟩
        (by unfold Room; omega) as ⟨r4, hI4, ht4, htb4, hx4, hr4⟩
      obtain ⟨out1, s4⟩ := r4
      simp only [norm] at hI4 ht4 htb4 hx4 hr4
      have hx04 := hx03.trans hx4
      have hout1 : Repr nm s4.nodes.val out1.val (encEqs nm ((vp, p) :: O)) :=
        .app hr4 (hx4.repr re) (hx04.repr hout)
      simp only [uncurry, bind_ok]
      have IH := ih s4 out1 vrest lrest Ps ((vp, p) :: O) hI4 (hx04.repr rvrest)
        (hx04.repr rlrest) hout1 (by omega) (by unfold Room; omega)
      unfold dom.eqns_of_loop at IH
      refine WP.spec_mono IH ?_
      rintro ⟨s', out'⟩ ⟨hI', hx', ht', hr'⟩
      refine ⟨hI', hx04.trans hx', by simp only [List.length_cons]; omega, ?_⟩
      simpa using hr'

/-- `eqns_of` gives the equations of each variable with its value. -/
theorem eqns_of_spec (Vs Ps : List Pat) (s : store.Store) (vs l : store.TermId) (hI : Inv s)
    (hvs : Repr nm s.nodes.val vs.val (encList (nm none) Vs))
    (hl : Repr nm s.nodes.val l.val (encList (nm none) Ps)) (hlen : Vs.length ≤ Ps.length)
    (hroom : Room s (6 * Vs.length + 3)) :
    dom.eqns_of s vs l ⦃ r s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + 6 * Vs.length + 3 ∧
        Repr nm s'.nodes.val r.val (encEqs nm (valEqns Vs Ps)) ⦄ := by
  unfold dom.eqns_of
  have hroom' := hroom
  unfold Room at hroom'
  step with alloc_spec s .Nil hI trivial (by unfold Room; omega)
    as ⟨nil, s1, hI1, ht1, htb1, hx1, hr1⟩
  simp only [norm] at hr1
  step with eqns_of_loop_spec (nm := nm) Vs s1 nil vs l Ps [] hI1 (hx1.repr hvs) (hx1.repr hl)
    (.nil hr1) hlen (by unfold Room; omega) as ⟨s2, out1, hI2, hx2, ht2, hr2⟩
  simp only [List.append_nil] at hr2
  rw [encEqs_eq] at hr2
  have hlz : (Vs.zip Ps).length ≤ Vs.length := by simp
  refine WP.spec_mono (rev_onto_spec _ [] s2 out1 nil hI2.toWf hr2 (hx2.repr (.nil hr1))
    (by simp only [List.length_map, List.length_reverse]; unfold Room; omega)) ?_
  rintro ⟨r, s'⟩ ⟨hR, hr⟩
  simp only [List.length_map, List.length_reverse] at hR
  have ht3 := hR.ticks
  refine ⟨⟨hR.wf, by rw [hR.stk]; exact hI2.empty⟩, (hx1.trans hx2).trans hR.ext, by omega, ?_⟩
  rw [encEqs_eq]
  simpa [valEqns] using hr

/-- The loop of `excls_onto` puts each exclusion, as equations, in front. -/
theorem excls_onto_loop_spec (Vs : List Pat) (vs : store.TermId) :
    ∀ (Xs : List (List Pat)) (s : store.Store) (xs out : store.TermId) (O : List (Eqns Nat)),
    Inv s → Repr nm s.nodes.val vs.val (encList (nm none) Vs) →
    Repr nm s.nodes.val xs.val (encLL nm Xs) →
    Repr nm s.nodes.val out.val (encX nm O) → (∀ L ∈ Xs, Vs.length ≤ L.length) →
    Room s (Xs.length * (6 * Vs.length + 5) + 1) →
    dom.excls_onto_loop xs s vs out ⦃ out' s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + Xs.length * (6 * Vs.length + 5) + 1 ∧
        Repr nm s'.nodes.val out'.val (encX nm (exclsOnto Vs Xs O)) ⦄ := by
  intro Xs
  induction Xs with
  | nil =>
    intro s xs out O hI hvs hxs hout hlen hroom
    have hroom' := hroom
    unfold Room at hroom'
    unfold dom.excls_onto_loop
    rw [loop]
    simp only [dom.excls_onto_loop.body]
    step with uncons_repr s xs hI.toWf (p := Term.sym (nm none)) hxs (by unfold Room; omega)
      as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    subst hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    have hfin : Inv s1 ∧ Extends s s1 ∧
        s1.ticks.val ≤ s.ticks.val + ([] : List (List Pat)).length * (6 * Vs.length + 5) + 1 ∧
        Repr nm s1.nodes.val out.val (encX nm (exclsOnto Vs [] O)) :=
      ⟨K1.inv, Extends.of_eq K1.nodes (by omega), by simp only [List.length_nil]; omega,
        by rw [K1.nodes]; simpa [exclsOnto] using hout⟩
    step*
  | cons L Xs ih =>
    intro s xs out O hI hvs hxs hout hlen hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons, Nat.add_mul] at hroom'
    unfold dom.excls_onto_loop
    rw [loop]
    simp only [dom.excls_onto_loop.body]
    step with uncons_repr s xs hI.toWf
      (p := Term.app (encList (nm none) L) (encLL nm Xs)) hxs
      (by unfold Room; omega) as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    obtain ⟨li, rest, rfl, rl, rrest⟩ := hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    have hx1 : Extends s s1 := Extends.of_eq K1.nodes (by omega)
    step with eqns_of_spec Vs L s1 vs li K1.inv (hx1.repr hvs) (hx1.repr rl)
      (hlen L (by simp)) (by unfold Room; omega) as ⟨r2, hI2, hx2, ht2, hr2⟩
    obtain ⟨e, s2⟩ := r2
    simp only at hI2 hx2 ht2 hr2
    have hx02 := hx1.trans hx2
    step with alloc_spec s2 (.App e out) hI2 ⟨hr2.lt, (hx02.repr hout).lt⟩
      (by unfold Room; omega) as ⟨r4, hI4, ht4, htb4, hx4, hr4⟩
    obtain ⟨out1, s4⟩ := r4
    simp only [norm] at hI4 ht4 htb4 hx4 hr4
    have hx04 := hx02.trans hx4
    have hout1 : Repr nm s4.nodes.val out1.val (encX nm (valEqns Vs L :: O)) :=
      .app hr4 (hx4.repr hr2) (hx04.repr hout)
    simp only [uncurry, bind_ok]
    have IH := ih s4 rest out1 (valEqns Vs L :: O) hI4 (hx04.repr hvs) (hx04.repr rrest) hout1
      (fun L' hL' => hlen L' (by simp [hL'])) (by unfold Room; omega)
    unfold dom.excls_onto_loop at IH
    refine WP.spec_mono IH ?_
    rintro ⟨out', s'⟩ ⟨hI', hx', ht', hr'⟩
    refine ⟨hI', hx04.trans hx', by simp only [List.length_cons, Nat.add_mul]; omega, ?_⟩
    simpa [exclsOnto] using hr'

/-- `excls_onto` puts in front of a list each exclusion as the equations of
the variables with their values. -/
theorem excls_onto_spec (Vs : List Pat) (Xs : List (List Pat)) (O : List (Eqns Nat))
    (s : store.Store) (vs xs out : store.TermId) (hI : Inv s)
    (hvs : Repr nm s.nodes.val vs.val (encList (nm none) Vs))
    (hxs : Repr nm s.nodes.val xs.val (encLL nm Xs))
    (hout : Repr nm s.nodes.val out.val (encX nm O)) (hlen : ∀ L ∈ Xs, Vs.length ≤ L.length)
    (hroom : Room s (Xs.length * (6 * Vs.length + 5) + 1)) :
    dom.excls_onto s vs xs out ⦃ out' s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + Xs.length * (6 * Vs.length + 5) + 1 ∧
        Repr nm s'.nodes.val out'.val (encX nm (exclsOnto Vs Xs O)) ⦄ := by
  unfold dom.excls_onto
  exact excls_onto_loop_spec Vs vs Xs s xs out O hI hvs hxs hout hlen hroom

end RwLogVerified
