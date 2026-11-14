/-
# Whether a subterm is free

`sorts::free` decides whether a subterm of the pattern of a store is free,
as `Sorts.freeB` does: it is not a variable, has a variable and none twice,
its variables are at no other place of the pattern and in no exclusion, and
the members of its sorts are its instances. It returns the sorts of the
subterm when it is.
-/
import RwLogVerified.Outside
import RwLogVerified.Fits

open Aeneas Aeneas.Std Result

namespace RwLogVerified

open rwlog_core RwLog

variable {nm : Option Nat → Sym}

/-- A member of a list with a node has a node. -/
theorem repr_mem_encList {nodes : List store.Node} {z : Sym} :
    ∀ {ps : List Pat} {l : Nat}, Repr nm nodes l (encList z ps) → ∀ p ∈ ps, ∃ k, Repr nm nodes k p
  | [], _, _, p, hp => by cases hp
  | q :: ps, l, h, p, hp => by
    cases h with
    | app hn ha hb =>
      rcases List.mem_cons.1 hp with rfl | hp
      · exact ⟨_, ha⟩
      · exact repr_mem_encList hb p hp

/-- The flags `once_each` leaves are on the variables of the term. -/
theorem OnceFlags.var_iff (hnm : Function.Injective nm) {u : Pat} {nodes : List store.Node}
    (hN : NodesOK nodes) {B : Nat → Option Nat} (h : OnceFlags nm u nodes B) {k y : Nat}
    (hk : Repr nm nodes k (.var y)) : B k ≠ none ↔ y ∈ u.vars := by
  constructor
  · intro hb
    obtain ⟨q, hq, hqs⟩ := h.2 k hb
    have := hk.unique hq
    subst this
    exact var_mem_subs_iff.1 hqs
  · intro hy
    obtain ⟨k', hk', hb⟩ := h.1 y hy
    rw [Repr.inj hnm hN hk hk']
    exact hb

open Classical in
/-- The sorts of a subterm, as a conjunction. -/
noncomputable def cloOf (S : Sorts) (U : List Name) (L : List (Nat × Sorts.Conj)) (u : Pat) :
    Sorts.Conj :=
  U.toFinset.filter (CloAt S L u)

theorem mem_cloOf {S : Sorts} {U : List Name} {L : List (Nat × Sorts.Conj)} {u : Pat} {n : Name} :
    n ∈ cloOf S U L u ↔ n ∈ U ∧ CloAt S L u n := by
  classical
  simp [cloOf]

theorem cpat_cloOf (z : Sym) (S : Sorts) (U : List Name) (L : List (Nat × Sorts.Conj)) (u : Pat) :
    cpat z U (cloOf S U L u) = namesPat z (conjList U (CloAt S L u)) := by
  unfold cpat
  rw [conjList_congr fun n hn => ?_]
  rw [mem_cloOf]
  exact ⟨fun h => h.2, fun h => ⟨hn, h⟩⟩

/-- A subterm is free: what `Sorts.freeB` asks, of a pattern, the variables
of the exclusions and the conjunctions of the entries. -/
def FreeAt (S : Sorts) (U : List Name) (L : List (Nat × Sorts.Conj)) (XV : List Nat)
    (tp up : Pat) : Prop :=
  (∀ v, up ≠ .var v) ∧ up.vars ≠ [] ∧ up.vars.Nodup ∧ (∀ y ∈ up.vars, y ∉ Sorts.outV up tp) ∧
    (∀ y ∈ up.vars, y ∉ XV) ∧ Sorts.fitsIn S (conjOf L) (cloOf S U L up) up = true

/-- The ticks `free` may take. -/
noncomputable def freeCost (S : Sorts) (U : List Name) (L : List (Nat × Sorts.Conj))
    (r q : Nat) (XV : List Nat) (tp up : Pat) : Nat :=
  14 * up.subs.card + onceCost up + 2 * XV.length + markedCost tp + cloCost S U L up +
    fitsCost S U.length L.length r q up + 9

/-- `free` returns the sorts of a subterm when it is free, and nothing when
it is not. -/
theorem free_spec {S : Sorts} {sp : Pat} {U : List Name} (hC : Ctx nm S sp U) {r q : Nat}
    (hr : ∀ d, (Sorts.reachSet S d).card ≤ r)
    (hq : ∀ d m, (Sorts.reachGSet S (d, some m)).card ≤ q) (hUz : ∀ n ∈ U, n ≠ nm none)
    (L : List (Nat × Sorts.Conj)) (hL : ∀ v, Sub U (conjOf L v)) (XV : List Nat) {tp up : Pat}
    (htfo : tp.firstOrder = true) (hufo : up.firstOrder = true) (s : store.Store)
    (decls names t xv es u : store.TermId) (hI : Inv s)
    (hd : Repr nm s.nodes.val decls.val sp)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (ht : Repr nm s.nodes.val t.val tp)
    (hxv : Repr nm s.nodes.val xv.val (encList (nm none) (XV.map Term.var)))
    (hes : Repr nm s.nodes.val es.val (encVarEntries nm U L))
    (hu : Repr nm s.nodes.val u.val up) (hroom : Room s (freeCost S U L r q XV tp up)) :
    sorts.free s decls names t xv es u ⦃ o s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + freeCost S U L r q XV tp up ∧
        match o with
        | none => ¬ FreeAt S U L XV tp up
        | some k => FreeAt S U L XV tp up ∧
            Repr nm s'.nodes.val k.val (cpat (nm none) U (cloOf S U L up)) ⦄ := by
  have hnm := hC.inj
  unfold sorts.free
  have hroom' := hroom
  unfold Room freeCost at hroom'
  have hfc : freeCost S U L r q XV tp up = 14 * up.subs.card + onceCost up + 2 * XV.length +
      markedCost tp + cloCost S U L up + fitsCost S U.length L.length r q up + 9 := rfl
  step with is_var_w s u hI.toWf hu (by unfold Room; omega) as ⟨b, s1, hb, hK1⟩
  have K1 : Kept s s1 1 := hK1.kept hI
  have ht1 := K1.ticks
  have hx1 : Extends s s1 := Extends.of_eq K1.nodes (by omega)
  by_cases hv : ∃ v, up = .var v
  · have hb' : b = true := hb.2 hv
    subst hb'
    simp only [↓reduceIte, WP.spec_ok]
    refine ⟨K1.inv, hx1, by omega, ?_⟩
    obtain ⟨v, hv⟩ := hv
    exact fun h => h.1 v hv
  have hb' : b = false := by
    cases b with
    | false => rfl
    | true => exact absurd (hb.1 rfl) hv
  subst hb'
  have hnv : ∀ v, up ≠ .var v := fun v e => hv ⟨v, e⟩
  simp only [Bool.false_eq_true, ↓reduceIte]
  step with clear_spec s1 .A K1.inv (by unfold Room; omega) as ⟨s2, n2, t2, hI2, tb2, tbo2⟩
  have hx2 : Extends s s2 := hx1.trans (Extends.of_eq n2 (by omega))
  have hpc := pending_card_le (nm := nm) s2.nodes.val (tbl s2 .A) up.subs
  step with rebuild_g_spec hnm s2 term.Leaf.Right u (σ := rightSub)
    (im := fun p => p.bind rightSub) up.subs hI2 (hx2.repr hu) rfl
    (fun k v hk => by rw [tb2 k] at hk; cases hk) (fun t _ _ _ => ImStep.bind rightSub t)
    (Finset.Subset.refl _) (by unfold Room; omega) as ⟨g, s3, hG⟩
  have ht3 := hG.cost
  have hRM : RightMemo nm s3.nodes.val (tbl s3 .A) up := hG.rightMemo hnm hI2 tb2
  have hx3 : Extends s s3 := hx2.trans hG.ext
  have hu3 : Repr nm s3.nodes.val u.val up := hx3.repr hu
  step with same_spec s3 g u hG.inv (by unfold Room; omega) as ⟨b1, s4, hb1, K4⟩
  have ht4 := K4.ticks
  have hx4 : Extends s s4 := hx3.trans (Extends.of_eq K4.nodes (by omega))
  have hground : g.val = u.val ↔ up.vars = [] := by
    rw [← bind_right_eq_iff]
    constructor
    · intro e
      have hr := hG.repr
      rw [e] at hr
      exact hr.unique hu3
    · intro e
      have hr := hG.repr
      rw [e] at hr
      exact Repr.inj hnm hG.inv.nodesOK hr hu3
  by_cases hgr : up.vars = []
  · have hb1' : b1 = true := by rw [hb1]; simpa using hground.2 hgr
    subst hb1'
    simp only [↓reduceIte, WP.spec_ok]
    exact ⟨K4.inv, hx4, by omega, fun h => h.2.1 hgr⟩
  have hb1' : b1 = false := by
    rw [hb1]
    simpa using fun h => hgr (hground.1 h)
  subst hb1'
  simp only [Bool.false_eq_true, ↓reduceIte]
  step with once_each_spec hnm s4 u K4.inv (by rw [K4.nodes]; exact hu3)
    (by rw [K4.nodes, K4.tbl]; exact hRM) (by unfold Room; omega)
    as ⟨b2, s5, hI5, hx5, htA5, hb2, hfl5, ht5⟩
  have hx05 : Extends s s5 := hx4.trans hx5
  by_cases hnd : up.vars.Nodup
  swap
  · have hb2' : b2 = false := by
      cases b2 with
      | false => rfl
      | true => exact absurd (hb2.1 rfl) hnd
    subst hb2'
    simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact ⟨hI5, hx05, by omega, fun h => hnd h.2.2.1⟩
  have hb2' : b2 = true := hb2.2 hnd
  subst hb2'
  simp only [↓reduceIte]
  have hfl := hfl5 rfl
  step with any_marked_spec hnm XV s5 xv hI5 (hx05.repr hxv) (by unfold Room; omega)
    as ⟨b3, s6, hI6, hn6, htb6, hm6, ht6, hb3⟩
  have hx06 : Extends s s6 := hx05.trans (Extends.of_eq hn6 (by omega))
  have hXV : (∃ x ∈ XV, ∃ k, Repr nm s5.nodes.val k (.var x) ∧ tbl s5 .B k ≠ none) ↔
      ∃ y ∈ up.vars, y ∈ XV := by
    constructor
    · rintro ⟨x, hx, k, hk, hfk⟩
      exact ⟨x, (OnceFlags.var_iff hnm hI5.nodesOK hfl hk).1 hfk, hx⟩
    · rintro ⟨y, hy, hyx⟩
      obtain ⟨k, hk⟩ := repr_mem_encList (hx05.repr hxv) (.var y) (List.mem_map.2 ⟨y, hyx, rfl⟩)
      exact ⟨y, hyx, k, hk, (OnceFlags.var_iff hnm hI5.nodesOK hfl hk).2 hy⟩
  by_cases hex : ∃ y ∈ up.vars, y ∈ XV
  · have hb3' : b3 = true := hb3.2 (hXV.2 hex)
    subst hb3'
    simp only [↓reduceIte, WP.spec_ok]
    refine ⟨hI6, hx06, by omega, fun h => ?_⟩
    obtain ⟨y, hy, hyx⟩ := hex
    exact h.2.2.2.2.1 y hy hyx
  have hb3' : b3 = false := by
    cases b3 with
    | false => rfl
    | true => exact absurd (hXV.1 (hb3.1 rfl)) hex
  subst hb3'
  simp only [Bool.false_eq_true, ↓reduceIte]
  step with marked_outside_spec hnm (fun y => y ∈ up.vars) s6 u t hI6 (hx06.repr hu)
    (hx06.repr ht) htfo
    (fun k y hk => by
      rw [htb6]
      rw [hn6] at hk
      exact OnceFlags.var_iff hnm hI5.nodesOK hfl hk)
    (by unfold Room; omega) as ⟨b4, s7, hI7, hx7, hB7, hb4, ht7⟩
  have hx07 : Extends s s7 := hx06.trans hx7
  by_cases hout : ∃ y ∈ Sorts.outV up tp, y ∈ up.vars
  · have hb4' : b4 = true := hb4.2 hout
    subst hb4'
    simp only [↓reduceIte, WP.spec_ok]
    refine ⟨hI7, hx07, by omega, fun h => ?_⟩
    obtain ⟨y, hy, hyu⟩ := hout
    exact h.2.2.2.1 y hyu hy
  have hb4' : b4 = false := by
    cases b4 with
    | false => rfl
    | true => exact absurd (hb4.1 rfl) hout
  subst hb4'
  simp only [Bool.false_eq_true, ↓reduceIte]
  step with sorts_of_spec hnm S hC.sorts
    (fun m _ f k ks hs m' hm' => ⟨hC.names m' (step_kid_names hs hm'),
      hC.nz m' (step_kid_names hs hm')⟩)
    L hufo s7 decls names es u hI7 (hx07.repr hd) (hx07.repr hU) (hx07.repr hes) (hx07.repr hu)
    (by unfold Room; omega) as ⟨k, s8, hI8, hx8, ht8, rk⟩
  have hx08 : Extends s s8 := hx07.trans hx8
  have rk' : Repr nm s8.nodes.val k.val (cpat (nm none) U (cloOf S U L up)) := by
    rw [cpat_cloOf]; exact rk
  step with fits_spec hC hr hq hUz L hL (K0 := cloOf S U L up) (fun n hn => (mem_cloOf.1 hn).1)
    hufo s8 decls names es k u hI8 (hx08.repr hd) (hx08.repr hU) (hx08.repr hes) rk'
    (hx08.repr hu) (by unfold Room; omega) as ⟨b5, s9, hI9, hx9, ht9, hb5⟩
  have hx09 : Extends s s9 := hx08.trans hx9
  by_cases hfit : Sorts.fitsIn S (conjOf L) (cloOf S U L up) up = true
  · have hb5' : b5 = true := hb5.2 hfit
    subst hb5'
    simp only [↓reduceIte, WP.spec_ok]
    exact ⟨hI9, hx09, by omega, ⟨hnv, hgr, hnd, fun y hy hyo => hout ⟨y, hyo, hy⟩,
      fun y hy hyx => hex ⟨y, hy, hyx⟩, hfit⟩, hx9.repr rk'⟩
  · have hb5' : b5 = false := by
      cases b5 with
      | false => rfl
      | true => exact absurd (hb5.1 rfl) hfit
    subst hb5'
    simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact ⟨hI9, hx09, by omega, fun h => hfit h.2.2.2.2.2⟩

end RwLogVerified
