/-
# The folded store

`sorts::fold` computes the folded store of the specification
(`Sorts.foldRaw`) from a store determined by its pattern and what it
denotes: it finds the outermost free subterms of the pattern, copies the
pattern with a variable for each, numbers the variables in the order they
first occur, renames the exclusions, and assembles the store. The exclusions
come out in the order the store lists them, last first, which the
specification leaves open (`Sorts.assembled_fold`).
-/
import RwLogVerified.FoldMath

open Aeneas Aeneas.Std Result

namespace RwLogVerified

open rwlog_core RwLog

variable {nm : Option Nat → Sym}

/-! ## Representatives on the store -/

/-- A representative on the store: the pattern, the list of the conjunctions
of the variables and the list of the exclusions, each the list of its
values, of a store. -/
structure RepAt (nm : Option Nat → RwLog.Sym) (U : List Name) (nodes : List store.Node)
    (a : sorts.Rep) (r : Sorts.Raw) (Y : List Sorts.Binds) : Prop where
  t : Repr nm nodes a.t.val r.t
  c : Repr nm nodes a.c.val (encList (nm none) (r.c.map (cpat (nm none) U)))
  nd : Y.Nodup
  y : Y.toFinset = r.x
  x : Repr nm nodes a.x.val (encLL nm (Y.map (vals r.c.length)))

theorem RepAt.extends {U : List Name} {s s' : store.Store} {a : sorts.Rep} {r : Sorts.Raw}
    {Y : List Sorts.Binds} (h : RepAt nm U s.nodes.val a r Y) (hx : Extends s s') :
    RepAt nm U s'.nodes.val a r Y :=
  ⟨hx.repr h.t, hx.repr h.c, h.nd, h.y, hx.repr h.x⟩

/-! ## Assembling a store -/

/-- The subterms of the lists of a list, counted list by list. -/
def listsCard (nm : Option Nat → RwLog.Sym) (Ls : List (List Pat)) : Nat :=
  (Ls.map fun B => (encList (nm none) B).subs.card).sum

theorem le_listsCard : ∀ {Ls : List (List Pat)} {B : List Pat}, B ∈ Ls →
    (encList (nm none) B).subs.card ≤ listsCard nm Ls
  | [], _, h => by cases h
  | A :: Ls, B, h => by
    simp only [listsCard, List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := le_listsCard h
      simp only [listsCard] at this
      omega

/-- The ticks `assemble` may take. -/
noncomputable def assembleCost (nm : Option Nat → RwLog.Sym) (S : Sorts) (U : List Name)
    (rc : Nat) (tp : Pat) (cL : List Sorts.Conj) (X : List (Eqns Nat)) : Nat :=
  placesCost cL.length + normExsCost nm S U rc ⟨tp, cL, ∅⟩ X +
    antiCost cL.length (listsCard nm ((Sorts.normExs S ⟨tp, cL, ∅⟩ X).map (vals cL.length)))
      ((Sorts.normExs S ⟨tp, cL, ∅⟩ X).map (vals cL.length)).length

/-- `assemble` gives the store assembled from a pattern, the conjunctions of
its variables and a list of exclusions (`Sorts.assembled`). -/
theorem assemble_spec (hnm : Function.Injective nm) {S : Sorts} {sp : Pat} {U : List Name}
    (hC : Ctx nm S sp U) {rc : Nat} (hr : ∀ d, (Sorts.reachSet S d).card ≤ rc) (tp : Pat)
    (cL : List Sorts.Conj) (hcN : ∀ c ∈ cL, ∀ n ∈ c, n ∈ Sorts.names S) (X : List (Eqns Nat))
    (hfo : ∀ E ∈ X, E.FO) (hv : ∀ E ∈ X, ∀ v ∈ E.vars, v < cL.length)
    (hnd : (RwLog.antichain (Sorts.covers cL.length) (Sorts.normExs S ⟨tp, cL, ∅⟩ X)).Nodup)
    (s : store.Store) (decls names t cs x : store.TermId) (hI : Inv s)
    (hd : Repr nm s.nodes.val decls.val sp)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (ht : Repr nm s.nodes.val t.val tp)
    (hcs : Repr nm s.nodes.val cs.val (encList (nm none) (cL.map (cpat (nm none) U))))
    (hx : Repr nm s.nodes.val x.val (encX nm X))
    (hroom : Room s (assembleCost nm S U rc tp cL X)) :
    sorts.assemble s decls names t cs x ⦃ rep s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + assembleCost nm S U rc tp cL X ∧
        RepAt nm U s'.nodes.val rep (Sorts.assembled S tp cL X)
          (RwLog.antichain (Sorts.covers cL.length) (Sorts.normExs S ⟨tp, cL, ∅⟩ X)) ⦄ := by
  unfold sorts.assemble
  have hroom' := hroom
  unfold Room assembleCost at hroom'
  have hklen : (cL.map (cpat (nm none) U)).length = cL.length := List.length_map _
  step with places_spec (cL.map (cpat (nm none) U)) s cs hI hcs
    (by rw [hklen]; unfold Room; omega) as ⟨vs, s1, hI1, hx1, ht1, rvs⟩
  rw [hklen] at ht1 rvs
  have hcN' : ∀ v, ∀ n ∈ (⟨tp, cL, ∅⟩ : Sorts.Raw).conj v, n ∈ Sorts.names S := by
    intro v n hn
    by_cases hvl : v < cL.length
    · have e : (⟨tp, cL, ∅⟩ : Sorts.Raw).conj v = cL[v] := by
        simp [Sorts.Raw.conj, List.getD_eq_getElem?_getD, hvl]
      rw [e] at hn
      exact hcN _ (List.getElem_mem hvl) n hn
    · have e : (⟨tp, cL, ∅⟩ : Sorts.Raw).conj v = ∅ := by
        simp [Sorts.Raw.conj, List.getD_eq_getElem?_getD, hvl]
      rw [e] at hn
      simp at hn
  step with norm_exs_spec hnm hC hr ⟨tp, cL, ∅⟩ hcN' X hfo hv s1 decls names vs cs x hI1
    (hx1.repr hd) (hx1.repr hU) rvs (hx1.repr hcs) (hx1.repr hx)
    (by unfold Room; omega) as ⟨ys, s2, hI2, hx2, ht2, rys⟩
  have hL : ∀ B' ∈ (Sorts.normExs S ⟨tp, cL, ∅⟩ X).map (vals cL.length),
      B'.length = cL.length ∧ (encList (nm none) B').subs.card ≤
        listsCard nm ((Sorts.normExs S ⟨tp, cL, ∅⟩ X).map (vals cL.length)) := by
    intro B' hB'
    refine ⟨?_, le_listsCard hB'⟩
    obtain ⟨θ', -, rfl⟩ := List.mem_map.1 hB'
    exact vals_length _ _
  step with antichain_spec hnm cL.length
    (listsCard nm ((Sorts.normExs S ⟨tp, cL, ∅⟩ X).map (vals cL.length)))
    ((Sorts.normExs S ⟨tp, cL, ∅⟩ X).map (vals cL.length)) s2 vs ys hI2 (hx2.repr rvs) rys hL
    (by unfold Room; omega) as ⟨zs, s3, hI3, hx3, ht3, rzs⟩
  have hY : ∀ θ' ∈ Sorts.normExs S ⟨tp, cL, ∅⟩ X, ∀ b' ∈ θ', b'.1 < cL.length := by
    intro θ' hθ'
    obtain ⟨E, hE, hEθ⟩ := List.mem_filterMap.1 hθ'
    exact (Sorts.normEx_some (hfo E hE) (hv E hE) hEθ).1.dom
  rw [antichain_vals hY] at rzs
  exact ⟨hI3, (hx1.trans hx2).trans hx3, by unfold assembleCost; omega,
    ((hx1.trans hx2).trans hx3).repr ht, ((hx1.trans hx2).trans hx3).repr hcs, hnd, rfl, rzs⟩

/-! ## What the fold works on -/

/-- The entries of the variables of a store, last first. -/
def storeEntries (R : Sorts.Raw) : List (Nat × Sorts.Conj) :=
  ((List.range R.c.length).zip R.c).reverse

theorem storeEntries_length (R : Sorts.Raw) : (storeEntries R).length = R.c.length := by
  simp [storeEntries]

theorem conjOf_storeEntries (R : Sorts.Raw) (v : Nat) : conjOf (storeEntries R) v = R.conj v := by
  have hfst : (storeEntries R).map Prod.fst = (List.range R.c.length).reverse := by
    unfold storeEntries
    rw [List.map_reverse, List.map_fst_zip (by simp)]
  by_cases hv : v < R.c.length
  · have e : R.conj v = R.c[v] := by simp [Sorts.Raw.conj, List.getD_eq_getElem?_getD, hv]
    rw [e]
    refine conjOf_mem (by rw [hfst]; exact List.nodup_reverse.2 List.nodup_range) ?_
    unfold storeEntries
    rw [List.mem_reverse]
    exact List.mem_iff_getElem.2 ⟨v, by simp [hv], by simp⟩
  · rw [Sorts.Raw.Normal.conj_of_ge R (Nat.le_of_not_lt hv)]
    refine conjOf_not fun e he e' => ?_
    have : e.1 ∈ (storeEntries R).map Prod.fst := List.mem_map.2 ⟨e, he, rfl⟩
    rw [hfst, List.mem_reverse, List.mem_range] at this
    omega

theorem storeEntries_enc (U : List Name) (R : Sorts.Raw) :
    (List.zipWith Term.app (varsTo R.c.length) (R.c.map (cpat (nm none) U))).reverse ++ [] =
      (storeEntries R).map (varEntry nm U) := by
  unfold storeEntries varsTo
  rw [List.append_nil, List.map_reverse, List.zip_eq_zipWith, List.map_zipWith,
    List.zipWith_map_left, List.zipWith_map_right]
  rfl

/-- The equations of the exclusions, in the order `moved_all` leaves them. -/
def exEqns (Y : List Sorts.Binds) : List (Eqns Nat) := Y.reverse.map Sorts.eqnsOf

/-- The exclusions over the numbers of the names, in that order. -/
def foldXl (S : Sorts) (R : Sorts.Raw) (Y : List Sorts.Binds) : List (Eqns Nat) :=
  (exEqns Y).map (Eqns.ren fun x => (Sorts.foldNames S R).idxOf (.var x))

/-- The folded store, as `fold` assembles it. -/
noncomputable def foldedRaw (S : Sorts) (R : Sorts.Raw) (Y : List Sorts.Binds) : Sorts.Raw :=
  Sorts.assembled S (Sorts.foldStore S R).t ((Sorts.foldNames S R).map (Sorts.foldConj S R))
    (foldXl S R Y)

/-- The exclusions of the folded store, as `fold` lists them. -/
noncomputable def foldedYs (S : Sorts) (R : Sorts.Raw) (Y : List Sorts.Binds) :
    List Sorts.Binds :=
  RwLog.antichain (Sorts.covers ((Sorts.foldNames S R).map (Sorts.foldConj S R)).length)
    (Sorts.normExs S ⟨(Sorts.foldStore S R).t,
      (Sorts.foldNames S R).map (Sorts.foldConj S R), ∅⟩ (foldXl S R Y))

section facts

variable {S : Sorts} {sp : Pat} {U : List Name} {R : Sorts.Raw} {Y : List Sorts.Binds}

theorem mem_foldXl (hy : Y.toFinset = R.x) {E : Eqns Nat} :
    E ∈ foldXl S R Y ↔ E ∈ Sorts.foldXs S R := by
  unfold foldXl exEqns Sorts.foldXs
  simp only [List.mem_map, List.mem_reverse, Sorts.Raw.mem_xs, ← hy, List.mem_toFinset]
  constructor
  · rintro ⟨_, ⟨θ, hθ, rfl⟩, rfl⟩
    exact ⟨θ, hθ, rfl⟩
  · rintro ⟨θ, hθ, rfl⟩
    exact ⟨_, ⟨θ, hθ, rfl⟩, rfl⟩

theorem mem_exVars (hy : Y.toFinset = R.x) {y : Nat} :
    y ∈ RwLog.firsts (encX nm (exEqns Y)).vars ↔ ∃ θ ∈ R.x, y ∈ (Sorts.eqnsOf θ).vars := by
  rw [(RwLog.firsts_spec _).2.1 y]
  unfold encX exEqns
  rw [mem_vars_encList]
  simp only [List.mem_map, List.mem_reverse, ← hy, List.mem_toFinset]
  constructor
  · rintro ⟨_, ⟨_, ⟨θ, hθ, rfl⟩, rfl⟩, hv⟩
    obtain ⟨p, hp, hv⟩ := mem_vars_encEqs.1 hv
    exact ⟨θ, hθ, List.mem_flatMap.2 ⟨p, hp, List.mem_append.2 hv⟩⟩
  · rintro ⟨θ, hθ, hv⟩
    obtain ⟨p, hp, hv⟩ := List.mem_flatMap.1 hv
    exact ⟨_, ⟨_, ⟨θ, hθ, rfl⟩, rfl⟩, mem_vars_encEqs.2 ⟨p, hp, List.mem_append.1 hv⟩⟩

theorem cloOf_storeEntries (hC : Ctx nm S sp U) (hUS : ∀ n ∈ U, n ∈ Sorts.names S) (u : Pat) :
    cloOf S U (storeEntries R) u = Sorts.clo S R u := by
  have hconj : conjOf (storeEntries R) = R.conj := funext (conjOf_storeEntries R)
  ext m
  rw [mem_cloOf, Sorts.mem_clo]
  unfold CloAt
  rw [hconj]
  exact ⟨fun h => ⟨hUS m h.1, h.2⟩, fun h => ⟨hC.names m h.1, h.2⟩⟩

/-- A subterm passes the test of `free` when the specification says it is
free. -/
theorem free_iff (hC : Ctx nm S sp U) (hUS : ∀ n ∈ U, n ∈ Sorts.names S)
    (hy : Y.toFinset = R.x) (u : Pat) :
    FreeAt S U (storeEntries R) (RwLog.firsts (encX nm (exEqns Y)).vars) R.t u ↔
      Sorts.freeB S R u = true := by
  have hconj : conjOf (storeEntries R) = R.conj := funext (conjOf_storeEntries R)
  have hxv : (∀ y ∈ u.vars, y ∉ RwLog.firsts (encX nm (exEqns Y)).vars) ↔
      ∀ θ ∈ R.x, ∀ y ∈ u.vars, y ∉ (Sorts.eqnsOf θ).vars := by
    simp only [mem_exVars (nm := nm) hy]
    exact ⟨fun h θ hθ y hyu hm => h y hyu ⟨θ, hθ, hm⟩,
      fun h y hyu ⟨θ, hθ, hm⟩ => h θ hθ y hyu hm⟩
  unfold FreeAt Sorts.freeB
  simp only [Bool.and_eq_true, decide_eq_true_iff, Sorts.notVar_iff]
  rw [cloOf_storeEntries hC hUS, hconj, hxv]
  tauto

end facts

/-! ## The names and their numbers -/

/-- What holds of the names of the folded pattern once the free subterms
are found: a name is a variable of the store, numbered by itself, or a free
subterm found, numbered by its variable. -/
def Named (S : Sorts) (R : Sorts.Raw) (Fl : List Pat) : Prop :=
  ∀ p ∈ (Sorts.foldVc S R R.t).vars,
    (∃ x, p = .var x ∧ x < R.c.length ∧ fnum (fpairs R.c.length Fl) p = x) ∨
      (p ∈ Fl ∧ R.c.length ≤ fnum (fpairs R.c.length Fl) p ∧
        (fpairs R.c.length Fl).lookup p = some (fnum (fpairs R.c.length Fl) p))

theorem named_of {S : Sorts} (hS : S.WellFormed) {R : Sorts.Raw} (hR : R.Roomy S) {U : List Name}
    {L : List (Nat × Sorts.Conj)} {XV : List Nat} {Sn Fl : List Pat}
    (hG : SGo S U L XV R.t [] Sn Fl)
    (hfree : ∀ u ∈ R.t.subs, u.firstOrder = true →
      (FreeAt S U L XV R.t u ↔ Sorts.freeB S R u = true)) : Named S R Fl := by
  have hN := Sorts.names_of_roomy hS hR
  intro p hp
  rcases (fold_im (N := R.c.length) hG hfree hR.shaped.fo).2 p hp with ⟨x, rfl⟩ | hF
  · have hp' : Term.var x ∈ (Sorts.foldV S R.store R.t).vars := hN.eq ▸ hp
    have hnF : Term.var x ∉ Fl := fun h => (hG.found _ h).2.1 x rfl
    exact .inl ⟨x, rfl, hN.vars _ hp' x (by simp [Term.vars]), fnum_var hnF⟩
  · exact .inr ⟨hF, (fnum_found hF).2, (fnum_found hF).1⟩

theorem Named.inj {S : Sorts} {R : Sorts.Raw} {Fl : List Pat} (h : Named S R Fl) :
    ∀ a ∈ (Sorts.foldVc S R R.t).vars, ∀ b ∈ (Sorts.foldVc S R R.t).vars,
      fnum (fpairs R.c.length Fl) a = fnum (fpairs R.c.length Fl) b → a = b := by
  intro a ha b hb e
  rcases h a ha with ⟨x, rfl, hx, ex⟩ | ⟨-, ha1, ha2⟩
  · rcases h b hb with ⟨x', rfl, hx', ex'⟩ | ⟨-, hb1, -⟩
    · rw [ex, ex'] at e; rw [e]
    · omega
  · rcases h b hb with ⟨x', rfl, hx', ex'⟩ | ⟨-, -, hb2⟩
    · omega
    · exact lookup_fpairs_inj ha2 (e ▸ hb2)

theorem Named.conj {S : Sorts} {sp : Pat} {U : List Name} {R : Sorts.Raw} {Fl : List Pat}
    (h : Named S R Fl) (hC : Ctx nm S sp U) (hUS : ∀ n ∈ U, n ∈ Sorts.names S) {XV : List Nat}
    {Sn : List Pat} (hG : SGo S U (storeEntries R) XV R.t [] Sn Fl) :
    ∀ p ∈ (Sorts.foldVc S R R.t).vars,
      conjOf (foundEntries S U (storeEntries R) R.c.length Fl)
        (fnum (fpairs R.c.length Fl) p) = Sorts.foldConj S R p := by
  intro p hp
  rcases h p hp with ⟨x, rfl, hx, ex⟩ | ⟨hF, -, hl⟩
  · rw [ex, conjOf_found_var hx, conjOf_storeEntries]
    rfl
  · rw [conjOf_found hl, cloOf_storeEntries hC hUS, Sorts.foldConj_notVar (hG.found p hF).2.1]

theorem fpairs_length (N : Nat) : ∀ Fl : List Pat, (fpairs N Fl).length = Fl.length
  | [] => rfl
  | _ :: Fl => by simp [fpairs, fpairs_length N Fl]

theorem mem_fpairs_lookup {N : Nat} : ∀ {Fl : List Pat} {p : Pat × Nat}, Fl.Nodup →
    p ∈ fpairs N Fl → (fpairs N Fl).lookup p.1 = some p.2
  | [], _, _, h => by cases h
  | u0 :: Fl, p, hnd, h => by
    rw [lookup_fpairs_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact ite_eq_left rfl
    · have hne : p.1 ≠ u0 := fun e => (List.nodup_cons.1 hnd).1 (e ▸ (mem_fpairs h).1)
      rw [ite_eq_right hne]
      exact mem_fpairs_lookup (List.nodup_cons.1 hnd).2 h

theorem size_rename {V W : Type} (f : V → W) : ∀ t : Term V, (t.rename f).size = t.size
  | .var _ => rfl
  | .sym _ => rfl
  | .app a b => by
    have ha := size_rename f a
    have hb := size_rename f b
    simp only [Term.rename] at ha hb ⊢
    simp only [Term.bind, Term.size, ha, hb]

theorem ren_congr {f g : Nat → Nat} {E : Eqns Nat}
    (h : ∀ p ∈ E, ∀ v ∈ p.1.vars ++ p.2.vars, f v = g v) : Eqns.ren f E = Eqns.ren g E := by
  unfold Eqns.ren
  refine List.map_congr_left fun p hp => ?_
  have h1 : p.1.rename f = p.1.rename g :=
    Term.bind_congr fun v hv => by rw [h p hp v (List.mem_append_left _ hv)]
  have h2 : p.2.rename f = p.2.rename g :=
    Term.bind_congr fun v hv => by rw [h p hp v (List.mem_append_right _ hv)]
  rw [h1, h2]

/-! ## The fold -/

/-- The ticks `fold` may take on a store. -/
noncomputable def foldCost (nm : Option Nat → RwLog.Sym) (S : Sorts) (U : List Name)
    (rc q : Nat) (R : Sorts.Raw) (Y : List Sorts.Binds) : Nat :=
  placesCost R.c.length + (4 * R.c.length + 2) + movedAllCost R.c.length Y.length +
    firstsCost (encX nm (exEqns Y)) + (numCost 0 R.c.length + 2) +
    freeSubsCost S U (storeEntries R) rc q (RwLog.firsts (encX nm (exEqns Y)).vars) R.t
      R.c.length +
    (17 * R.t.subs.card + 8) +
    (22 * (Sorts.foldStore S R).t.size + 2 * (Sorts.foldNames S R).length + 13) +
    ((Sorts.foldNames S R).length * (3 * (R.t.subs.card + R.c.length) + 4) +
      2 * (Sorts.foldNames S R).length + 4) +
    (numCost 0 (Sorts.foldNames S R).length + 3) +
    (14 * (encX nm (exEqns Y)).subs.card + 5) +
    assembleCost nm S U rc (Sorts.foldStore S R).t
      ((Sorts.foldNames S R).map (Sorts.foldConj S R)) (foldXl S R Y)

/-- `fold` computes the folded store of a store determined by its pattern
and what it denotes, with a solution, whose variables each have infinitely
many values: the store assembled from the folded pattern, the sorts of its
names and the renamed exclusions. -/
theorem fold_spec (hnm : Function.Injective nm) {S : Sorts} {sp : Pat} {U : List Name}
    (hC : Ctx nm S sp U) (hS : S.WellFormed) (hUS : ∀ n ∈ U, n ∈ Sorts.names S) {rc q : Nat}
    (hr : ∀ d, (Sorts.reachSet S d).card ≤ rc)
    (hq : ∀ d m, (Sorts.reachGSet S (d, some m)).card ≤ q)
    (R : Sorts.Raw) (hR : R.Roomy S) (Y : List Sorts.Binds) (s : store.Store)
    (decls names : store.TermId) (rep : sorts.Rep) (hI : Inv s)
    (hd : Repr nm s.nodes.val decls.val sp)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (hrep : RepAt nm U s.nodes.val rep R Y)
    (hroom : Room s (foldCost nm S U rc q R Y)) :
    sorts.fold s decls names rep ⦃ res s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + foldCost nm S U rc q R Y ∧
        RepAt nm U s'.nodes.val res (foldedRaw S R Y) (foldedYs S R Y) ⦄ := by
  unfold sorts.fold
  have hroom' := hroom
  unfold Room foldCost at hroom'
  have hsh := hR.shaped
  have hN := Sorts.names_of_roomy hS hR
  have hUz : ∀ m ∈ U, m ≠ nm none := fun m hm => hC.nz m (hUS m hm)
  have hYpre : ∀ θ ∈ Y, Sorts.Pre R.c.length θ := fun θ hθ =>
    (hsh.ex θ (by rw [← hrep.y]; exact List.mem_toFinset.2 hθ)).toPre
  have hklen : (R.c.map (cpat (nm none) U)).length = R.c.length := List.length_map _
  -- the variables and their entries
  step with places_spec (R.c.map (cpat (nm none) U)) s rep.c hI hrep.c
    (by rw [hklen]; unfold Room; omega) as ⟨vs, s1, hI1, hx1, ht1, rvs⟩
  rw [hklen] at ht1 rvs
  step with alloc_spec s1 .Nil hI1 trivial (by unfold Room; omega)
    as ⟨nil, s2, hI2, ht2, htb2, hx2, hr2⟩
  simp only [norm] at hr2
  have hx02 := hx1.trans hx2
  step with pairs_onto_gen_spec (nm := nm) (varsTo R.c.length) (R.c.map (cpat (nm none) U)) s2
    vs rep.c nil [] hI2 (by simp) (hx2.repr rvs) (hx02.repr hrep.c) (.nil hr2)
    (by simp only [varsTo_length]; unfold Room; omega) as ⟨es, s3, hI3, hx3, ht3, res⟩
  simp only [varsTo_length] at ht3
  rw [storeEntries_enc] at res
  have res' : Repr nm s3.nodes.val es.val (encVarEntries nm U (storeEntries R)) := res
  have hx03 := hx02.trans hx3
  -- the equations of the exclusions and their variables
  have hYlen : ∀ B ∈ Y.map (vals R.c.length), B.length = R.c.length := by
    intro B hB
    obtain ⟨θ, -, rfl⟩ := List.mem_map.1 hB
    exact vals_length _ _
  step with moved_all_spec hnm R.c.length (Y.map (vals R.c.length)) s3 vs rep.x hI3 hYlen
    ((hx2.trans hx3).repr rvs) (hx03.repr hrep.x)
    (by simp only [List.length_map]; unfold Room; omega) as ⟨ms, s4, hI4, hx4, ht4, rms⟩
  simp only [List.length_map] at ht4
  have hMS : (Y.map (vals R.c.length)).reverse.map movedVals = exEqns Y := by
    unfold exEqns
    rw [← List.map_reverse, List.map_map]
    exact List.map_congr_left fun θ hθ => movedVals_vals (hYpre θ (List.mem_reverse.1 hθ))
  rw [hMS] at rms
  have hx04 := hx03.trans hx4
  step with firsts_spec hnm s4 ms hI4 rms (by unfold Room; omega)
    as ⟨xv, s5, hI5, hx5, ht5, rxv⟩
  have hx05 := hx04.trans hx5
  step with number_spec (List.range R.c.length) List.nodup_range s5 vs hI5
    (((hx2.trans hx3).trans (hx4.trans hx5)).repr rvs)
    (by simp only [List.length_range]; unfold Room; omega)
    as ⟨next, s6, hI6, hx6, ht6, hA6, hnx6, hleaf6⟩
  simp only [List.length_range] at ht6 hnx6
  have hx06 := hx05.trans hx6
  -- the free subterms
  have hL : ∀ v, Sub U (conjOf (storeEntries R) v) := by
    intro v m hm
    rw [conjOf_storeEntries] at hm
    by_cases hv : v < R.c.length
    · exact hC.names m ((hsh.up v hv m).1 hm).1
    · rw [Sorts.Raw.Normal.conj_of_ge R (Nat.le_of_not_lt hv)] at hm
      simp at hm
  step with free_subterms_spec hC hr hq hUz (storeEntries R) hL
    (RwLog.firsts (encX nm (exEqns Y)).vars) hsh.fo R.c.length s6 decls names rep.t xv es next
    hI6 (hx06.repr hd) (hx06.repr hU) (hx06.repr hrep.t) (hx6.repr rxv)
    ((hx4.trans (hx5.trans hx6)).repr res') hnx6 (by unfold Room; omega)
    as ⟨found, es1, s7, hI7, hx7, ht7, Sn, Fl, rF, rE, hG⟩
  have hx07 := hx06.trans hx7
  have hfree : ∀ u ∈ R.t.subs, u.firstOrder = true →
      (FreeAt S U (storeEntries R) (RwLog.firsts (encX nm (exEqns Y)).vars) R.t u ↔
        Sorts.freeB S R u = true) := fun u _ _ => free_iff hC hUS hrep.y u
  have hNm := named_of hS hR hG hfree
  have hFlW : Fl.length ≤ R.t.subs.card := Nat.le_trans hG.fl hG.seen_le
  obtain ⟨him, -⟩ := fold_im (N := R.c.length) hG hfree hsh.fo
  -- the copy over their variables
  have rF' : Repr nm s7.nodes.val found.val
      (encList (nm none) (((fpairs R.c.length Fl).map fun p => (p.1, Term.var p.2)).map
        fun p => .app p.1 p.2)) := by
    rw [List.map_map]
    exact rF
  step with seed_spec hnm ((fpairs R.c.length Fl).map fun p => (p.1, Term.var p.2)) s7 found
    hI7 rF' (by simp only [List.length_map, fpairs_length]; unfold Room; omega)
    as ⟨s8, hI8, hn8, ht8, hm8, hB8, hA8a, hA8b⟩
  simp only [List.length_map, fpairs_length] at ht8
  step with clear_spec s8 .B hI8 (by unfold Room; omega) as ⟨s9, c1, c2, hI9, c4, c5⟩
  have hn9 : s9.nodes.val = s7.nodes.val := by rw [c1, hn8]
  have hx79 : Extends s7 s9 := Extends.of_eq hn9 (by omega)
  have hx09 := hx07.trans hx79
  have hA9 : tbl s9 .A = tbl s8 .A := c5 .A (by simp)
  have hM : MemoG nm s9.nodes.val (tbl s9 .A) (imF (fpairs R.c.length Fl)) := by
    intro k v hk
    rw [hA9] at hk
    obtain ⟨p, hp, hk1, hk2⟩ := hA8a k v hk
    obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hp
    refine ⟨q'.1, by rw [hn9]; exact hk1, ?_⟩
    rw [imF_some (mem_fpairs_lookup hG.fnd hq'), hn9]
    exact hk2
  have hg : ∀ t k, Repr nm s9.nodes.val k t → tbl s9 .A k = none →
      ImStep Term.var (imF (fpairs R.c.length Fl)) t := by
    intro t k hk hnone
    refine imF_none (lookup_fpairs_none fun hF => ?_)
    obtain ⟨w, hw⟩ := lookup_fpairs_some (N := R.c.length) hF
    rw [hA9] at hnone
    exact hA8b (t, Term.var w) (List.mem_map.2 ⟨(t, w), Sorts.mem_of_lookup hw, rfl⟩) k
      (by rw [← hn9]; exact hk) hnone
  have hleaf9 : LeafOK nm s9.nodes.val (tbl s9 .B) term.Leaf.Map Term.var :=
    ⟨fun q u h => (by rw [c4 q] at h; cases h), fun v _ => rfl⟩
  have hpend9 := pending_card_le (nm := nm) s9.nodes.val (tbl s9 .A) R.t.subs
  step with rebuild_g_spec hnm s9 .Map rep.t (t := R.t) (σ := Term.var)
    (im := imF (fpairs R.c.length Fl)) R.t.subs hI9 (hx09.repr hrep.t) hleaf9 hM hg
    (Finset.Subset.refl _) (by unfold Room; omega) as ⟨t1, s10, hG10⟩
  have ht10 : s10.ticks.val ≤ s9.ticks.val + 5 + 14 * R.t.subs.card := by
    have := hG10.cost
    omega
  have hx010 := hx09.trans hG10.ext
  have rt1 := hG10.repr
  rw [him] at rt1
  -- the names, their numbers and their sorts
  have hvars1 : ((Sorts.foldVc S R R.t).rename (fnum (fpairs R.c.length Fl))).vars =
      (Sorts.foldVc S R R.t).vars.map (fnum (fpairs R.c.length Fl)) := Term.vars_rename _ _
  have hfirsts : RwLog.firsts ((Sorts.foldVc S R R.t).rename (fnum (fpairs R.c.length Fl))).vars =
      (Sorts.foldNames S R).map (fnum (fpairs R.c.length Fl)) := by
    rw [hvars1, RwLog.firsts_map _ _ hNm.inj]
    rfl
  have hsize : ((Sorts.foldVc S R R.t).rename (fnum (fpairs R.c.length Fl))).size =
      (Sorts.foldStore S R).t.size := by
    rw [size_rename]
    show _ = ((Sorts.foldVc S R R.t).rename fun p => (Sorts.foldNames S R).idxOf p).size
    rw [size_rename]
  have hcard1 := Term.card_subs_le_size
    ((Sorts.foldVc S R R.t).rename (fnum (fpairs R.c.length Fl)))
  rw [hsize] at hcard1
  step with firsts_spec hnm s10 t1 hG10.inv rt1
    (by unfold Room firstsCost; rw [hfirsts, List.length_map]; omega)
    as ⟨ks, s11, hI11, hx11, ht11, rks⟩
  unfold firstsCost at ht11
  rw [hfirsts, List.length_map] at ht11
  rw [hfirsts] at rks
  have hL1len : (foundEntries S U (storeEntries R) R.c.length Fl).length =
      Fl.length + R.c.length := by
    simp [foundEntries, fpairs_length, storeEntries_length]
  have hmul : (Sorts.foldNames S R).length * (3 * (Fl.length + R.c.length) + 4) ≤
      (Sorts.foldNames S R).length * (3 * (R.t.subs.card + R.c.length) + 4) :=
    Nat.mul_le_mul_left _ (by omega)
  step with conjs_at_spec (U := U) (foundEntries S U (storeEntries R) R.c.length Fl)
    ((Sorts.foldNames S R).map (fnum (fpairs R.c.length Fl))) s11 es1 ks hI11
    ((hx79.trans (hG10.ext.trans hx11)).repr rE) rks
    (by unfold Room conjsAtCost; rw [List.length_map, hL1len]; omega)
    as ⟨cs, s12, hI12, hx12, ht12, rcs⟩
  unfold conjsAtCost at ht12
  rw [List.length_map, hL1len] at ht12
  have hcs : ((Sorts.foldNames S R).map (fnum (fpairs R.c.length Fl))).map
      (fun k => cpat (nm none) U (conjOf (foundEntries S U (storeEntries R) R.c.length Fl) k)) =
      ((Sorts.foldNames S R).map (Sorts.foldConj S R)).map (cpat (nm none) U) := by
    rw [List.map_map, List.map_map]
    refine List.map_congr_left fun p hp => ?_
    simp only [Function.comp_apply]
    rw [hNm.conj hC hUS hG p (((RwLog.firsts_spec _).2.1 p).1 hp)]
  rw [hcs] at rcs
  have hKnd : ((Sorts.foldNames S R).map (fnum (fpairs R.c.length Fl))).Nodup :=
    List.Nodup.map_on (fun a ha b hb e => hNm.inj a (((RwLog.firsts_spec _).2.1 a).1 ha) b
      (((RwLog.firsts_spec _).2.1 b).1 hb) e) hN.nodup
  step with number_spec ((Sorts.foldNames S R).map (fnum (fpairs R.c.length Fl))) hKnd s12 ks
    hI12 (hx12.repr rks) (by rw [List.length_map]; unfold Room; omega)
    as ⟨nx, s13, hI13, hx13, ht13, hA13, hnx13, hleaf13⟩
  rw [List.length_map] at ht13
  step with clear_spec s13 .A hI13 (by unfold Room; omega) as ⟨s14, d1, d2, hI14, d4, d5⟩
  have hx1314 : Extends s13 s14 := Extends.of_eq d1 (by omega)
  have hB14 : tbl s14 .B = tbl s13 .B := d5 .B (by simp)
  have hleaf14 : LeafOK nm s14.nodes.val (tbl s14 .B) term.Leaf.Map
      (numSub ((Sorts.foldNames S R).map (fnum (fpairs R.c.length Fl)))) := by
    rw [hB14, d1]
    exact hleaf13
  have hx1014 : Extends s10 s14 := hx11.trans (hx12.trans (hx13.trans hx1314))
  have hpend14 := pending_card_le (nm := nm) s14.nodes.val (tbl s14 .A)
    ((Sorts.foldVc S R R.t).rename (fnum (fpairs R.c.length Fl))).subs
  step with rebuild_spec hnm s14 .Map t1
    (σ := numSub ((Sorts.foldNames S R).map (fnum (fpairs R.c.length Fl))))
    ((Sorts.foldVc S R R.t).rename (fnum (fpairs R.c.length Fl))).subs hI14 (hx1014.repr rt1)
    hleaf14 (fun k v h => by rw [d4 k] at h; cases h) (Finset.Subset.refl _)
    (by unfold Room; omega) as ⟨t2, s15, hP15⟩
  have ht15 : s15.ticks.val ≤ s14.ticks.val + 5 + 14 * (Sorts.foldStore S R).t.size := by
    have := hP15.cost
    omega
  have hx415 : Extends s4 s15 :=
    ((((hx5.trans hx6).trans hx7).trans hx79).trans hG10.ext).trans (hx1014.trans hP15.ext)
  have hpend15 := pending_card_le (nm := nm) s15.nodes.val (tbl s15 .A)
    (encX nm (exEqns Y)).subs
  step with rebuild_spec hnm s15 .Map ms
    (σ := numSub ((Sorts.foldNames S R).map (fnum (fpairs R.c.length Fl))))
    (encX nm (exEqns Y)).subs hP15.inv (hx415.repr rms)
    (by rw [hP15.tblB]; exact hleaf14.extends hP15.ext) hP15.memo (Finset.Subset.refl _)
    (by unfold Room; omega) as ⟨x2, s16, hP16⟩
  have ht16 : s16.ticks.val ≤ s15.ticks.val + 5 + 14 * (encX nm (exEqns Y)).subs.card := by
    have := hP16.cost
    omega
  have hx016 : Extends s s16 := ((hx010.trans hx1014).trans hP15.ext).trans hP16.ext
  -- what was built is what the folded store is assembled from
  have hKmem : ∀ p ∈ (Sorts.foldVc S R R.t).vars, fnum (fpairs R.c.length Fl) p ∈
      (Sorts.foldNames S R).map (fnum (fpairs R.c.length Fl)) :=
    fun p hp => List.mem_map.2 ⟨p, ((RwLog.firsts_spec _).2.1 p).2 hp, rfl⟩
  have hidx : ∀ p ∈ (Sorts.foldVc S R R.t).vars,
      ((Sorts.foldNames S R).map (fnum (fpairs R.c.length Fl))).idxOf
        (fnum (fpairs R.c.length Fl) p) = (Sorts.foldNames S R).idxOf p :=
    fun p hp => Sorts.idxOf_map_inj _ p _ fun a ha e =>
      hNm.inj a (((RwLog.firsts_spec _).2.1 a).1 ha) p hp e
  have hT2 : ((Sorts.foldVc S R R.t).rename (fnum (fpairs R.c.length Fl))).bind
      (numSub ((Sorts.foldNames S R).map (fnum (fpairs R.c.length Fl)))) =
      (Sorts.foldStore S R).t := by
    rw [bind_numSub (fun v hv => by
      rw [hvars1] at hv
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hv
      exact hKmem p hp)]
    show Term.bind _ (Term.bind _ _) = Term.bind _ _
    rw [Term.bind_bind]
    exact Term.bind_congr fun p hp => by
      simp only [Term.bind_var]
      rw [hidx p hp]
  have hvarF : ∀ θ ∈ Y, ∀ x ∈ (Sorts.eqnsOf θ).vars,
      Term.var x ∈ (Sorts.foldVc S R R.t).vars ∧ fnum (fpairs R.c.length Fl) (.var x) = x := by
    intro θ hθ x hx
    have h1 : Term.var x ∈ (Sorts.foldVc S R R.t).vars := by
      rw [hN.eq]
      exact hN.kept θ (by rw [← hrep.y]; exact List.mem_toFinset.2 hθ) x hx
    exact ⟨h1, fnum_var fun h => (hG.found _ h).2.1 x rfl⟩
  have hX2a := encX_numSub (nm := nm)
    (F := (Sorts.foldNames S R).map (fnum (fpairs R.c.length Fl))) (X := exEqns Y) (by
      intro E hE p hp
      have hE' : E ∈ Y.reverse.map Sorts.eqnsOf := hE
      obtain ⟨θ, hθ, rfl⟩ := List.mem_map.1 hE'
      have key : ∀ v ∈ p.1.vars ++ p.2.vars,
          v ∈ (Sorts.foldNames S R).map (fnum (fpairs R.c.length Fl)) := by
        intro v hv
        obtain ⟨h1, h2⟩ := hvarF θ (List.mem_reverse.1 hθ) v (List.mem_flatMap.2 ⟨p, hp, hv⟩)
        rw [← h2]
        exact hKmem _ h1
      exact ⟨fun v hv => key v (List.mem_append_left _ hv),
        fun v hv => key v (List.mem_append_right _ hv)⟩)
  have hX2b : (exEqns Y).map (Eqns.ren fun v =>
      ((Sorts.foldNames S R).map (fnum (fpairs R.c.length Fl))).idxOf v) = foldXl S R Y := by
    unfold foldXl
    refine List.map_congr_left fun E hE => ?_
    have hE' : E ∈ Y.reverse.map Sorts.eqnsOf := hE
    obtain ⟨θ, hθ, rfl⟩ := List.mem_map.1 hE'
    refine ren_congr fun p hp v hv => ?_
    obtain ⟨h1, h2⟩ := hvarF θ (List.mem_reverse.1 hθ) v (List.mem_flatMap.2 ⟨p, hp, hv⟩)
    rw [← hidx _ h1, h2]
  have rx2 := hP16.repr
  rw [hX2a, hX2b] at rx2
  have rt2 : Repr nm s16.nodes.val t2.val (Sorts.foldStore S R).t := by
    rw [← hT2]
    exact hP16.ext.repr hP15.repr
  have hXiff : ∀ E, E ∈ foldXl S R Y ↔ E ∈ Sorts.foldXs S R := fun E => mem_foldXl hrep.y
  obtain ⟨hXfo, hXv⟩ := Sorts.foldXs_fin hS hR
  obtain ⟨-, -, -, hnd⟩ := Sorts.assembled_fold hS hR hXiff
  have hcN : ∀ c ∈ (Sorts.foldNames S R).map (Sorts.foldConj S R), ∀ m ∈ c,
      m ∈ Sorts.names S := by
    intro c hc m hm
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc
    have hp' := ((RwLog.firsts_spec _).2.1 p).1 hp
    rcases hNm p hp' with ⟨x, rfl, hx, -⟩ | ⟨hF, -, -⟩
    · exact ((hsh.up x hx m).1 hm).1
    · rw [Sorts.foldConj_notVar (hG.found p hF).2.1] at hm
      exact (Sorts.mem_clo.1 hm).1
  refine WP.spec_mono (assemble_spec hnm hC hr (Sorts.foldStore S R).t
    ((Sorts.foldNames S R).map (Sorts.foldConj S R)) hcN (foldXl S R Y)
    (fun E hE => hXfo E ((hXiff E).1 hE))
    (fun E hE v hv => by rw [List.length_map]; exact hXv E ((hXiff E).1 hE) v hv) hnd
    s16 decls names t2 cs x2 hP16.inv (hx016.repr hd) (hx016.repr hU) rt2
    ((hx13.trans (hx1314.trans (hP15.ext.trans hP16.ext))).repr rcs) rx2
    (by unfold Room; omega)) ?_
  rintro ⟨res2, s'⟩ ⟨hI', hx', ht', hrep'⟩
  exact ⟨hI', hx016.trans hx', by unfold foldCost; omega, hrep'⟩

end RwLogVerified
