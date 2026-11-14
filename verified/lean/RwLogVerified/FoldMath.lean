/-
# What the steps of the fold compute

The facts that tie the steps of `sorts::fold` to the folded store of the
specification (`Sorts.foldRaw`): the equations read back from the list of
values of an exclusion are the equations of the exclusion; the copy of the
pattern over the variables of the free subterms found is the folded pattern
(`Sorts.foldVc`) with each name replaced by its number; and the entries give
the number of a name the sorts of the name (`Sorts.foldConj`).
-/
import RwLogVerified.FoldParts
import RwLog.Sorts.FoldRaw

namespace RwLogVerified

open rwlog_core RwLog

/-! ## The equations of an exclusion, from its values -/

/-- The equations read back from the values of a solved exclusion are its
equations. -/
theorem movedVals_vals {k : Nat} {θ : Sorts.Binds} (hθ : Sorts.Pre k θ) :
    movedVals (vals k θ) = Sorts.eqnsOf θ := by
  have hz : (List.range (vals k θ).length).zip (vals k θ) =
      (List.range k).map fun y => (y, PSubst.apply θ y) := by
    rw [vals_length]
    unfold vals
    exact List.map_prod_left_eq_zip.symm
  unfold movedVals
  rw [hz, movedOf_map]
  unfold Sorts.solvedOn Sorts.eqnsOf
  have hmem : ∀ y, y ∈ (List.range k).filter (fun y => decide (PSubst.apply θ y ≠ .var y)) ↔
      y ∈ θ.map Prod.fst := by
    intro y
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq, List.mem_map]
    constructor
    · rintro ⟨-, hne⟩
      rcases Sorts.apply_cases θ y with h | h
      · exact absurd h hne
      · exact ⟨_, h, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      refine ⟨hθ.dom b hb, ?_⟩
      rw [Sorts.apply_of_mem hθ.sorted hb]
      intro e
      exact Nat.lt_irrefl _ (hθ.later b hb b.1 e)
  have hs1 : ((List.range k).filter (fun y => decide (PSubst.apply θ y ≠ .var y))).Pairwise
      (· < ·) := List.pairwise_lt_range.filter _
  have hs2 : (θ.map Prod.fst).Pairwise (· < ·) := List.pairwise_map.2 hθ.sorted
  have hkeys : (List.range k).filter (fun y => decide (PSubst.apply θ y ≠ .var y)) =
      θ.map Prod.fst :=
    List.Perm.eq_of_pairwise (le := fun a b : Nat => a < b)
      (fun a b _ _ h1 h2 => absurd h1 (Nat.lt_asymm h2)) hs1 hs2
      ((List.perm_ext_iff_of_nodup (hs1.imp fun h => Nat.ne_of_lt h)
        (hs2.imp fun h => Nat.ne_of_lt h)).2 hmem)
  rw [hkeys, List.map_map]
  exact List.map_congr_left fun b hb => by simp [Sorts.apply_of_mem hθ.sorted hb]

/-! ## The numbers of the names -/

/-- The number of a name: the variable of a free subterm found, and a
variable for itself. -/
def fnum (P : List (Pat × Nat)) (p : Pat) : Nat :=
  match P.lookup p with
  | some w => w
  | none =>
    match p with
    | .var x => x
    | _ => 0

/-- A term with each outermost subterm that has a variable replaced by its
variable. -/
def imF (P : List (Pat × Nat)) : Pat → Pat
  | .var x =>
    match P.lookup (.var x) with
    | some w => .var w
    | none => .var x
  | .sym f =>
    match P.lookup (.sym f) with
    | some w => .var w
    | none => .sym f
  | .app a b =>
    match P.lookup (.app a b) with
    | some w => .var w
    | none => .app (imF P a) (imF P b)

theorem imF_some {P : List (Pat × Nat)} {t : Pat} {w : Nat} (h : P.lookup t = some w) :
    imF P t = .var w := by
  cases t <;> simp [imF, h]

theorem imF_none {P : List (Pat × Nat)} {t : Pat} (h : P.lookup t = none) :
    ImStep Term.var (imF P) t := by
  refine ⟨?_, ?_, ?_⟩
  · rintro v rfl; simp [imF, h]
  · rintro f rfl; simp [imF, h]
  · rintro a b rfl; simp [imF, h]

theorem lookup_fpairs_cons (N : Nat) (u0 : Pat) (Fl : List Pat) (u : Pat) :
    (fpairs N (u0 :: Fl)).lookup u =
      if u = u0 then some (N + Fl.length) else (fpairs N Fl).lookup u := by
  simp only [fpairs, List.lookup_cons]
  by_cases e : u = u0
  · simp [e]
  · have hb : (u == u0) = false := beq_eq_false_iff_ne.2 e
    rw [hb, ite_eq_right e]

theorem lookup_fpairs_none {N : Nat} : ∀ {Fl : List Pat} {u : Pat}, u ∉ Fl →
    (fpairs N Fl).lookup u = none
  | [], _, _ => rfl
  | u0 :: Fl, u, h => by
    have h1 : u ≠ u0 := fun e => h (e ▸ List.mem_cons_self)
    have h2 : u ∉ Fl := fun e => h (List.mem_cons_of_mem _ e)
    rw [lookup_fpairs_cons, ite_eq_right h1, lookup_fpairs_none h2]

theorem lookup_fpairs_lt {N : Nat} {Fl : List Pat} {u : Pat} {w : Nat}
    (h : (fpairs N Fl).lookup u = some w) : u ∈ Fl ∧ N ≤ w ∧ w < N + Fl.length :=
  mem_fpairs (Sorts.mem_of_lookup h)

theorem lookup_fpairs_some {N : Nat} : ∀ {Fl : List Pat} {u : Pat}, u ∈ Fl →
    ∃ w, (fpairs N Fl).lookup u = some w
  | [], _, h => by cases h
  | u0 :: Fl, u, h => by
    rw [lookup_fpairs_cons]
    by_cases e : u = u0
    · exact ⟨_, ite_eq_left e⟩
    · rw [ite_eq_right e]
      rcases List.mem_cons.1 h with h | h
      · exact absurd h e
      · exact lookup_fpairs_some h

theorem lookup_fpairs_inj {N : Nat} : ∀ {Fl : List Pat} {u u' : Pat} {w : Nat},
    (fpairs N Fl).lookup u = some w → (fpairs N Fl).lookup u' = some w → u = u'
  | [], _, _, _, h, _ => by simp [fpairs] at h
  | u0 :: Fl, u, u', w, h, h' => by
    rw [lookup_fpairs_cons] at h h'
    by_cases e : u = u0
    · by_cases e' : u' = u0
      · rw [e, e']
      · rw [ite_eq_left e] at h
        rw [ite_eq_right e'] at h'
        have := (lookup_fpairs_lt h').2.2
        simp only [Option.some.injEq] at h
        omega
    · by_cases e' : u' = u0
      · rw [ite_eq_right e] at h
        rw [ite_eq_left e'] at h'
        have := (lookup_fpairs_lt h).2.2
        simp only [Option.some.injEq] at h'
        omega
      · rw [ite_eq_right e] at h
        rw [ite_eq_right e'] at h'
        exact lookup_fpairs_inj h h'

theorem fnum_var {N : Nat} {Fl : List Pat} {x : Nat} (h : Term.var x ∉ Fl) :
    fnum (fpairs N Fl) (.var x) = x := by
  simp [fnum, lookup_fpairs_none h]

theorem fnum_found {N : Nat} {Fl : List Pat} {u : Pat} (h : u ∈ Fl) :
    (fpairs N Fl).lookup u = some (fnum (fpairs N Fl) u) ∧ N ≤ fnum (fpairs N Fl) u := by
  obtain ⟨w, hw⟩ := lookup_fpairs_some (N := N) h
  have : fnum (fpairs N Fl) u = w := by simp [fnum, hw]
  rw [this]
  exact ⟨hw, (lookup_fpairs_lt hw).2.1⟩

/-! ## A free subterm is not the function part of an application -/

theorem outF_self : ∀ u : Pat, Sorts.outF u u = u.vars
  | .var _ => rfl
  | .sym _ => rfl
  | .app h c => by
    have hc : c ≠ .app h c := fun e => by
      have := congrArg Term.size e
      simp only [Term.size] at this
      omega
    simp only [Sorts.outF, ite_eq_right hc, Term.vars]
    rw [Sorts.outF_eq_vars _ h (.inr (by simp only [Term.size]; omega)),
      Sorts.outF_eq_vars _ c (.inr (by simp only [Term.size]; omega))]

theorem outF_head {g b : Pat} : ∀ t : Pat, .app g b ∈ t.subs → ∀ y ∈ g.vars, y ∈ Sorts.outF g t
  | .var _, h, _, _ => by simp [Term.subs] at h
  | .sym _, h, _, _ => by simp [Term.subs] at h
  | .app c d, h, y, hy => by
    simp only [Term.subs, Finset.mem_insert, Finset.mem_union] at h
    simp only [Sorts.outF, List.mem_append]
    rcases h with h | h | h
    · simp only [Term.app.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .inl (by rw [outF_self]; exact hy)
    · exact .inl (outF_head c h y hy)
    · have hd : d ≠ g := fun e => by
        subst e
        have := Term.size_le_of_mem_subs h
        simp only [Term.size] at this
        omega
      exact .inr (by rw [ite_eq_right hd]; exact outF_head d h y hy)

/-- A subterm that is applied to an argument somewhere in the pattern is not
free: its variables are at a place outside it. -/
theorem not_free_head {S : Sorts} {U : List Name} {L : List (Nat × Sorts.Conj)} {XV : List Nat}
    {tp g b : Pat} (h : .app g b ∈ tp.subs) : ¬ FreeAt S U L XV tp g := by
  rintro ⟨-, hne, -, hin, -, -⟩
  obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ hne
  refine hin y hy ?_
  have htg : tp ≠ g := fun e => by
    subst e
    have := Term.size_le_of_mem_subs h
    simp only [Term.size] at this
    omega
  unfold Sorts.outV
  rw [ite_eq_right htg]
  exact outF_head tp h y hy

/-! ## The copy over the variables found is the folded pattern -/

section image

variable {S : Sorts} {U : List Name} {L : List (Nat × Sorts.Conj)} {XV : List Nat} {tp : Pat}
  {R : Sorts.Raw} {N : Nat} {Sn Fl : List Pat}

theorem fold_im_F (hG : SGo S U L XV tp [] Sn Fl)
    (hfree : ∀ u ∈ tp.subs, u.firstOrder = true →
      (FreeAt S U L XV tp u ↔ Sorts.freeB S R u = true)) :
    ∀ t : Pat, t ∈ tp.subs → t.firstOrder = true → t ∉ Fl →
      ((∀ v, t ≠ .var v) → ∀ a ∈ (unspine t []).2, a ∈ Sn) →
      imF (fpairs N Fl) t = (Sorts.foldFc S R t).rename (fnum (fpairs N Fl)) ∧
        ∀ p ∈ (Sorts.foldFc S R t).vars, (∃ x, p = .var x) ∨ p ∈ Fl
  | .var x, _, _, hF, _ => by
    refine ⟨?_, fun p hp => .inl ⟨x, by simpa [Sorts.foldFc, Term.vars] using hp⟩⟩
    rw [(imF_none (lookup_fpairs_none hF)).1 x rfl]
    simp [Sorts.foldFc, Term.rename, fnum_var hF]
  | .sym f, _, _, hF, _ => by
    refine ⟨?_, fun p hp => by simp [Sorts.foldFc, Term.vars] at hp⟩
    rw [(imF_none (lookup_fpairs_none hF)).2.1 f rfl]
    simp [Sorts.foldFc, Term.rename]
  | .app g b, hs, hfo, hF, hk => by
    obtain ⟨hgfo, hbfo, hgnv⟩ := firstOrder_app hfo
    have hgs := Term.subs_app_left hs
    have hbs := Term.subs_app_right hs
    have hgF : g ∉ Fl := fun h => not_free_head hs (hG.found g h).2
    have hargs : (unspine (.app g b) []).2 = (unspine g []).2 ++ [b] := by
      rw [unspine, unspine_append]
    have hkk := hk (by simp)
    rw [hargs] at hkk
    obtain ⟨ig, vg⟩ := fold_im_F hG hfree g hgs hgfo hgF
      (fun _ a ha => hkk a (List.mem_append_left _ ha))
    have hbSn : b ∈ Sn := hkk b (by simp)
    rw [(imF_none (lookup_fpairs_none hF)).2.2 g b rfl, ig]
    by_cases hb : Sorts.freeB S R b = true
    · have hbF : b ∈ Fl := hG.free b hbSn ((hfree b hbs hbfo).2 hb)
      refine ⟨?_, fun p hp => ?_⟩
      · rw [imF_some (fnum_found hbF).1]
        simp [Sorts.foldFc, hb, Term.rename]
      · simp only [Sorts.foldFc, hb, ↓reduceIte, Term.vars, List.mem_append,
          List.mem_singleton] at hp
        rcases hp with hp | rfl
        · exact vg p hp
        · exact .inr hbF
    · have hbF : b ∉ Fl := fun h => hb ((hfree b hbs hbfo).1 (hG.found b h).2)
      obtain ⟨ib, vb⟩ := fold_im_F hG hfree b hbs hbfo hbF (fun hnv a ha => by
        rcases hG.kids b hbSn hnv hbF a ha with h | h
        · exact h
        · cases h)
      refine ⟨?_, fun p hp => ?_⟩
      · rw [ib]
        simp [Sorts.foldFc, hb, Term.rename]
      · simp only [Sorts.foldFc, hb, Bool.false_eq_true, ↓reduceIte, Term.vars,
          List.mem_append] at hp
        rcases hp with hp | hp
        · exact vg p hp
        · exact vb p hp

/-- The copy of the pattern over the variables of the free subterms found is
the folded pattern with each name replaced by its number, and every name is
a variable or a free subterm found. -/
theorem fold_im (hG : SGo S U L XV tp [] Sn Fl)
    (hfree : ∀ u ∈ tp.subs, u.firstOrder = true →
      (FreeAt S U L XV tp u ↔ Sorts.freeB S R u = true)) (htfo : tp.firstOrder = true) :
    imF (fpairs N Fl) tp = (Sorts.foldVc S R tp).rename (fnum (fpairs N Fl)) ∧
      ∀ p ∈ (Sorts.foldVc S R tp).vars, (∃ x, p = .var x) ∨ p ∈ Fl := by
  have hroot : tp ∈ Sn := by
    rcases hG.root with h | h
    · exact h
    · cases h
  unfold Sorts.foldVc
  by_cases hb : Sorts.freeB S R tp = true
  · have hF : tp ∈ Fl := hG.free tp hroot ((hfree tp (Term.self_mem_subs _) htfo).2 hb)
    rw [ite_eq_left hb, imF_some (fnum_found hF).1]
    exact ⟨by simp [Term.rename], fun p hp => by
      simp only [Term.vars, List.mem_singleton] at hp
      exact .inr (hp ▸ hF)⟩
  · have hF : tp ∉ Fl := fun h => hb ((hfree tp (Term.self_mem_subs _) htfo).1 (hG.found tp h).2)
    rw [ite_eq_right hb]
    exact fold_im_F hG hfree tp (Term.self_mem_subs _) htfo hF (fun hnv a ha => by
      rcases hG.kids tp hroot hnv hF a ha with h | h
      · exact h
      · cases h)

end image

/-! ## The sorts the entries give the numbers -/

theorem conjOf_append_of_not {A B : List (Nat × Sorts.Conj)} {v : Nat} (h : ∀ e ∈ A, e.1 ≠ v) :
    conjOf (A ++ B) v = conjOf B v := by
  induction A with
  | nil => rfl
  | cons e A ih =>
    rw [List.cons_append, conjOf_cons,
      ite_eq_right (fun e' => h e List.mem_cons_self e'.symm),
      ih fun e' he' => h e' (List.mem_cons_of_mem _ he')]

/-- The entries give a variable under the first new one what they gave it. -/
theorem conjOf_found_var {S : Sorts} {U : List Name} {L : List (Nat × Sorts.Conj)} {N : Nat}
    {Fl : List Pat} {x : Nat} (hx : x < N) :
    conjOf (foundEntries S U L N Fl) x = conjOf L x := by
  unfold foundEntries
  refine conjOf_append_of_not fun e he => ?_
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
  have := (mem_fpairs hp).2.1
  show p.2 ≠ x
  omega

/-- The entries give the variable of a free subterm found the sorts of the
subterm. -/
theorem conjOf_found {S : Sorts} {U : List Name} {L : List (Nat × Sorts.Conj)} {N : Nat} :
    ∀ {Fl : List Pat} {u : Pat} {w : Nat}, (fpairs N Fl).lookup u = some w →
      conjOf (foundEntries S U L N Fl) w = cloOf S U L u
  | [], _, _, h => by simp [fpairs] at h
  | u0 :: Fl, u, w, h => by
    rw [lookup_fpairs_cons] at h
    unfold foundEntries
    simp only [fpairs, List.map_cons, List.cons_append]
    rw [conjOf_cons]
    by_cases e : u = u0
    · rw [ite_eq_left e] at h
      simp only [Option.some.injEq] at h
      subst h
      simp [e]
    · rw [ite_eq_right e] at h
      have hlt := (lookup_fpairs_lt h).2.2
      have hne : w ≠ N + Fl.length := by omega
      simp only [hne, ↓reduceIte]
      exact conjOf_found h

end RwLogVerified
