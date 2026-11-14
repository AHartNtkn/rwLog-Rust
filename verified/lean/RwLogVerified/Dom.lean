/-
# The sorts as the constraint domain, on the store

A representative on the store is the folded canonical store of a
representative of the specification (`Sorts.FoldOf`), as `sorts::normal`
returns it. Each operation of the domain states a problem with the solutions
of its arguments and takes its folded canonical store: `dom::one` a pair of
patterns over the solutions of one store, and `dom::compose` and `dom::meet`
a pattern and equations over the solutions of two, the variables of the
first sent to the even and those of the second to the odd numbers. The
problem relates the pairs the operation of the specification is to relate
(`oneProb_rel`, `compose_rel`, `meet_rel`), and the representative of a
relation is unique (`Sorts.Rep.mk?`). The pair symbol is reserved: no sort
has a case for it (`Sorts.NoPair`).
-/
import RwLogVerified.Normal
import RwLog.Sorts.Dom
import RwLog.Sorts.FoldRep

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

/-- The sorts and the exclusions of a store, written as a problem
has them and with the variables renamed, hold of a substitution exactly
when it is, on the variables as renamed, a solution of the store. -/
theorem parts_sol {S : Sorts} {U : List Name} (hU : ∀ n ∈ Sorts.names S, n ∈ U) {r : Sorts.Raw}
    (hr : r.Shaped S) {Y : List Sorts.Binds} (hY : Y.toFinset = r.x) (f : Nat → Nat)
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

theorem mem_atomsOnto_out {U : List Name} {a : Name × Pat} {cs : List Sorts.Conj}
    {vs : List Pat} {out : List (Name × Pat)} :
    a ∈ atomsOnto U cs vs out ↔ a ∈ atomsOnto U cs vs [] ∨ a ∈ out := by
  rw [mem_atomsOnto, mem_atomsOnto (out := [])]
  simp only [List.not_mem_nil, false_or]
  exact or_comm

theorem exclsOnto_out (vs : List Pat) (X : List (List Pat)) (out : List (Eqns Nat)) :
    exclsOnto vs X out = exclsOnto vs X [] ++ out := by
  simp [exclsOnto]

theorem atomsOnto_fo {U : List Name} {cs : List Sorts.Conj} {vs : List Pat}
    (hvs : ∀ v ∈ vs, v.firstOrder = true) :
    ∀ a ∈ atomsOnto U cs vs [], a.2.firstOrder = true := by
  intro a ha
  rcases mem_atomsOnto.1 ha with ha | ⟨i, h, h', e, -, -⟩
  · simp at ha
  · rw [e]; exact hvs _ (List.getElem_mem h')

theorem atomsOnto_names {S : Sorts} {r : Sorts.Raw} (hr : r.Shaped S) {U : List Name}
    {vs : List Pat} : ∀ a ∈ atomsOnto U r.c vs [], a.1 ∈ Sorts.names S := by
  intro a ha
  rcases mem_atomsOnto.1 ha with ha | ⟨i, h, h', -, -, hn⟩
  · simp at ha
  · refine ((hr.up i h a.1).1 ?_).1
    simpa [Sorts.Raw.conj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h] using hn

theorem exclsOnto_fo {vs : List Pat} {X : List (List Pat)}
    (hvs : ∀ v ∈ vs, v.firstOrder = true) (hX : ∀ L ∈ X, ∀ p ∈ L, p.firstOrder = true) :
    ∀ E ∈ exclsOnto vs X [], E.FO := by
  intro E hE p hp
  simp only [exclsOnto, List.append_nil, List.mem_reverse, List.mem_map] at hE
  obtain ⟨L, hL, rfl⟩ := hE
  have := List.of_mem_zip (show (p.1, p.2) ∈ vs.zip L from hp)
  exact ⟨hvs _ this.1, hX L hL _ this.2⟩

theorem rename_id : ∀ t : Pat, t.rename id = t
  | .var _ => rfl
  | .sym _ => rfl
  | .app a b => by
    show Term.app (a.rename id) (b.rename id) = _
    rw [rename_id a, rename_id b]

/-- The variables of a store of `k` variables, renamed. -/
def partVs (g : Nat → Nat) (k : Nat) : List Pat := (varsTo k).map (Term.rename g)

/-- The exclusions of a store of `k` variables, each the list of its
values, renamed. -/
def partXs (g : Nat → Nat) (k : Nat) (Y : List Sorts.Binds) : List (List Pat) :=
  (Y.map (vals k)).map (List.map (Term.rename g))

theorem rename_id_fun : (Term.rename id : Pat → Pat) = id := funext rename_id

theorem partVs_id (k : Nat) : partVs id k = varsTo k := by
  rw [partVs, rename_id_fun, List.map_id]

theorem partXs_id (k : Nat) (Y : List Sorts.Binds) : partXs id k Y = Y.map (vals k) := by
  rw [partXs, rename_id_fun, List.map_id_fun, List.map_id]

theorem partVs_fo (g : Nat → Nat) (k : Nat) : ∀ v ∈ partVs g k, v.firstOrder = true := by
  intro v hv
  simp only [partVs, varsTo, List.map_map, List.mem_map, List.mem_range] at hv
  obtain ⟨i, -, rfl⟩ := hv
  rfl

theorem partXs_fo {S : Sorts} {r : Sorts.Raw} (hr : r.Shaped S) {Y : List Sorts.Binds}
    (hY : Y.toFinset = r.x) (g : Nat → Nat) :
    ∀ L ∈ partXs g r.c.length Y, ∀ p ∈ L, p.firstOrder = true := by
  intro L hL p hp
  simp only [partXs, List.map_map, List.mem_map] at hL
  obtain ⟨θ, hθ, rfl⟩ := hL
  simp only [Function.comp_apply, vals, List.map_map, List.mem_map, List.mem_range] at hp
  obtain ⟨i, -, rfl⟩ := hp
  have hθ' : θ ∈ r.x := by rw [← hY]; exact List.mem_toFinset.2 hθ
  exact Sorts.rename_fo (Sorts.Pre.apply_fo (hr.ex θ hθ').toPre i) g

theorem partXs_len (g : Nat → Nat) (k : Nat) (Y : List Sorts.Binds) :
    ∀ L ∈ partXs g k Y, (partVs g k).length ≤ L.length := by
  intro L hL
  simp only [partXs, List.map_map, List.mem_map] at hL
  obtain ⟨θ, -, rfl⟩ := hL
  simp [partVs]

/-! ## The problems the operations state -/

/-- The problem `dom::one` states: the pair of two patterns under the sorts
and the exclusions of a representative. -/
noncomputable def oneProb (U : List Name) (r : Sorts.Raw) (Y : List Sorts.Binds) (u w : Pat) :
    Sorts.Prob :=
  ⟨Sorts.tpair u w, [], atomsOnto U r.c (partVs id r.c.length) [],
    exclsOnto (partVs id r.c.length) (partXs id r.c.length Y) []⟩

theorem oneProb_fo {S : Sorts} {U : List Name} {r : Sorts.Raw} (hr : r.Shaped S)
    {Y : List Sorts.Binds} (hY : Y.toFinset = r.x) {u w : Pat} (hu : u.firstOrder = true)
    (hw : w.firstOrder = true) : (oneProb U r Y u w).FO :=
  ⟨by show (Sorts.tpair u w).firstOrder = true; rw [Sorts.tpair_fo, hu, hw]; rfl,
    fun p hp => by simp [oneProb] at hp, atomsOnto_fo (partVs_fo _ _),
    exclsOnto_fo (partVs_fo _ _) (partXs_fo hr hY _)⟩

theorem oneProb_sol {S : Sorts} {U : List Name} (hU : ∀ n ∈ Sorts.names S, n ∈ U) {r : Sorts.Raw}
    (hr : r.Shaped S) {Y : List Sorts.Binds} (hY : Y.toFinset = r.x) (u w : Pat)
    (σ : Nat → GTerm) : σ ∈ (oneProb U r Y u w).Sol S ↔ σ ∈ r.store.Sol S := by
  have := parts_sol hU hr hY id σ
  rw [Function.comp_id] at this
  rw [← this]
  exact ⟨fun h => h.2, fun h => ⟨fun p hp => by simp [oneProb] at hp, h⟩⟩

/-- The pairs the problem `dom::one` states relates. -/
theorem oneProb_rel {S : Sorts} {U : List Name} (hU : ∀ n ∈ Sorts.names S, n ∈ U) {r : Sorts.Raw}
    (hr : r.Shaped S) {Y : List Sorts.Binds} (hY : Y.toFinset = r.x) (u w : Pat) :
    {p : GTerm × GTerm | Sorts.tpair p.1 p.2 ∈ (oneProb U r Y u w).Den S} =
      {p | ∃ σ ∈ r.store.Sol S, p.1 = u.bind σ ∧ p.2 = w.bind σ} := by
  ext p
  constructor
  · rintro ⟨σ, hσ, e⟩
    exact ⟨σ, (oneProb_sol hU hr hY u w σ).1 hσ, Sorts.tpair_inj e⟩
  · rintro ⟨σ, hσ, e₁, e₂⟩
    exact ⟨σ, (oneProb_sol hU hr hY u w σ).2 hσ, by
      show _ = (Sorts.tpair u w).bind σ
      rw [Sorts.tpair_bind, e₁, e₂]⟩

/-- The pairs of the two sides of a store, swapped. -/
theorem swap_rel {S : Sorts} {r : Sorts.Raw} {lp rp : Pat} (ht : r.t = Sorts.tpair lp rp) :
    {p : GTerm × GTerm | ∃ σ ∈ r.store.Sol S, p.1 = rp.bind σ ∧ p.2 = lp.bind σ} =
      (r.rel S).inv := by
  rw [Sorts.Raw.rel_eq ht]
  ext p
  constructor
  · rintro ⟨σ, hσ, e₁, e₂⟩; exact ⟨σ, hσ, e₂, e₁⟩
  · rintro ⟨σ, hσ, e₁, e₂⟩; exact ⟨σ, hσ, e₂, e₁⟩

/-- The pairs of the right side of a store with itself. -/
theorem right_rel {S : Sorts} {r : Sorts.Raw} {lp rp : Pat} (ht : r.t = Sorts.tpair lp rp) :
    {p : GTerm × GTerm | ∃ σ ∈ r.store.Sol S, p.1 = rp.bind σ ∧ p.2 = rp.bind σ} =
      {p | p.2 = p.1 ∧ ∃ x, (x, p.1) ∈ r.rel S} := by
  rw [Sorts.Raw.rel_eq ht]
  ext p
  constructor
  · rintro ⟨σ, hσ, e₁, e₂⟩; exact ⟨e₂.trans e₁.symm, _, σ, hσ, rfl, e₁⟩
  · rintro ⟨e, x, σ, hσ, -, e₂⟩; exact ⟨σ, hσ, e₂, e.trans e₂⟩

/-- The two sides of a store over a pair are first order. -/
theorem sides_fo {S : Sorts} {r : Sorts.Raw} (hr : r.Shaped S) {lp rp : Pat}
    (ht : r.t = Sorts.tpair lp rp) : lp.firstOrder = true ∧ rp.firstOrder = true := by
  have := hr.fo
  rw [ht, Sorts.tpair_fo, Bool.and_eq_true] at this
  exact this

/-- The renaming of the variables of the first of two representatives. -/
def lren : Nat → Nat := fun v => 2 * v

/-- The renaming of the variables of the second of two representatives. -/
def rren : Nat → Nat := fun v => 2 * v + 1

/-- The problem `dom::compose` and `dom::meet` state: a pattern and
equations under the sorts and the exclusions of two representatives, the
variables of the first sent to the even numbers and those of the second to
the odd numbers. -/
noncomputable def twoProb (U : List Name) (a : Sorts.Raw) (Ya : List Sorts.Binds) (b : Sorts.Raw)
    (Yb : List Sorts.Binds) (t : Pat) (e : Eqns Nat) : Sorts.Prob :=
  ⟨t, e, atomsOnto U a.c (partVs lren a.c.length) (atomsOnto U b.c (partVs rren b.c.length) []),
    exclsOnto (partVs lren a.c.length) (partXs lren a.c.length Ya)
      (exclsOnto (partVs rren b.c.length) (partXs rren b.c.length Yb) [])⟩

theorem twoProb_fo {S : Sorts} {U : List Name} {a b : Sorts.Raw} (ha : a.Shaped S)
    (hb : b.Shaped S) {Ya Yb : List Sorts.Binds} (hYa : Ya.toFinset = a.x)
    (hYb : Yb.toFinset = b.x) {t : Pat} {e : Eqns Nat} (ht : t.firstOrder = true) (he : e.FO) :
    (twoProb U a Ya b Yb t e).FO := by
  refine ⟨ht, he, ?_, ?_⟩
  · intro x hx
    rcases mem_atomsOnto_out.1 hx with hx | hx
    · exact atomsOnto_fo (partVs_fo _ _) x hx
    · exact atomsOnto_fo (partVs_fo _ _) x hx
  · intro E hE
    change E ∈ exclsOnto _ _ _ at hE
    rw [exclsOnto_out] at hE
    rcases List.mem_append.1 hE with hE | hE
    · exact exclsOnto_fo (partVs_fo _ _) (partXs_fo ha hYa _) E hE
    · exact exclsOnto_fo (partVs_fo _ _) (partXs_fo hb hYb _) E hE

theorem twoProb_names {S : Sorts} {U : List Name} {a b : Sorts.Raw} (ha : a.Shaped S)
    (hb : b.Shaped S) {Ya Yb : List Sorts.Binds} {t : Pat} {e : Eqns Nat} :
    ∀ x ∈ (twoProb U a Ya b Yb t e).a, x.1 ∈ Sorts.names S := by
  intro x hx
  rcases mem_atomsOnto_out.1 hx with hx | hx
  · exact atomsOnto_names ha x hx
  · exact atomsOnto_names hb x hx

/-- The solutions of the problem `dom::compose` and `dom::meet` state: the
substitutions that satisfy the equations and are, on the even numbers, a
solution of the first store and, on the odd numbers, one of the second. -/
theorem twoProb_sol {S : Sorts} {U : List Name} (hU : ∀ n ∈ Sorts.names S, n ∈ U)
    {a b : Sorts.Raw} (ha : a.Shaped S) (hb : b.Shaped S) {Ya Yb : List Sorts.Binds}
    (hYa : Ya.toFinset = a.x) (hYb : Yb.toFinset = b.x) (t : Pat) (e : Eqns Nat)
    (σ : Nat → GTerm) :
    σ ∈ (twoProb U a Ya b Yb t e).Sol S ↔
      Eqns.Unifies σ e ∧ σ ∘ lren ∈ a.store.Sol S ∧ σ ∘ rren ∈ b.store.Sol S := by
  have h₁ := parts_sol hU ha hYa lren σ
  have h₂ := parts_sol hU hb hYb rren σ
  rw [← h₁, ← h₂]
  show (_ ∧ (∀ x ∈ atomsOnto _ _ _ _, _) ∧ ∀ E ∈ exclsOnto _ _ _, _) ↔ _
  rw [exclsOnto_out]
  simp only [mem_atomsOnto_out (out := atomsOnto _ _ _ _), List.mem_append, partVs, partXs]
  constructor
  · rintro ⟨he, ha, hx⟩
    exact ⟨he, ⟨fun x hx' => ha x (.inl hx'), fun E hE => hx E (.inl hE)⟩,
      fun x hx' => ha x (.inr hx'), fun E hE => hx E (.inr hE)⟩
  · rintro ⟨he, ⟨ha₁, hx₁⟩, ha₂, hx₂⟩
    exact ⟨he, fun x hx' => hx'.elim (ha₁ x) (ha₂ x), fun E hE => hE.elim (hx₁ E) (hx₂ E)⟩

/-- The substitution that is one substitution on the even numbers and
another on the odd numbers. -/
def mix (σ₁ σ₂ : Nat → GTerm) : Nat → GTerm :=
  fun w => if w % 2 = 0 then σ₁ (w / 2) else σ₂ (w / 2)

theorem mix_l (σ₁ σ₂ : Nat → GTerm) : mix σ₁ σ₂ ∘ lren = σ₁ := by
  funext v
  have h1 : 2 * v % 2 = 0 := by omega
  have h2 : 2 * v / 2 = v := by omega
  show (if 2 * v % 2 = 0 then σ₁ (2 * v / 2) else σ₂ (2 * v / 2)) = σ₁ v
  rw [h1, h2]
  rfl

theorem mix_r (σ₁ σ₂ : Nat → GTerm) : mix σ₁ σ₂ ∘ rren = σ₂ := by
  funext v
  have h1 : (2 * v + 1) % 2 = 1 := by omega
  have h2 : (2 * v + 1) / 2 = v := by omega
  show (if (2 * v + 1) % 2 = 0 then σ₁ ((2 * v + 1) / 2) else σ₂ ((2 * v + 1) / 2)) = σ₂ v
  rw [h1, h2]
  rfl

/-- The problem `dom::compose` states relates the pairs of the composition
of the two stores. -/
theorem compose_rel {S : Sorts} {U : List Name} (hU : ∀ n ∈ Sorts.names S, n ∈ U)
    {a b : Sorts.Raw} (ha : a.Shaped S) (hb : b.Shaped S) {Ya Yb : List Sorts.Binds}
    (hYa : Ya.toFinset = a.x) (hYb : Yb.toFinset = b.x) {la ra lb rb : Pat}
    (hta : a.t = Sorts.tpair la ra) (htb : b.t = Sorts.tpair lb rb) :
    {p : GTerm × GTerm | Sorts.tpair p.1 p.2 ∈ (twoProb U a Ya b Yb
        (Sorts.tpair (la.rename lren) (rb.rename rren))
        [(ra.rename lren, lb.rename rren)]).Den S} = (a.rel S).comp (b.rel S) := by
  rw [Sorts.Raw.rel_eq hta, Sorts.Raw.rel_eq htb]
  ext p
  constructor
  · rintro ⟨σ, hσ, e⟩
    obtain ⟨hu, h₁, h₂⟩ := (twoProb_sol hU ha hb hYa hYb _ _ σ).1 hσ
    obtain ⟨e₁, e₂⟩ := Sorts.tpair_inj e
    have hm := hu _ List.mem_cons_self
    simp only [RwLog.rename_bind] at hm e₁ e₂
    exact ⟨ra.bind (σ ∘ lren), ⟨σ ∘ lren, h₁, e₁, rfl⟩, σ ∘ rren, h₂, hm, e₂⟩
  · rintro ⟨m, ⟨σ₁, hσ₁, e₁, e₂⟩, σ₂, hσ₂, e₃, e₄⟩
    refine ⟨mix σ₁ σ₂, (twoProb_sol hU ha hb hYa hYb _ _ _).2
      ⟨?_, by rw [mix_l]; exact hσ₁, by rw [mix_r]; exact hσ₂⟩, ?_⟩
    · intro q hq
      rw [List.mem_singleton] at hq; subst hq
      show (ra.rename lren).bind _ = (lb.rename rren).bind _
      rw [RwLog.rename_bind, RwLog.rename_bind, mix_l, mix_r]
      exact e₂.symm.trans e₃
    · show _ = Sorts.tpair ((la.rename lren).bind _) ((rb.rename rren).bind _)
      rw [RwLog.rename_bind, RwLog.rename_bind, mix_l, mix_r, ← e₁, ← e₄]

/-- The problem `dom::meet` states relates the pairs both stores relate. -/
theorem meet_rel {S : Sorts} {U : List Name} (hU : ∀ n ∈ Sorts.names S, n ∈ U)
    {a b : Sorts.Raw} (ha : a.Shaped S) (hb : b.Shaped S) {Ya Yb : List Sorts.Binds}
    (hYa : Ya.toFinset = a.x) (hYb : Yb.toFinset = b.x) {la ra lb rb : Pat}
    (hta : a.t = Sorts.tpair la ra) (htb : b.t = Sorts.tpair lb rb) :
    {p : GTerm × GTerm | Sorts.tpair p.1 p.2 ∈ (twoProb U a Ya b Yb
        (Sorts.tpair (la.rename lren) (ra.rename lren))
        [(la.rename lren, lb.rename rren), (ra.rename lren, rb.rename rren)]).Den S} =
      a.rel S ∩ b.rel S := by
  rw [Sorts.Raw.rel_eq hta, Sorts.Raw.rel_eq htb]
  ext p
  constructor
  · rintro ⟨σ, hσ, e⟩
    obtain ⟨hu, h₁, h₂⟩ := (twoProb_sol hU ha hb hYa hYb _ _ σ).1 hσ
    obtain ⟨e₁, e₂⟩ := Sorts.tpair_inj e
    have hm₁ := hu _ List.mem_cons_self
    have hm₂ := hu _ (List.mem_cons_of_mem _ List.mem_cons_self)
    simp only [RwLog.rename_bind] at hm₁ hm₂ e₁ e₂
    exact ⟨⟨σ ∘ lren, h₁, e₁, e₂⟩, σ ∘ rren, h₂, e₁.trans hm₁, e₂.trans hm₂⟩
  · rintro ⟨⟨σ₁, hσ₁, e₁, e₂⟩, σ₂, hσ₂, e₃, e₄⟩
    refine ⟨mix σ₁ σ₂, (twoProb_sol hU ha hb hYa hYb _ _ _).2
      ⟨?_, by rw [mix_l]; exact hσ₁, by rw [mix_r]; exact hσ₂⟩, ?_⟩
    · intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · show (la.rename lren).bind _ = (lb.rename rren).bind _
        rw [RwLog.rename_bind, RwLog.rename_bind, mix_l, mix_r]
        exact e₁.symm.trans e₃
      · show (ra.rename lren).bind _ = (rb.rename rren).bind _
        rw [RwLog.rename_bind, RwLog.rename_bind, mix_l, mix_r]
        exact e₂.symm.trans e₄
    · show _ = Sorts.tpair ((la.rename lren).bind _) ((ra.rename lren).bind _)
      rw [RwLog.rename_bind, RwLog.rename_bind, mix_l, ← e₁, ← e₂]

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
    sorts.eqns_of_loop s out vs l true ⦃ s' out' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + 4 * Vs.length + 1 ∧
        Repr nm s'.nodes.val out'.val (encEqs nm ((Vs.zip Ps).reverse ++ O)) ⦄ := by
  intro Vs
  induction Vs with
  | nil =>
    intro s out vs l Ps O hI hvs hl hout hlen hroom
    have hroom' := hroom
    unfold Room at hroom'
    unfold sorts.eqns_of_loop
    rw [loop]
    simp only [sorts.eqns_of_loop.body, ↓reduceIte]
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
      unfold sorts.eqns_of_loop
      rw [loop]
      simp only [sorts.eqns_of_loop.body, ↓reduceIte]
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
      unfold sorts.eqns_of_loop at IH
      refine WP.spec_mono IH ?_
      rintro ⟨s', out'⟩ ⟨hI', hx', ht', hr'⟩
      refine ⟨hI', hx04.trans hx', by simp only [List.length_cons]; omega, ?_⟩
      simpa using hr'

/-- `eqns_of` gives the equations of each variable with its value. -/
theorem eqns_of_spec (Vs Ps : List Pat) (s : store.Store) (vs l : store.TermId) (hI : Inv s)
    (hvs : Repr nm s.nodes.val vs.val (encList (nm none) Vs))
    (hl : Repr nm s.nodes.val l.val (encList (nm none) Ps)) (hlen : Vs.length ≤ Ps.length)
    (hroom : Room s (6 * Vs.length + 3)) :
    sorts.eqns_of s vs l ⦃ r s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + 6 * Vs.length + 3 ∧
        Repr nm s'.nodes.val r.val (encEqs nm (valEqns Vs Ps)) ⦄ := by
  unfold sorts.eqns_of
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
    sorts.excls_onto_loop xs s vs out ⦃ out' s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + Xs.length * (6 * Vs.length + 5) + 1 ∧
        Repr nm s'.nodes.val out'.val (encX nm (exclsOnto Vs Xs O)) ⦄ := by
  intro Xs
  induction Xs with
  | nil =>
    intro s xs out O hI hvs hxs hout hlen hroom
    have hroom' := hroom
    unfold Room at hroom'
    unfold sorts.excls_onto_loop
    rw [loop]
    simp only [sorts.excls_onto_loop.body]
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
    unfold sorts.excls_onto_loop
    rw [loop]
    simp only [sorts.excls_onto_loop.body]
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
    unfold sorts.excls_onto_loop at IH
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
    sorts.excls_onto s vs xs out ⦃ out' s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + Xs.length * (6 * Vs.length + 5) + 1 ∧
        Repr nm s'.nodes.val out'.val (encX nm (exclsOnto Vs Xs O)) ⦄ := by
  unfold sorts.excls_onto
  exact excls_onto_loop_spec Vs vs Xs s xs out O hI hvs hxs hout hlen hroom

/-! ## Representatives on the store -/

/-- What an operation that computes a representative returns: nothing when
the specification has none, and otherwise the folded canonical store of the
one of the specification. -/
def RepPost {S : Sorts} (nm : Option Nat → RwLog.Sym) (U : List Name) (nodes : List store.Node)
    (want : Option (Sorts.Rep S)) (res : Option sorts.Rep) : Prop :=
  match res with
  | none => want = none
  | some o => ∃ (ρ' : Sorts.Rep S) (r' : Sorts.Raw) (Y' : List Sorts.Binds),
      want = some ρ' ∧ Sorts.FoldOf S ρ'.1 r' ∧ RepAt nm U nodes o r' Y'

/-- What `normal` returns on a problem over a pair is the folded canonical
store of the representative of the pairs the problem relates. -/
theorem repPost_of {S : Sorts} (hS : S.WellFormed) {U : List Name} {nodes : List store.Node}
    {P : Sorts.Prob} (hP : P.FO) (ht : ∃ l r, P.t = Sorts.tpair l r) {X : PRel}
    (hX : {p : GTerm × GTerm | Sorts.tpair p.1 p.2 ∈ P.Den S} = X) {res : Option sorts.Rep}
    (h : NormalPost nm S hS U P nodes res) :
    RepPost nm U nodes (Sorts.Rep.mk? S X) res := by
  rw [← hX, ← Sorts.Rep.of_eq hS P hP ht]
  cases res with
  | none =>
    simp only [NormalPost] at h
    exact (Sorts.Rep.of_eq_none hS P hP ht).2 h
  | some o =>
    simp only [NormalPost] at h
    obtain ⟨n, r, Y, hn, hF, hrep⟩ := h
    obtain ⟨ρ', hρ', rfl⟩ := Sorts.Rep.of_val hS P hP ht hn
    exact ⟨ρ', r, Y, hρ', hF, hrep⟩

/-- `pair` gives the pair of two patterns. -/
theorem pair_spec (hz : nm none = "") (s : store.Store) (u w : store.TermId) {up wp : Pat}
    (hI : Inv s) (hu : Repr nm s.nodes.val u.val up) (hw : Repr nm s.nodes.val w.val wp)
    (hroom : Room s 3) :
    dom.pair s u w ⦃ t s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + 3 ∧
        Repr nm s'.nodes.val t.val (Sorts.tpair up wp) ⦄ := by
  unfold dom.pair
  have hroom' := hroom
  unfold Room at hroom'
  step with alloc_spec s .Nil hI trivial (by unfold Room; omega)
    as ⟨nil, s1, hI1, ht1, htb1, hx1, hr1⟩
  simp only [norm] at hr1
  step with alloc_spec s1 (.App nil u) hI1 ⟨(Repr.nil (nm := nm) hr1).lt, (hx1.repr hu).lt⟩
    (by unfold Room; omega) as ⟨h, s2, hI2, ht2, htb2, hx2, hr2⟩
  simp only [norm] at hr2
  have hx02 := hx1.trans hx2
  have rh : Repr nm s2.nodes.val h.val (Term.app (Term.sym (nm none)) up) :=
    .app hr2 (hx2.repr (.nil hr1)) (hx02.repr hu)
  refine WP.spec_mono (alloc_spec s2 (.App h w) hI2 ⟨rh.lt, (hx02.repr hw).lt⟩
    (by unfold Room; omega)) ?_
  rintro ⟨t, s3⟩ ⟨hI3, ht3, htb3, hx3, hr3⟩
  simp only [norm] at hr3
  refine ⟨hI3, hx02.trans hx3, by omega, ?_⟩
  have := Repr.app hr3 (hx3.repr rh) ((hx02.trans hx3).repr hw)
  rw [hz] at this
  exact this

/-- `sides` gives the two sides of a pair. -/
theorem sides_spec (s : store.Store) (t : store.TermId) {lp rp : Pat} (hI : Inv s)
    (ht : Repr nm s.nodes.val t.val (Sorts.tpair lp rp)) (hroom : Room s 2) :
    dom.sides s t ⦃ res s' =>
      Kept s s' 2 ∧ Repr nm s.nodes.val res.1.val lp ∧ Repr nm s.nodes.val res.2.val rp ⦄ := by
  unfold dom.sides
  have hroom' := hroom
  unfold Room at hroom'
  step with uncons_repr s t hI.toWf (p := Term.app (Term.app (Term.sym "") lp) rp) ht
    (by unfold Room; omega) as ⟨o, s1, hK0, hu⟩
  obtain ⟨h, r, rfl, rh, rr⟩ := hu
  have K1 := hK0.kept hI
  have ht1 := K1.ticks
  step with uncons_repr s1 h K1.inv.toWf (p := Term.app (Term.sym "") lp)
    (by rw [K1.nodes]; exact rh) (by unfold Room; omega) as ⟨o1, s2, hK1, hu1⟩
  obtain ⟨z, l, rfl, -, rl⟩ := hu1
  have K2 := hK1.kept K1.inv
  rw [K1.nodes] at rl
  have hfin : Kept s s2 2 ∧ Repr nm s.nodes.val l.val lp ∧ Repr nm s.nodes.val r.val rp :=
    ⟨⟨by rw [K2.nodes, K1.nodes], by rw [K2.tbl, K1.tbl], by rw [K2.ticks, K1.ticks],
      K2.inv⟩, rl, rr⟩
  step*

/-! ## One representative -/

/-- The ticks `one` may take before the normal store of its problem: for
`u` names, a representative of `k` variables and `y` exclusions. -/
def repOneCost (u k y : Nat) : Nat :=
  placesCost k + 1 + (k * (3 * u + 3) + 1) + (y * (6 * k + 5) + 1) + 3

/-- `one` computes the representative of a pair of patterns over the
solutions of a store. -/
theorem one_spec (hnm : Function.Injective nm) (hz : nm none = "") {S : Sorts} {sp : Pat}
    {U : List Name} (hC : Ctx nm S sp U) (hS : S.WellFormed)
    (hUS : ∀ n ∈ U, n ∈ Sorts.names S) {rc q : Nat}
    (hr : ∀ d, (Sorts.reachSet S d).card ≤ rc)
    (hq : ∀ d m, (Sorts.reachGSet S (d, some m)).card ≤ q) {r : Sorts.Raw}
    (hsh : r.Shaped S)
    (Y : List Sorts.Binds) {up wp : Pat} (hup : up.firstOrder = true)
    (hwp : wp.firstOrder = true)
    (s : store.Store) (decls names : store.TermId) (a : sorts.Rep) (u w : store.TermId)
    (hI : Inv s) (hde : Repr nm s.nodes.val decls.val sp)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (ha : RepAt nm U s.nodes.val a r Y) (hu : Repr nm s.nodes.val u.val up)
    (hw : Repr nm s.nodes.val w.val wp)
    (hroom : Room s (repOneCost U.length r.c.length Y.length +
      startCost nm S U.length (oneProb U r Y up wp) + normCharge nm S U rc q (oneProb U r Y up wp))) :
    dom.one s decls names a u w ⦃ res s' =>
      Inv s' ∧ Extends s s' ∧
        s'.ticks.val ≤ s.ticks.val + repOneCost U.length r.c.length Y.length +
          startCost nm S U.length (oneProb U r Y up wp) + normCharge nm S U rc q (oneProb U r Y up wp) ∧
        RepPost nm U s'.nodes.val (Sorts.Rep.mk? S
          {p | ∃ σ ∈ r.store.Sol S, p.1 = up.bind σ ∧ p.2 = wp.bind σ}) res ⦄ := by
  unfold dom.one
  have hroom' := hroom
  unfold Room at hroom'
  simp only [repOneCost] at hroom'
  step with places_spec (r.c.map (cpat (nm none) U)) s a.c hI ha.c
    (by simp only [List.length_map]; unfold Room; omega) as ⟨vs, s1, hI1, hx1, ht1, rvs⟩
  simp only [List.length_map] at ht1 rvs
  step with alloc_spec s1 .Nil hI1 trivial (by unfold Room; omega)
    as ⟨nil, s2, hI2, ht2, htb2, hx2, hr2⟩
  simp only [norm] at hr2
  have hx02 := hx1.trans hx2
  step with atoms_onto_spec U r.c (varsTo r.c.length) [] s2 a.c vs nil hI2
    (hx02.repr ha.c) (hx2.repr rvs) (.nil hr2) (by simp) (by unfold Room; omega)
    as ⟨atoms, s3, hI3, hx3, ht3, ratoms⟩
  have hx03 := hx02.trans hx3
  step with excls_onto_spec (varsTo r.c.length) (Y.map (vals r.c.length)) [] s3 vs a.x nil
    hI3 ((hx2.trans hx3).repr rvs) (hx03.repr ha.x) (hx3.repr (.nil hr2))
    (by intro L hL; obtain ⟨θ, -, rfl⟩ := List.mem_map.1 hL; simp)
    (by simp only [List.length_map, varsTo_length]; unfold Room; omega)
    as ⟨excl, s4, hI4, hx4, ht4, rexcl⟩
  simp only [List.length_map, varsTo_length] at ht4
  have hx04 := hx03.trans hx4
  step with pair_spec hz s4 u w hI4 (hx04.repr hu) (hx04.repr hw) (by unfold Room; omega)
    as ⟨t, s5, hI5, hx5, ht5, rt⟩
  have hx05 := hx04.trans hx5
  have hP := oneProb_fo (U := U) hsh ha.y hup hwp
  have ra' : Repr nm s5.nodes.val atoms.val
      (encList (nm none) ((oneProb U r Y up wp).a.map ppair)) := by
    simp only [oneProb, partVs_id]
    exact (hx4.trans hx5).repr ratoms
  have rx' : Repr nm s5.nodes.val excl.val (encX nm (oneProb U r Y up wp).x) := by
    simp only [oneProb, partVs_id, partXs_id]
    exact hx5.repr rexcl
  refine WP.spec_mono (normal_spec hnm hC hS hUS hr hq (oneProb U r Y up wp) hP
    (atomsOnto_names hsh) s5 decls names t nil atoms excl hI5 (hx05.repr hde)
    (hx05.repr hU) rt ((hx3.trans (hx4.trans hx5)).repr (.nil hr2)) ra' rx'
    (by unfold Room; omega)) ?_
  rintro ⟨res, s'⟩ ⟨hI', hx', ht', hpost⟩
  refine ⟨hI', hx05.trans hx', by simp only [repOneCost]; omega, ?_⟩
  exact repPost_of hS hP ⟨up, wp, rfl⟩ (oneProb_rel hC.names hsh ha.y up wp) hpost

/-! ## Two representatives -/

/-- A representative with its variables renamed, on the store. -/
structure HalfAt (nm : Option Nat → RwLog.Sym) (U : List Name) (nodes : List store.Node)
    (h : dom.Half) (g : Nat → Nat) (w : Sorts.Raw) (Y : List Sorts.Binds) (lp rp : Pat) :
    Prop where
  l : Repr nm nodes h.l.val (lp.rename g)
  r : Repr nm nodes h.r.val (rp.rename g)
  vs : Repr nm nodes h.vs.val (encList (nm none) (partVs g w.c.length))
  c : Repr nm nodes h.c.val (encList (nm none) (w.c.map (cpat (nm none) U)))
  x : Repr nm nodes h.x.val (encLL nm (partXs g w.c.length Y))

theorem HalfAt.extends {U : List Name} {s s' : store.Store} {h : dom.Half} {g : Nat → Nat}
    {r : Sorts.Raw} {Y : List Sorts.Binds} {lp rp : Pat}
    (hh : HalfAt nm U s.nodes.val h g r Y lp rp) (hx : Extends s s') :
    HalfAt nm U s'.nodes.val h g r Y lp rp :=
  ⟨hx.repr hh.l, hx.repr hh.r, hx.repr hh.vs, hx.repr hh.c, hx.repr hh.x⟩

/-- The subterms `half` rebuilds. -/
def halfSubs (nm : Option Nat → RwLog.Sym) (r : Sorts.Raw) (Y : List Sorts.Binds) : Finset Pat :=
  r.t.subs ∪ (encList (nm none) (varsTo r.c.length)).subs ∪
    (encLL nm (Y.map (vals r.c.length))).subs

/-- The ticks `half` may take. -/
def halfCost (nm : Option Nat → RwLog.Sym) (r : Sorts.Raw) (Y : List Sorts.Binds) : Nat :=
  placesCost r.c.length + 18 + 14 * (halfSubs nm r Y).card

/-- `half` renames the variables of a representative. -/
theorem half_spec (hnm : Function.Injective nm) {U : List Name} (s : store.Store)
    (f : term.Leaf) (g : Nat → Nat)
    (hf : ∀ nodes B, LeafOK nm nodes B f (fun v => Term.var (g v))) (a : sorts.Rep)
    {r : Sorts.Raw} {Y : List Sorts.Binds} {lp rp : Pat} (hI : Inv s)
    (ha : RepAt nm U s.nodes.val a r Y) (ht : r.t = Sorts.tpair lp rp)
    (hroom : Room s (halfCost nm r Y)) :
    dom.half s f a ⦃ h s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + halfCost nm r Y ∧
        HalfAt nm U s'.nodes.val h g r Y lp rp ⦄ := by
  unfold dom.half
  have hroom' := hroom
  unfold Room halfCost at hroom'
  step with places_spec (r.c.map (cpat (nm none) U)) s a.c hI ha.c
    (by simp only [List.length_map]; unfold Room; omega) as ⟨vs0, s0, hI0, hx0, ht0, rvs0⟩
  simp only [List.length_map] at ht0 rvs0
  step with clear_spec s0 .A hI0 (by unfold Room; omega) as ⟨s1, c1, c2, c3, c4, c5⟩
  have hx1 : Extends s0 s1 := Extends.of_eq c1 (by omega)
  have hx01 := hx0.trans hx1
  have hpc := pending_card_le (nm := nm) s1.nodes.val (tbl s1 .A) (halfSubs nm r Y)
  step with rebuild_spec hnm s1 f a.t (t := r.t) (σ := fun v => Term.var (g v))
    (halfSubs nm r Y) c3 (hx01.repr ha.t) (hf _ _)
    (by intro k v hk; rw [c4] at hk; cases hk)
    (fun w hw => by simp [halfSubs, hw]) (by unfold Room; omega) as ⟨t, s2, h2⟩
  have hc2 := h2.cost
  have hx2 := hx01.trans h2.ext
  step with rebuild_spec hnm s2 f vs0 (t := encList (nm none) (varsTo r.c.length))
    (σ := fun v => Term.var (g v)) (halfSubs nm r Y) h2.inv
    ((hx1.trans h2.ext).repr rvs0) (hf _ _) h2.memo
    (fun w hw => by simp [halfSubs, hw]) (by unfold Room; omega) as ⟨vs, s3, h3⟩
  have hc3 := h3.cost
  have hx3 := hx2.trans h3.ext
  step with rebuild_spec hnm s3 f a.x (t := encLL nm (Y.map (vals r.c.length)))
    (σ := fun v => Term.var (g v)) (halfSubs nm r Y) h3.inv (hx3.repr ha.x) (hf _ _) h3.memo
    (fun w hw => by simp [halfSubs, hw]) (by unfold Room; omega) as ⟨x, s4, h4⟩
  have hc4 := h4.cost
  have hx4 := hx3.trans h4.ext
  have rt : Repr nm s4.nodes.val t.val
      (Sorts.tpair (lp.rename g) (rp.rename g)) := by
    have := h4.ext.repr (h3.ext.repr h2.repr)
    rw [ht] at this
    exact this
  step with sides_spec s4 t h4.inv rt (by unfold Room; omega) as ⟨l, rr', s5, hK, rl, rr⟩
  have ht5 := hK.ticks
  have hx5 : Extends s4 s5 := Extends.of_eq hK.nodes (by omega)
  have hfin : Inv s5 ∧ Extends s s5 ∧ s5.ticks.val ≤ s.ticks.val + halfCost nm r Y ∧
      HalfAt nm U s5.nodes.val { l := l, r := rr', vs := vs, c := a.c, x := x } g r Y lp rp := by
    refine ⟨hK.inv, hx4.trans hx5, by unfold halfCost; omega, hx5.repr rl, hx5.repr rr, ?_,
      (hx4.trans hx5).repr ha.c, ?_⟩
    · have := hx5.repr (h4.ext.repr h3.repr)
      rw [encList_bind] at this
      exact this
    · have := hx5.repr h4.repr
      simp only [encLL, encList_bind, List.map_map] at this
      simp only [partXs, encLL, List.map_map]
      refine cast ?_ this
      congr 3
      funext θ
      simp only [Function.comp_apply, encList_bind]
      rfl
  step*

theorem lren_ok (nodes : List store.Node) (B : Nat → Option Nat) :
    LeafOK nm nodes B .Left (fun v => Term.var (lren v)) := rfl

theorem rren_ok (nodes : List store.Node) (B : Nat → Option Nat) :
    LeafOK nm nodes B .Right (fun v => Term.var (rren v)) := rfl

/-- The ticks `two` may take before the normal store of its problem: for
`u` names and representatives of `ka` and `kb` variables and `ya` and `yb`
exclusions. -/
def twoCost (u ka ya kb yb : Nat) : Nat :=
  1 + (kb * (3 * u + 3) + 1) + (ka * (3 * u + 3) + 1) + (yb * (6 * kb + 5) + 1) +
    (ya * (6 * ka + 5) + 1)

/-- `two` computes the normal store of a pattern and equations over the
solutions of two representatives whose variables are kept apart. -/
theorem two_spec (hnm : Function.Injective nm) {S : Sorts} {sp : Pat}
    {U : List Name} (hC : Ctx nm S sp U) (hS : S.WellFormed)
    (hUS : ∀ n ∈ U, n ∈ Sorts.names S) {rc q : Nat}
    (hr : ∀ d, (Sorts.reachSet S d).card ≤ rc)
    (hq : ∀ d m, (Sorts.reachGSet S (d, some m)).card ≤ q) {ra rb : Sorts.Raw}
    (hra : ra.Shaped S) (hrb : rb.Shaped S) {Ya Yb : List Sorts.Binds}
    (hYa : Ya.toFinset = ra.x) (hYb : Yb.toFinset = rb.x) {tp : Pat} {ep : Eqns Nat}
    (htp : tp.firstOrder = true) (hep : ep.FO)
    (s : store.Store) (decls names : store.TermId) (a b : dom.Half) (t e : store.TermId)
    {la ra' lb rb' : Pat} (hI : Inv s) (hde : Repr nm s.nodes.val decls.val sp)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (ha : HalfAt nm U s.nodes.val a lren ra Ya la ra')
    (hb : HalfAt nm U s.nodes.val b rren rb Yb lb rb')
    (ht : Repr nm s.nodes.val t.val tp) (he : Repr nm s.nodes.val e.val (encEqs nm ep))
    (hroom : Room s (twoCost U.length ra.c.length Ya.length rb.c.length Yb.length +
      startCost nm S U.length (twoProb U ra Ya rb Yb tp ep) + normCharge nm S U rc q (twoProb U ra Ya rb Yb tp ep))) :
    dom.two s decls names a b t e ⦃ res s' =>
      Inv s' ∧ Extends s s' ∧
        s'.ticks.val ≤ s.ticks.val +
          twoCost U.length ra.c.length Ya.length rb.c.length Yb.length +
          startCost nm S U.length (twoProb U ra Ya rb Yb tp ep) + normCharge nm S U rc q (twoProb U ra Ya rb Yb tp ep) ∧
        NormalPost nm S hS U (twoProb U ra Ya rb Yb tp ep) s'.nodes.val res ⦄ := by
  unfold dom.two
  have hroom' := hroom
  unfold Room at hroom'
  simp only [twoCost] at hroom'
  step with alloc_spec s .Nil hI trivial (by unfold Room; omega)
    as ⟨nil, s1, hI1, ht1, htb1, hx1, hr1⟩
  simp only [norm] at hr1
  step with atoms_onto_spec U rb.c (partVs rren rb.c.length) [] s1 b.c b.vs nil hI1
    (hx1.repr hb.c) (hx1.repr hb.vs) (.nil hr1) (by simp [partVs]) (by unfold Room; omega)
    as ⟨atomsb, s2, hI2, hx2, ht2, ratomsb⟩
  have hx02 := hx1.trans hx2
  step with atoms_onto_spec U ra.c (partVs lren ra.c.length) _ s2 a.c a.vs atomsb hI2
    (hx02.repr ha.c) (hx02.repr ha.vs) ratomsb (by simp [partVs]) (by unfold Room; omega)
    as ⟨atoms, s3, hI3, hx3, ht3, ratoms⟩
  have hx03 := hx02.trans hx3
  step with excls_onto_spec (partVs rren rb.c.length) (partXs rren rb.c.length Yb) [] s3 b.vs
    b.x nil hI3 (hx03.repr hb.vs) (hx03.repr hb.x) ((hx2.trans hx3).repr (.nil hr1))
    (partXs_len _ _ _)
    (by simp only [partXs, partVs, List.length_map, varsTo_length]; unfold Room; omega)
    as ⟨exclb, s4, hI4, hx4, ht4, rexclb⟩
  simp only [partXs, partVs, List.length_map, varsTo_length] at ht4
  have hx04 := hx03.trans hx4
  step with excls_onto_spec (partVs lren ra.c.length) (partXs lren ra.c.length Ya) _ s4 a.vs
    a.x exclb hI4 (hx04.repr ha.vs) (hx04.repr ha.x) rexclb (partXs_len _ _ _)
    (by simp only [partXs, partVs, List.length_map, varsTo_length]; unfold Room; omega)
    as ⟨excl, s5, hI5, hx5, ht5, rexcl⟩
  simp only [partXs, partVs, List.length_map, varsTo_length] at ht5
  have hx05 := hx04.trans hx5
  refine WP.spec_mono (normal_spec hnm hC hS hUS hr hq (twoProb U ra Ya rb Yb tp ep)
    (twoProb_fo hra hrb hYa hYb htp hep) (twoProb_names hra hrb) s5 decls names t e atoms
    excl hI5 (hx05.repr hde) (hx05.repr hU) (hx05.repr ht) (hx05.repr he)
    ((hx4.trans hx5).repr ratoms) rexcl (by unfold Room; omega)) ?_
  rintro ⟨res, s'⟩ ⟨hI', hx', ht', hpost⟩
  exact ⟨hI', hx05.trans hx', by simp only [twoCost]; omega, hpost⟩

/-- The problem `dom::compose` states. -/
noncomputable def composeProb (U : List Name) (ra rb : Sorts.Raw)
    (Ya Yb : List Sorts.Binds) : Sorts.Prob :=
  twoProb U ra Ya rb Yb (Sorts.tpair (ra.sides.1.rename lren) (rb.sides.2.rename rren))
    [(ra.sides.2.rename lren, rb.sides.1.rename rren)]

/-- The problem `dom::meet` states. -/
noncomputable def meetProb (U : List Name) (ra rb : Sorts.Raw)
    (Ya Yb : List Sorts.Binds) : Sorts.Prob :=
  twoProb U ra Ya rb Yb (Sorts.tpair (ra.sides.1.rename lren) (ra.sides.2.rename lren))
    [(ra.sides.1.rename lren, rb.sides.1.rename rren),
      (ra.sides.2.rename lren, rb.sides.2.rename rren)]

/-- The ticks `compose` and `meet` may take before the normal store of
their problem. -/
def halvesCost (nm : Option Nat → RwLog.Sym) (u : Nat) (ra : Sorts.Raw) (Ya : List Sorts.Binds)
    (rb : Sorts.Raw) (Yb : List Sorts.Binds) : Nat :=
  halfCost nm ra Ya + halfCost nm rb Yb + 8 +
    twoCost u ra.c.length Ya.length rb.c.length Yb.length

/-- `compose` computes the composition of two representatives
(`Sorts.Rep.compose`), from their folded canonical stores. -/
theorem dom_compose_spec (hnm : Function.Injective nm) (hz : nm none = "") {S : Sorts} {sp : Pat}
    {U : List Name} (hC : Ctx nm S sp U) (hN : Sorts.NoPair S)
    (hUS : ∀ n ∈ U, n ∈ Sorts.names S) {rc q : Nat}
    (hr : ∀ d, (Sorts.reachSet S d).card ≤ rc)
    (hq : ∀ d m, (Sorts.reachGSet S (d, some m)).card ≤ q) (ρa ρb : Sorts.Rep S)
    {ra rb : Sorts.Raw} (hfa : Sorts.FoldOf S ρa.1 ra) (hfb : Sorts.FoldOf S ρb.1 rb)
    (Ya Yb : List Sorts.Binds)
    (s : store.Store) (decls names : store.TermId) (a b : sorts.Rep)
    (hI : Inv s) (hde : Repr nm s.nodes.val decls.val sp)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (ha : RepAt nm U s.nodes.val a ra Ya) (hb : RepAt nm U s.nodes.val b rb Yb)
    (hroom : Room s (halvesCost nm U.length ra Ya rb Yb +
      startCost nm S U.length (composeProb U ra rb Ya Yb) +
      normCharge nm S U rc q (composeProb U ra rb Ya Yb))) :
    dom.compose s decls names a b ⦃ res s' =>
      Inv s' ∧ Extends s s' ∧
        s'.ticks.val ≤ s.ticks.val + halvesCost nm U.length ra Ya rb Yb +
          startCost nm S U.length (composeProb U ra rb Ya Yb) +
          normCharge nm S U rc q (composeProb U ra rb Ya Yb) ∧
        RepPost nm U s'.nodes.val (ρa.compose ρb) res ⦄ := by
  unfold dom.compose
  unfold composeProb at hroom ⊢
  have hroom' := hroom
  unfold Room at hroom'
  simp only [halvesCost] at hroom'
  obtain ⟨hta, -⟩ := ρa.fold_sides hN hfa
  obtain ⟨htb, -⟩ := ρb.fold_sides hN hfb
  obtain ⟨hla, hra⟩ := sides_fo hfa.1 hta
  obtain ⟨hlb, hrb⟩ := sides_fo hfb.1 htb
  step with half_spec hnm s .Left lren lren_ok a hI ha hta (by unfold Room; omega)
    as ⟨ha', s1, hI1, hx1, ht1, hha⟩
  step with half_spec hnm s1 .Right rren rren_ok b hI1 (hb.extends hx1) htb
    (by unfold Room; omega) as ⟨hb', s2, hI2, hx2, ht2, hhb⟩
  have hx02 := hx1.trans hx2
  have hha2 := hha.extends hx2
  step with alloc_spec s2 .Nil hI2 trivial (by unfold Room; omega)
    as ⟨nil, s3, hI3, ht3, htb3, hx3, hr3⟩
  simp only [norm] at hr3
  step with alloc_spec s3 (.App ha'.r hb'.l) hI3 ⟨(hx3.repr hha2.r).lt, (hx3.repr hhb.l).lt⟩
    (by unfold Room; omega) as ⟨e0, s4, hI4, ht4, htb4, hx4, hr4⟩
  simp only [norm] at hr4
  have hx34 := hx3.trans hx4
  step with alloc_spec s4 (.App e0 nil) hI4
    ⟨(List.getElem?_eq_some_iff.1 hr4).1, (hx4.repr (Repr.nil (nm := nm) hr3)).lt⟩
    (by unfold Room; omega) as ⟨e, s5, hI5, ht5, htb5, hx5, hr5⟩
  simp only [norm] at hr5
  have hx35 := hx34.trans hx5
  have re : Repr nm s5.nodes.val e.val
      (encEqs nm [(ra.sides.2.rename lren, rb.sides.1.rename rren)]) :=
    .app hr5 (hx5.repr (.app hr4 (hx34.repr hha2.r) (hx34.repr hhb.l)))
      ((hx4.trans hx5).repr (.nil hr3))
  step with pair_spec hz s5 ha'.l hb'.r hI5 (hx35.repr hha2.l) (hx35.repr hhb.r)
    (by unfold Room; omega) as ⟨t, s6, hI6, hx6, ht6, rt⟩
  have hx06 := (hx02.trans hx35).trans hx6
  have hfo : (Sorts.tpair (ra.sides.1.rename lren) (rb.sides.2.rename rren)).firstOrder = true := by
    rw [Sorts.tpair_fo, Sorts.rename_fo hla, Sorts.rename_fo hrb]; rfl
  have hefo : Eqns.FO [(ra.sides.2.rename lren, rb.sides.1.rename rren)] := fun p hp => by
    rw [List.mem_singleton] at hp; subst hp
    exact ⟨Sorts.rename_fo hra _, Sorts.rename_fo hlb _⟩
  refine WP.spec_mono (two_spec hnm hC ρa.wf hUS hr hq hfa.1 hfb.1 ha.y hb.y hfo hefo
    s6 decls names ha' hb' t e hI6 (hx06.repr hde) (hx06.repr hU)
    (hha2.extends (hx35.trans hx6)) (hhb.extends (hx35.trans hx6)) rt (hx6.repr re)
    (by unfold Room; omega)) ?_
  rintro ⟨res, s'⟩ ⟨hI', hx', ht', hpost⟩
  refine ⟨hI', hx06.trans hx', by simp only [halvesCost]; omega, ?_⟩
  rw [Sorts.Rep.compose_eq, ← hfa.rel, ← hfb.rel]
  exact repPost_of ρa.wf (twoProb_fo hfa.1 hfb.1 ha.y hb.y hfo hefo) ⟨_, _, rfl⟩
    (compose_rel hC.names hfa.1 hfb.1 ha.y hb.y hta htb) hpost

/-- `meet` computes the conjunction of two representatives
(`Sorts.Rep.meet`), from their folded canonical stores. -/
theorem dom_meet_spec (hnm : Function.Injective nm) (hz : nm none = "") {S : Sorts} {sp : Pat}
    {U : List Name} (hC : Ctx nm S sp U) (hN : Sorts.NoPair S)
    (hUS : ∀ n ∈ U, n ∈ Sorts.names S) {rc q : Nat}
    (hr : ∀ d, (Sorts.reachSet S d).card ≤ rc)
    (hq : ∀ d m, (Sorts.reachGSet S (d, some m)).card ≤ q) (ρa ρb : Sorts.Rep S)
    {ra rb : Sorts.Raw} (hfa : Sorts.FoldOf S ρa.1 ra) (hfb : Sorts.FoldOf S ρb.1 rb)
    (Ya Yb : List Sorts.Binds)
    (s : store.Store) (decls names : store.TermId) (a b : sorts.Rep)
    (hI : Inv s) (hde : Repr nm s.nodes.val decls.val sp)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (ha : RepAt nm U s.nodes.val a ra Ya) (hb : RepAt nm U s.nodes.val b rb Yb)
    (hroom : Room s (halvesCost nm U.length ra Ya rb Yb + 2 +
      startCost nm S U.length (meetProb U ra rb Ya Yb) +
      normCharge nm S U rc q (meetProb U ra rb Ya Yb))) :
    dom.meet s decls names a b ⦃ res s' =>
      Inv s' ∧ Extends s s' ∧
        s'.ticks.val ≤ s.ticks.val + halvesCost nm U.length ra Ya rb Yb + 2 +
          startCost nm S U.length (meetProb U ra rb Ya Yb) +
          normCharge nm S U rc q (meetProb U ra rb Ya Yb) ∧
        RepPost nm U s'.nodes.val (ρa.meet ρb) res ⦄ := by
  unfold dom.meet
  unfold meetProb at hroom ⊢
  have hroom' := hroom
  unfold Room at hroom'
  simp only [halvesCost] at hroom'
  obtain ⟨hta, -⟩ := ρa.fold_sides hN hfa
  obtain ⟨htb, -⟩ := ρb.fold_sides hN hfb
  obtain ⟨hla, hra⟩ := sides_fo hfa.1 hta
  obtain ⟨hlb, hrb⟩ := sides_fo hfb.1 htb
  step with half_spec hnm s .Left lren lren_ok a hI ha hta (by unfold Room; omega)
    as ⟨ha', s1, hI1, hx1, ht1, hha⟩
  step with half_spec hnm s1 .Right rren rren_ok b hI1 (hb.extends hx1) htb
    (by unfold Room; omega) as ⟨hb', s2, hI2, hx2, ht2, hhb⟩
  have hx02 := hx1.trans hx2
  have hha2 := hha.extends hx2
  step with alloc_spec s2 .Nil hI2 trivial (by unfold Room; omega)
    as ⟨nil, s3, hI3, ht3, htb3, hx3, hr3⟩
  simp only [norm] at hr3
  step with alloc_spec s3 (.App ha'.r hb'.r) hI3 ⟨(hx3.repr hha2.r).lt, (hx3.repr hhb.r).lt⟩
    (by unfold Room; omega) as ⟨e2, s4, hI4, ht4, htb4, hx4, hr4⟩
  simp only [norm] at hr4
  have hx34 := hx3.trans hx4
  step with alloc_spec s4 (.App e2 nil) hI4
    ⟨(List.getElem?_eq_some_iff.1 hr4).1, (hx4.repr (Repr.nil (nm := nm) hr3)).lt⟩
    (by unfold Room; omega) as ⟨r2, s5, hI5, ht5, htb5, hx5, hr5⟩
  simp only [norm] at hr5
  have hx35 := hx34.trans hx5
  have rr2 : Repr nm s5.nodes.val r2.val
      (encEqs nm [(ra.sides.2.rename lren, rb.sides.2.rename rren)]) :=
    .app hr5 (hx5.repr (.app hr4 (hx34.repr hha2.r) (hx34.repr hhb.r)))
      ((hx4.trans hx5).repr (.nil hr3))
  step with alloc_spec s5 (.App ha'.l hb'.l) hI5 ⟨(hx35.repr hha2.l).lt, (hx35.repr hhb.l).lt⟩
    (by unfold Room; omega) as ⟨e1, s6, hI6, ht6, htb6, hx6, hr6⟩
  simp only [norm] at hr6
  have hx36 := hx35.trans hx6
  step with alloc_spec s6 (.App e1 r2) hI6
    ⟨(List.getElem?_eq_some_iff.1 hr6).1, (hx6.repr rr2).lt⟩
    (by unfold Room; omega) as ⟨e, s7, hI7, ht7, htb7, hx7, hr7⟩
  simp only [norm] at hr7
  have hx37 := hx36.trans hx7
  have re : Repr nm s7.nodes.val e.val
      (encEqs nm [(ra.sides.1.rename lren, rb.sides.1.rename rren),
        (ra.sides.2.rename lren, rb.sides.2.rename rren)]) :=
    .app hr7 (hx7.repr (.app hr6 (hx36.repr hha2.l) (hx36.repr hhb.l)))
      ((hx6.trans hx7).repr rr2)
  step with pair_spec hz s7 ha'.l ha'.r hI7 (hx37.repr hha2.l) (hx37.repr hha2.r)
    (by unfold Room; omega) as ⟨t, s8, hI8, hx8, ht8, rt⟩
  have hx08 := (hx02.trans hx37).trans hx8
  have hfo : (Sorts.tpair (ra.sides.1.rename lren) (ra.sides.2.rename lren)).firstOrder = true := by
    rw [Sorts.tpair_fo, Sorts.rename_fo hla, Sorts.rename_fo hra]; rfl
  have hefo : Eqns.FO [(ra.sides.1.rename lren, rb.sides.1.rename rren),
      (ra.sides.2.rename lren, rb.sides.2.rename rren)] := fun p hp => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact ⟨Sorts.rename_fo hla _, Sorts.rename_fo hlb _⟩
    · exact ⟨Sorts.rename_fo hra _, Sorts.rename_fo hrb _⟩
  refine WP.spec_mono (two_spec hnm hC ρa.wf hUS hr hq hfa.1 hfb.1 ha.y hb.y hfo hefo
    s8 decls names ha' hb' t e hI8 (hx08.repr hde) (hx08.repr hU)
    (hha2.extends (hx37.trans hx8)) (hhb.extends (hx37.trans hx8)) rt (hx8.repr re)
    (by unfold Room; omega)) ?_
  rintro ⟨res, s'⟩ ⟨hI', hx', ht', hpost⟩
  refine ⟨hI', hx08.trans hx', by simp only [halvesCost]; omega, ?_⟩
  rw [Sorts.Rep.meet_eq, ← hfa.rel, ← hfb.rel]
  exact repPost_of ρa.wf (twoProb_fo hfa.1 hfb.1 ha.y hb.y hfo hefo) ⟨_, _, rfl⟩
    (meet_rel hC.names hfa.1 hfb.1 ha.y hb.y hta htb) hpost

/-! ## The right interface, the converse and the interface test -/

/-- `right` computes the right interface of a representative
(`Sorts.Rep.right`), from its folded canonical store. -/
theorem right_spec (hnm : Function.Injective nm) (hz : nm none = "") {S : Sorts} {sp : Pat}
    {U : List Name} (hC : Ctx nm S sp U) (hN : Sorts.NoPair S)
    (hUS : ∀ n ∈ U, n ∈ Sorts.names S) {rc q : Nat}
    (hr : ∀ d, (Sorts.reachSet S d).card ≤ rc)
    (hq : ∀ d m, (Sorts.reachGSet S (d, some m)).card ≤ q) (ρ : Sorts.Rep S)
    {fr : Sorts.Raw} (hf : Sorts.FoldOf S ρ.1 fr) (Y : List Sorts.Binds)
    (s : store.Store) (decls names : store.TermId) (a : sorts.Rep)
    (hI : Inv s) (hde : Repr nm s.nodes.val decls.val sp)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (ha : RepAt nm U s.nodes.val a fr Y)
    (hroom : Room s (2 + repOneCost U.length fr.c.length Y.length +
      startCost nm S U.length (oneProb U fr Y fr.sides.2 fr.sides.2) +
      normCharge nm S U rc q (oneProb U fr Y fr.sides.2 fr.sides.2))) :
    dom.right s decls names a ⦃ res s' =>
      Inv s' ∧ Extends s s' ∧
        s'.ticks.val ≤ s.ticks.val + 2 + repOneCost U.length fr.c.length Y.length +
          startCost nm S U.length (oneProb U fr Y fr.sides.2 fr.sides.2) +
          normCharge nm S U rc q (oneProb U fr Y fr.sides.2 fr.sides.2) ∧
        RepPost nm U s'.nodes.val ρ.right res ⦄ := by
  unfold dom.right
  have hroom' := hroom
  unfold Room at hroom'
  obtain ⟨hta, -⟩ := ρ.fold_sides hN hf
  obtain ⟨-, hrfo⟩ := sides_fo hf.1 hta
  have rt : Repr nm s.nodes.val a.t.val (Sorts.tpair fr.sides.1 fr.sides.2) := by
    rw [← hta]; exact ha.t
  step with sides_spec s a.t hI rt (by unfold Room; omega) as ⟨l, r, s1, hK, rl, rr⟩
  have ht1 := hK.ticks
  have hx1 : Extends s s1 := Extends.of_eq hK.nodes (by omega)
  refine WP.spec_mono (one_spec hnm hz hC ρ.wf hUS hr hq hf.1 Y hrfo hrfo s1 decls names a r r
    hK.inv (hx1.repr hde) (hx1.repr hU) (ha.extends hx1) (hx1.repr rr) (hx1.repr rr)
    (by unfold Room; omega)) ?_
  rintro ⟨res, s'⟩ ⟨hI', hx', ht', hpost⟩
  refine ⟨hI', hx1.trans hx', by omega, ?_⟩
  rw [Sorts.Rep.right_eq, ← hf.rel, ← right_rel hta]
  exact hpost

/-- `conv` computes the converse of a representative (`Sorts.Rep.conv`),
from its folded canonical store. -/
theorem conv_spec (hnm : Function.Injective nm) (hz : nm none = "") {S : Sorts} {sp : Pat}
    {U : List Name} (hC : Ctx nm S sp U) (hN : Sorts.NoPair S)
    (hUS : ∀ n ∈ U, n ∈ Sorts.names S) {rc q : Nat}
    (hr : ∀ d, (Sorts.reachSet S d).card ≤ rc)
    (hq : ∀ d m, (Sorts.reachGSet S (d, some m)).card ≤ q) (ρ : Sorts.Rep S)
    {fr : Sorts.Raw} (hf : Sorts.FoldOf S ρ.1 fr) (Y : List Sorts.Binds)
    (s : store.Store) (decls names : store.TermId) (a : sorts.Rep)
    (hI : Inv s) (hde : Repr nm s.nodes.val decls.val sp)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (ha : RepAt nm U s.nodes.val a fr Y)
    (hroom : Room s (2 + repOneCost U.length fr.c.length Y.length +
      startCost nm S U.length (oneProb U fr Y fr.sides.2 fr.sides.1) +
      normCharge nm S U rc q (oneProb U fr Y fr.sides.2 fr.sides.1))) :
    dom.conv s decls names a ⦃ res s' =>
      Inv s' ∧ Extends s s' ∧
        s'.ticks.val ≤ s.ticks.val + 2 + repOneCost U.length fr.c.length Y.length +
          startCost nm S U.length (oneProb U fr Y fr.sides.2 fr.sides.1) +
          normCharge nm S U rc q (oneProb U fr Y fr.sides.2 fr.sides.1) ∧
        ∃ r' Y', Sorts.FoldOf S ρ.conv.1 r' ∧ RepAt nm U s'.nodes.val res r' Y' ⦄ := by
  unfold dom.conv
  have hroom' := hroom
  unfold Room at hroom'
  obtain ⟨hta, -⟩ := ρ.fold_sides hN hf
  obtain ⟨hlfo, hrfo⟩ := sides_fo hf.1 hta
  have rt : Repr nm s.nodes.val a.t.val (Sorts.tpair fr.sides.1 fr.sides.2) := by
    rw [← hta]; exact ha.t
  step with sides_spec s a.t hI rt (by unfold Room; omega) as ⟨l, r, s1, hK, rl, rr⟩
  have ht1 := hK.ticks
  have hx1 : Extends s s1 := Extends.of_eq hK.nodes (by omega)
  step with one_spec hnm hz hC ρ.wf hUS hr hq hf.1 Y hrfo hlfo s1 decls names a r l
    hK.inv (hx1.repr hde) (hx1.repr hU) (ha.extends hx1) (hx1.repr rr) (hx1.repr rl)
    (by unfold Room; omega) as ⟨o, s2, hI2, hx2, ht2, hpost⟩
  rw [swap_rel hta, hf.rel] at hpost
  cases o with
  | none =>
    simp only [RepPost] at hpost
    simp only [WP.spec_ok]
    refine ⟨hI2, hx1.trans hx2, by omega, fr, Y, ?_, ha.extends (hx1.trans hx2)⟩
    rw [Sorts.Rep.conv_eq, hpost]
    exact hf
  | some b =>
    simp only [RepPost] at hpost
    obtain ⟨ρ', r', Y', hρ', hf', hb⟩ := hpost
    simp only [WP.spec_ok]
    refine ⟨hI2, hx1.trans hx2, by omega, r', Y', ?_, hb⟩
    rw [Sorts.Rep.conv_eq, hρ']
    exact hf'

/-- `is_bound` decides whether the two sides of a representative are the
same pattern, on its folded canonical store, in three ticks. -/
theorem is_bound_spec (hnm : Function.Injective nm) {S : Sorts} {U : List Name}
    (hN : Sorts.NoPair S) (ρ : Sorts.Rep S) {fr : Sorts.Raw} (hf : Sorts.FoldOf S ρ.1 fr)
    (Y : List Sorts.Binds) (s : store.Store) (a : sorts.Rep) (hI : Inv s)
    (ha : RepAt nm U s.nodes.val a fr Y) (hroom : Room s 3) :
    dom.is_bound s a ⦃ res s' => Kept s s' 3 ∧ res = decide (ρ.l = ρ.r) ⦄ := by
  unfold dom.is_bound
  have hroom' := hroom
  unfold Room at hroom'
  obtain ⟨hta, hiff⟩ := ρ.fold_sides hN hf
  have rt : Repr nm s.nodes.val a.t.val (Sorts.tpair fr.sides.1 fr.sides.2) := by
    rw [← hta]; exact ha.t
  step with sides_spec s a.t hI rt (by unfold Room; omega) as ⟨l, r, s1, hK, rl, rr⟩
  have ht1 := hK.ticks
  refine WP.spec_mono (same_spec s1 l r hK.inv (by unfold Room; omega)) ?_
  rintro ⟨res, s'⟩ ⟨hres, hK'⟩
  refine ⟨⟨by rw [hK'.nodes, hK.nodes], by rw [hK'.tbl, hK.tbl], by rw [hK'.ticks, hK.ticks],
    hK'.inv⟩, ?_⟩
  rw [hres]
  congr 1
  refine propext ⟨fun h => hiff.1 ?_, fun h => ?_⟩
  · have := rl; rw [h] at this; exact this.unique rr
  · have := rl; rw [hiff.2 h] at this; exact Repr.inj hnm hI.nodesOK this rr

/-! ## The covering test -/

/-- A solved exclusion is determined by the values it gives the variables. -/
theorem vals_inj {k : Nat} {θ θ' : Sorts.Binds} (hθ : Sorts.Pre k θ) (hθ' : Sorts.Pre k θ')
    (h : vals k θ = vals k θ') : θ = θ' := by
  have happ : ∀ i, i < k → PSubst.apply θ i = PSubst.apply θ' i := by
    intro i _
    have := congrArg (fun L : List Pat => L.getD i (.var i)) h
    simpa only [getD_vals hθ.dom, getD_vals hθ'.dom] using this
  have sub : ∀ {α β : Sorts.Binds}, Sorts.Pre k α → Sorts.Pre k β →
      (∀ i, i < k → PSubst.apply α i = PSubst.apply β i) → ∀ b ∈ α, b ∈ β := by
    intro α β hα hβ hab b hb
    have e := hab b.1 (hα.dom b hb)
    rw [Sorts.apply_of_mem hα.sorted hb] at e
    rcases Sorts.apply_cases β b.1 with hv | hm
    · exfalso
      rw [hv] at e
      exact (hα.ran b hb b.1 (by rw [e]; simp [Term.vars])).2 b hb rfl
    · rw [← e] at hm; exact hm
  have nodup : ∀ {α : Sorts.Binds}, Sorts.Pre k α → α.Nodup := fun hα =>
    hα.sorted.imp fun h e => by rw [e] at h; exact lt_irrefl _ h
  exact List.Perm.eq_of_pairwise (le := fun a b : Nat × Pat => a.1 < b.1)
    (fun a b _ _ h1 h2 => absurd h1 (Nat.lt_asymm h2)) hθ.sorted hθ'.sorted
    ((List.perm_ext_iff_of_nodup (nodup hθ) (nodup hθ')).2 fun b =>
      ⟨sub hθ hθ' happ b, sub hθ' hθ (fun i hi => (happ i hi).symm) b⟩)

theorem map_cpat_inj {z : Sym} {U : List Name} : ∀ {l l' : List Sorts.Conj},
    (∀ c ∈ l, Sub U c) → (∀ c ∈ l', Sub U c) → l.map (cpat z U) = l'.map (cpat z U) → l = l'
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | c :: l, d :: l', hl, hl', h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [cpat_inj (hl c (by simp)) (hl' d (by simp)) h.1,
      map_cpat_inj (fun c hc => hl c (by simp [hc])) (fun c hc => hl' c (by simp [hc])) h.2]

theorem raw_eq_iff {ra rb : Sorts.Raw} :
    ra = rb ↔ ra.t = rb.t ∧ ra.c = rb.c ∧ ra.x = rb.x := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨t, c, x⟩ := ra
    obtain ⟨t', c', x'⟩ := rb
    simp only at h1 h2 h3
    subst h1 h2 h3
    rfl

theorem raw_sub {S : Sorts} {sp : Pat} {U : List Name} (hC : Ctx nm S sp U) {r : Sorts.Raw}
    (hr : r.Shaped S) : ∀ c ∈ r.c, Sub U c := by
  intro c hc n hn
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hc
  refine hC.names n ((hr.up i hi n).1 ?_).1
  simpa [Sorts.Raw.conj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] using hn

/-- The first loop of `subset` flags the members of a list. -/
theorem subset_loop0_spec :
    ∀ (Bs : List Pat) (s : store.Store) (b : store.TermId),
    Inv s → Repr nm s.nodes.val b.val (encList (nm none) Bs) → Room s (2 * Bs.length + 1) →
    dom.subset_loop0 b s ⦃ s' =>
      Inv s' ∧ s'.nodes.val = s.nodes.val ∧ s'.ticks.val ≤ s.ticks.val + 2 * Bs.length + 1 ∧
        s.ticks.val ≤ s'.ticks.val ∧ tbl s' .A = tbl s .A ∧
        (∀ k, tbl s .B k ≠ none → tbl s' .B k ≠ none) ∧
        (∀ p ∈ Bs, ∃ k, Repr nm s.nodes.val k p ∧ tbl s' .B k ≠ none) ∧
        ∀ k, tbl s' .B k ≠ none → tbl s .B k ≠ none ∨ ∃ p ∈ Bs, Repr nm s.nodes.val k p ⦄ := by
  intro Bs
  induction Bs with
  | nil =>
    intro s b hI hb hroom
    have hroom' := hroom
    unfold Room at hroom'
    unfold dom.subset_loop0
    rw [loop]
    simp only [dom.subset_loop0.body]
    step with uncons_repr s b hI.toWf (p := Term.sym (nm none)) hb (by unfold Room; omega)
      as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    subst hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    have hfin : Inv s1 ∧ s1.nodes.val = s.nodes.val ∧
        s1.ticks.val ≤ s.ticks.val + 2 * ([] : List Pat).length + 1 ∧
        s.ticks.val ≤ s1.ticks.val ∧ tbl s1 .A = tbl s .A ∧
        (∀ k, tbl s .B k ≠ none → tbl s1 .B k ≠ none) ∧
        (∀ p ∈ ([] : List Pat), ∃ k, Repr nm s.nodes.val k p ∧ tbl s1 .B k ≠ none) ∧
        ∀ k, tbl s1 .B k ≠ none →
          tbl s .B k ≠ none ∨ ∃ p ∈ ([] : List Pat), Repr nm s.nodes.val k p :=
      ⟨K1.inv, K1.nodes, by simp only [List.length_nil]; omega, by omega, by rw [K1.tbl],
        fun k h => by rw [K1.tbl]; exact h, by simp,
        fun k h => .inl (by rw [K1.tbl] at h; exact h)⟩
    step*
  | cons p Bs ih =>
    intro s b hI hb hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons] at hroom'
    unfold dom.subset_loop0
    rw [loop]
    simp only [dom.subset_loop0.body]
    step with uncons_repr s b hI.toWf (p := Term.app p (encList (nm none) Bs)) hb
      (by unfold Room; omega) as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    obtain ⟨hi, rest, rfl, rp, rrest⟩ := hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    step with set_flag_spec s1 .B hi true K1.inv (by rw [K1.nodes]; exact rp.lt)
      (by unfold Room; omega) as ⟨s2, f1, f2, f3, f4, f5⟩
    have hn2 : s2.nodes.val = s.nodes.val := by rw [f1, K1.nodes]
    simp only [uncurry]
    have IH := ih s2 rest f3 (by rw [hn2]; exact rrest) (by unfold Room; omega)
    unfold dom.subset_loop0 at IH
    refine WP.spec_mono IH ?_
    rintro s' ⟨hI', hn', ht', hm', hA', hmono', hall', hback'⟩
    have hB2 : ∀ k, tbl s2 .B k = if k = hi.val then some 1 else tbl s .B k := by
      intro k
      rw [f4, K1.tbl, Function.update_apply]
      rfl
    refine ⟨hI', by rw [hn', hn2], by simp only [List.length_cons]; omega, by omega,
      by rw [hA', f5 .A (by simp), K1.tbl], ?_, ?_, ?_⟩
    · intro k hk
      apply hmono'
      rw [hB2]
      split
      · simp
      · exact hk
    · intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact ⟨hi.val, rp, hmono' _ (by rw [hB2]; simp)⟩
      · obtain ⟨k, hk, hf⟩ := hall' q hq
        exact ⟨k, by rw [hn2] at hk; exact hk, hf⟩
    · intro k hk
      rcases hback' k hk with h | ⟨q, hq, hr⟩
      · rw [hB2] at h
        by_cases e : k = hi.val
        · exact .inr ⟨p, by simp, e ▸ rp⟩
        · simp only [e, ↓reduceIte] at h; exact .inl h
      · exact .inr ⟨q, by simp [hq], by rw [hn2] at hr; exact hr⟩

/-- The second loop of `subset` says whether every member of a list is
flagged. -/
theorem subset_loop1_spec (hnm : Function.Injective nm) :
    ∀ (As : List Pat) (s : store.Store) (a : store.TermId),
    Inv s → Repr nm s.nodes.val a.val (encList (nm none) As) → Room s (2 * As.length + 1) →
    dom.subset_loop1 s true a true ⦃ res s' =>
      Inv s' ∧ s'.nodes.val = s.nodes.val ∧ tbl s' = tbl s ∧
        s'.ticks.val ≤ s.ticks.val + 2 * As.length + 1 ∧ s.ticks.val ≤ s'.ticks.val ∧
        (res = true ↔ ∀ p ∈ As, ∃ k, Repr nm s.nodes.val k p ∧ tbl s .B k ≠ none) ⦄ := by
  intro As
  induction As with
  | nil =>
    intro s a hI ha hroom
    have hroom' := hroom
    unfold Room at hroom'
    unfold dom.subset_loop1
    rw [loop]
    simp only [dom.subset_loop1.body, ↓reduceIte]
    step with uncons_repr s a hI.toWf (p := Term.sym (nm none)) ha (by unfold Room; omega)
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
    exact ⟨K1.inv, K1.nodes, K1.tbl, by simp only [List.length_nil]; omega, by omega, by simp⟩
  | cons p As ih =>
    intro s a hI ha hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons] at hroom'
    unfold dom.subset_loop1
    rw [loop]
    simp only [dom.subset_loop1.body, ↓reduceIte]
    step with uncons_repr s a hI.toWf (p := Term.app p (encList (nm none) As)) ha
      (by unfold Room; omega) as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    obtain ⟨hi, rest, rfl, rp, rrest⟩ := hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    step with get_flag_spec s1 .B hi K1.inv (by rw [K1.nodes]; exact rp.lt)
      (by unfold Room; omega) as ⟨r1, hres, K2⟩
    obtain ⟨o1, s2⟩ := r1
    simp only at hres K2
    have ht2 := K2.ticks
    have hn2 : s2.nodes.val = s.nodes.val := by rw [K2.nodes, K1.nodes]
    have htb2 : tbl s2 = tbl s := by rw [K2.tbl, K1.tbl]
    cases hfl : tbl s .B hi.val with
    | none =>
      have : o1 = none := by rw [hres, K1.tbl, hfl]; rfl
      subst this
      simp only [uncurry, bind_ok]
      rw [loop]
      simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, WP.spec_ok]
      refine ⟨K2.inv, hn2, htb2, by simp only [List.length_cons]; omega, by omega, ?_⟩
      constructor
      · intro h; cases h
      · intro h
        exfalso
        obtain ⟨k, hk, hf⟩ := h p (by simp)
        rw [Repr.inj hnm hI.nodesOK hk rp] at hf
        exact hf hfl
    | some v =>
      have : o1 = some (decide (v ≠ 0)) := by rw [hres, K1.tbl, hfl]; rfl
      subst this
      simp only [uncurry, bind_ok]
      have IH := ih s2 rest K2.inv (by rw [hn2]; exact rrest) (by unfold Room; omega)
      unfold dom.subset_loop1 at IH
      refine WP.spec_mono IH ?_
      rintro ⟨res, s'⟩ ⟨hI', hn', htb', ht', hm', hiff⟩
      simp only [hn2, htb2] at hiff
      refine ⟨hI', by rw [hn', hn2], by rw [htb', htb2], by simp only [List.length_cons]; omega,
        by omega, ?_⟩
      rw [hiff]
      constructor
      · intro h q hq
        rcases List.mem_cons.1 hq with rfl | hq
        · exact ⟨hi.val, rp, by rw [hfl]; simp⟩
        · exact h q hq
      · intro h q hq
        exact h q (List.mem_cons_of_mem _ hq)

/-- `subset` decides whether every member of a list is a member of
another. -/
theorem subset_spec (hnm : Function.Injective nm) (As Bs : List Pat) (s : store.Store)
    (a b : store.TermId) (hI : Inv s) (ha : Repr nm s.nodes.val a.val (encList (nm none) As))
    (hb : Repr nm s.nodes.val b.val (encList (nm none) Bs))
    (hroom : Room s (2 * As.length + 2 * Bs.length + 3)) :
    dom.subset s a b ⦃ res s' =>
      Inv s' ∧ s'.nodes.val = s.nodes.val ∧ tbl s' .A = tbl s .A ∧
        s'.ticks.val ≤ s.ticks.val + 2 * As.length + 2 * Bs.length + 3 ∧
        s.ticks.val ≤ s'.ticks.val ∧ res = decide (∀ p ∈ As, p ∈ Bs) ⦄ := by
  unfold dom.subset
  have hroom' := hroom
  unfold Room at hroom'
  step with clear_spec s .B hI (by unfold Room; omega) as ⟨s1, c1, c2, c3, c4, c5⟩
  step with subset_loop0_spec (nm := nm) Bs s1 b c3 (by rw [c1]; exact hb)
    (by unfold Room; omega) as ⟨s2, hI2, hn2, ht2, hm2, hA2, hmono2, hall2, hback2⟩
  refine WP.spec_mono (subset_loop1_spec hnm As s2 a hI2 (by rw [hn2, c1]; exact ha)
    (by unfold Room; omega)) ?_
  rintro ⟨res, s'⟩ ⟨hI', hn', htb', ht', hm', hiff⟩
  simp only [hn2] at hiff
  refine ⟨hI', by rw [hn', hn2, c1], by rw [htb', hA2, c5 .A (by simp)], by omega, by omega, ?_⟩
  have key : res = true ↔ ∀ p ∈ As, p ∈ Bs := by
    rw [hiff]
    constructor
    · intro h p hp
      obtain ⟨k, hk, hf⟩ := h p hp
      rcases hback2 k hf with h0 | ⟨q, hq, hr⟩
      · exact absurd (c4 k) h0
      · rw [hk.unique hr]; exact hq
    · intro h p hp
      exact hall2 p (h p hp)
  by_cases hall : ∀ p ∈ As, p ∈ Bs
  · rw [decide_eq_true hall]; exact key.2 hall
  · rw [decide_eq_false hall]
    cases res with
    | false => rfl
    | true => exact absurd (key.1 rfl) hall

theorem map_sub_iff {α β : Type} {f : α → β} (hf : Function.Injective f) (l l' : List α) :
    (∀ p ∈ l.map f, p ∈ l'.map f) ↔ ∀ p ∈ l, p ∈ l' := by
  constructor
  · intro h p hp
    obtain ⟨q, hq, e⟩ := List.mem_map.1 (h _ (List.mem_map_of_mem hp))
    exact hf e ▸ hq
  · intro h p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    exact List.mem_map_of_mem (h q hq)

/-- `same_rep` decides whether two representatives are the same. -/
theorem same_rep_spec (hnm : Function.Injective nm) {S : Sorts} {sp : Pat} {U : List Name}
    (hC : Ctx nm S sp U) (ρa ρb : Sorts.Rep S) {ra rb : Sorts.Raw}
    (hfa : Sorts.FoldOf S ρa.1 ra) (hfb : Sorts.FoldOf S ρb.1 rb) (Ya Yb : List Sorts.Binds)
    (s : store.Store) (a b : sorts.Rep) (hI : Inv s) (ha : RepAt nm U s.nodes.val a ra Ya)
    (hb : RepAt nm U s.nodes.val b rb Yb)
    (hroom : Room s (4 * Ya.length + 4 * Yb.length + 8)) :
    dom.same_rep s a b ⦃ res s' =>
      Inv s' ∧ s'.nodes.val = s.nodes.val ∧
        s'.ticks.val ≤ s.ticks.val + 4 * Ya.length + 4 * Yb.length + 8 ∧
        s.ticks.val ≤ s'.ticks.val ∧ res = decide (ρa = ρb) ⦄ := by
  have hρ : ρa = ρb ↔ ra = rb :=
    ⟨fun h => by subst h; exact Sorts.FoldOf.eq ρa.wf hfa hfb,
      fun h => by subst h; exact Sorts.Rep.eq_of_fold hfa hfb⟩
  have hT : a.t.val = b.t.val ↔ ra.t = rb.t := by
    constructor
    · intro h; have := ha.t; rw [h] at this; exact this.unique hb.t
    · intro h; have := ha.t; rw [h] at this; exact Repr.inj hnm hI.nodesOK this hb.t
  have hCc : a.c.val = b.c.val ↔ ra.c = rb.c := by
    constructor
    · intro h
      have := ha.c
      rw [h] at this
      exact map_cpat_inj (raw_sub hC hfa.1) (raw_sub hC hfb.1) (encList_inj _ (this.unique hb.c))
    · intro h; have := ha.c; rw [h] at this; exact Repr.inj hnm hI.nodesOK this hb.c
  have hpa : ∀ θ ∈ Ya, Sorts.Pre ra.c.length θ := fun θ hθ =>
    (hfa.1.ex θ (by rw [← ha.y]; exact List.mem_toFinset.2 hθ)).toPre
  have hpb : ∀ θ ∈ Yb, Sorts.Pre rb.c.length θ := fun θ hθ =>
    (hfb.1.ex θ (by rw [← hb.y]; exact List.mem_toFinset.2 hθ)).toPre
  have hX : ra.c = rb.c →
      (((∀ p ∈ Ya.map (vals ra.c.length), p ∈ Yb.map (vals rb.c.length)) ∧
        ∀ p ∈ Yb.map (vals rb.c.length), p ∈ Ya.map (vals ra.c.length)) ↔
        ra.x = rb.x) := by
    intro hc
    have hk : ra.c.length = rb.c.length := congrArg List.length hc
    constructor
    · rintro ⟨h1, h2⟩
      rw [← ha.y, ← hb.y]
      ext θ
      simp only [List.mem_toFinset]
      constructor
      · intro hθ
        obtain ⟨θ', hθ', e⟩ := List.mem_map.1 (h1 _ (List.mem_map_of_mem hθ))
        rw [← hk] at e
        have := vals_inj (by rw [hk]; exact hpb θ' hθ') (hpa θ hθ) e
        rw [← this]; exact hθ'
      · intro hθ
        obtain ⟨θ', hθ', e⟩ := List.mem_map.1 (h2 _ (List.mem_map_of_mem hθ))
        rw [hk] at e
        have := vals_inj (by rw [← hk]; exact hpa θ' hθ') (hpb θ hθ) e
        rw [← this]; exact hθ'
    · intro hx
      have hmem : ∀ θ, θ ∈ Ya ↔ θ ∈ Yb := fun θ => by
        rw [← List.mem_toFinset, ha.y, hx, ← hb.y, List.mem_toFinset]
      constructor
      · intro p hp
        obtain ⟨θ, hθ, rfl⟩ := List.mem_map.1 hp
        rw [hk]; exact List.mem_map_of_mem ((hmem θ).1 hθ)
      · intro p hp
        obtain ⟨θ, hθ, rfl⟩ := List.mem_map.1 hp
        rw [← hk]; exact List.mem_map_of_mem ((hmem θ).2 hθ)
  have hE : Function.Injective (encList (V := Nat) (nm none)) := fun _ _ h => encList_inj _ h
  unfold dom.same_rep
  have hroom' := hroom
  unfold Room at hroom'
  step with same_spec s a.t b.t hI (by unfold Room; omega) as ⟨b1, s1, hb1, hK1⟩
  have ht1 := hK1.ticks
  by_cases e1 : a.t.val = b.t.val
  · have : b1 = true := by simp [hb1, e1]
    subst this
    simp only [↓reduceIte]
    step with same_spec s1 a.c b.c hK1.inv (by unfold Room; omega) as ⟨b2, s2, hb2, hK2⟩
    have ht2 := hK2.ticks
    have hn2 : s2.nodes.val = s.nodes.val := by rw [hK2.nodes, hK1.nodes]
    by_cases e2 : a.c.val = b.c.val
    · have : b2 = true := by simp [hb2, e2]
      subst this
      simp only [↓reduceIte]
      step with subset_spec hnm ((Ya.map (vals ra.c.length)).map (encList (nm none)))
        ((Yb.map (vals rb.c.length)).map (encList (nm none))) s2
        a.x b.x hK2.inv (by rw [hn2]; exact ha.x) (by rw [hn2]; exact hb.x)
        (by simp only [List.length_map]; unfold Room; omega)
        as ⟨b3, s3, hI3, hn3, hA3, ht3, hm3, hb3⟩
      simp only [List.length_map] at ht3
      replace hb3 : b3 = true ↔
          ∀ p ∈ Ya.map (vals ra.c.length), p ∈ Yb.map (vals rb.c.length) := by
        rw [hb3, decide_eq_true_iff, map_sub_iff hE]
      by_cases e3 : ∀ p ∈ Ya.map (vals ra.c.length), p ∈ Yb.map (vals rb.c.length)
      · have : b3 = true := hb3.2 e3
        subst this
        simp only [↓reduceIte]
        refine WP.spec_mono (subset_spec hnm
          ((Yb.map (vals rb.c.length)).map (encList (nm none)))
          ((Ya.map (vals ra.c.length)).map (encList (nm none))) s3 b.x a.x hI3 (by rw [hn3, hn2]; exact hb.x)
          (by rw [hn3, hn2]; exact ha.x)
          (by simp only [List.length_map]; unfold Room; omega)) ?_
        rintro ⟨res, s'⟩ ⟨hI', hn', hA', ht', hm', hres⟩
        simp only [List.length_map] at ht'
        replace hres : res = true ↔
            ∀ p ∈ Yb.map (vals rb.c.length), p ∈ Ya.map (vals ra.c.length) := by
          rw [hres, decide_eq_true_iff, map_sub_iff hE]
        refine ⟨hI', by rw [hn', hn3, hn2], by omega, by omega, ?_⟩
        refine Bool.eq_iff_iff.2 ?_
        rw [hres, decide_eq_true_iff]
        exact ⟨fun h => hρ.2 (raw_eq_iff.2 ⟨hT.1 e1, hCc.1 e2, (hX (hCc.1 e2)).1 ⟨e3, h⟩⟩),
          fun h => ((hX (hCc.1 e2)).2 (raw_eq_iff.1 (hρ.1 h)).2.2).2⟩
      · have : b3 = false := Bool.eq_false_iff.2 fun h => e3 (hb3.1 h)
        subst this
        simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        refine ⟨hI3, by rw [hn3, hn2], by omega, by omega, ?_⟩
        exact (decide_eq_false fun h => e3 ((hX (hCc.1 e2)).2 (raw_eq_iff.1 (hρ.1 h)).2.2).1).symm
    · have : b2 = false := by simp [hb2, e2]
      subst this
      simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      refine ⟨hK2.inv, hn2, by omega, by omega, ?_⟩
      exact (decide_eq_false fun h => e2 (hCc.2 (raw_eq_iff.1 (hρ.1 h)).2.1)).symm
  · have : b1 = false := by simp [hb1, e1]
    subst this
    simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    refine ⟨hK1.inv, hK1.nodes, by omega, by omega, ?_⟩
    exact (decide_eq_false fun h => e1 (hT.2 (raw_eq_iff.1 (hρ.1 h)).1)).symm

open Classical in
/-- The number of exclusions of the folded canonical store of a
representative. -/
noncomputable def foldCard {S : Sorts} (ρ : Sorts.Rep S) : Nat :=
  if h : ∃ r, Sorts.FoldOf S ρ.1 r then (Classical.choose h).x.card else 0

theorem foldCard_eq {S : Sorts} {ρ : Sorts.Rep S} {r : Sorts.Raw} (h : Sorts.FoldOf S ρ.1 r) :
    foldCard ρ = r.x.card := by
  have hex : ∃ r, Sorts.FoldOf S ρ.1 r := ⟨r, h⟩
  unfold foldCard
  rw [dite_eq_left_of_eq_true (eq_true hex),
    Sorts.FoldOf.eq ρ.wf (Classical.choose_spec (of_eq_true (eq_true hex))) h]

/-- The number of exclusions of the conjunction of two representatives, in
its folded canonical store. -/
noncomputable def meetXs {S : Sorts} (ρa ρb : Sorts.Rep S) : Nat :=
  ((ρa.meet ρb).map foldCard).getD 0

/-- `covers` decides whether the conjunction of two representatives is the
second (`covers` of `Sorts.dom`): whether the first relates every pair the
second relates. -/
theorem dom_covers_spec (hnm : Function.Injective nm) (hz : nm none = "") {S : Sorts} {sp : Pat}
    {U : List Name} (hC : Ctx nm S sp U) (hN : Sorts.NoPair S)
    (hUS : ∀ n ∈ U, n ∈ Sorts.names S) {rc q : Nat}
    (hr : ∀ d, (Sorts.reachSet S d).card ≤ rc)
    (hq : ∀ d m, (Sorts.reachGSet S (d, some m)).card ≤ q) (ρa ρb : Sorts.Rep S)
    {ra rb : Sorts.Raw} (hfa : Sorts.FoldOf S ρa.1 ra) (hfb : Sorts.FoldOf S ρb.1 rb)
    (Ya Yb : List Sorts.Binds)
    (s : store.Store) (decls names : store.TermId) (a b : sorts.Rep)
    (hI : Inv s) (hde : Repr nm s.nodes.val decls.val sp)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (ha : RepAt nm U s.nodes.val a ra Ya) (hb : RepAt nm U s.nodes.val b rb Yb)
    (hroom : Room s (halvesCost nm U.length ra Ya rb Yb + 2 +
      startCost nm S U.length (meetProb U ra rb Ya Yb) +
      normCharge nm S U rc q (meetProb U ra rb Ya Yb) +
      (4 * meetXs ρa ρb + 4 * Yb.length + 8))) :
    dom.covers s decls names a b ⦃ res s' =>
      Inv s' ∧ Extends s s' ∧
        s'.ticks.val ≤ s.ticks.val + halvesCost nm U.length ra Ya rb Yb + 2 +
          startCost nm S U.length (meetProb U ra rb Ya Yb) +
          normCharge nm S U rc q (meetProb U ra rb Ya Yb) +
          (4 * meetXs ρa ρb + 4 * Yb.length + 8) ∧
        res = decide (ρa.meet ρb = some ρb) ⦄ := by
  unfold dom.covers
  have hroom' := hroom
  unfold Room at hroom'
  step with dom_meet_spec hnm hz hC hN hUS hr hq ρa ρb hfa hfb Ya Yb s decls names a b hI hde hU
    ha hb (by unfold Room; omega) as ⟨o, s1, hI1, hx1, ht1, hpost⟩
  cases o with
  | none =>
    simp only [RepPost] at hpost
    simp only [WP.spec_ok]
    refine ⟨hI1, hx1, by omega, ?_⟩
    rw [hpost]
    simp
  | some m =>
    simp only [RepPost] at hpost
    obtain ⟨ρ', r', Y', hρ', hf', hm⟩ := hpost
    have hlen : Y'.length = meetXs ρa ρb := by
      unfold meetXs
      rw [hρ', Option.map_some, Option.getD_some, foldCard_eq hf', ← hm.y,
        List.toFinset_card_of_nodup hm.nd]
    simp only
    refine WP.spec_mono (same_rep_spec hnm hC ρ' ρb hf' hfb Y' Yb s1 m b hI1 hm
      (hb.extends hx1) (by rw [hlen]; unfold Room; omega)) ?_
    rintro ⟨res, s'⟩ ⟨hI', hn', ht', hm', hres⟩
    rw [hlen] at ht'
    refine ⟨hI', hx1.trans (Extends.of_eq hn' hm'), by omega, ?_⟩
    rw [hres, hρ']
    simp

end RwLogVerified
