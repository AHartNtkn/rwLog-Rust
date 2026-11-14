/-
# The folded store

`foldRaw S r` is the store `r` with each outermost free subterm of its
pattern replaced by a variable that carries the sorts of the subterm
(`clo`), its variables renumbered and its exclusions renamed. It is computed
on `r` (`freeB` decides which subterms are free). For a store determined by
its pattern and what it denotes whose variables have infinitely many values
(`Raw.Roomy`), the result is again determined by its pattern and what it
denotes, denotes the same, and its pattern is the folded pattern of `r`
(`foldRaw_spec`).

With `Unfold.lean` this gives the canonical folded store of a problem
(`FoldOf`, `foldRaw_ofTight`): fold the store assembled when the variables
that exclusions mention have been written out.
-/
import RwLog.Sorts.Fits
import RwLog.Sorts.Unfold

namespace RwLog
namespace Sorts

open Function

variable {S : Sorts}

/-! ## The names of a folded term -/

section leaves

variable {s : Store}

/-- A name of a folded term is a variable of the term or a free subterm. -/
theorem foldF_leaf : ∀ (t : Pat), ∀ p ∈ (foldF S s t).vars,
    (∃ x ∈ t.vars, p = .var x) ∨ Free S s p
  | .var x, p, hp => by
    simp only [foldF, Term.vars, List.mem_singleton] at hp
    exact Or.inl ⟨x, by simp [Term.vars], hp⟩
  | .sym _, p, hp => by simp [foldF, Term.vars] at hp
  | .app g b, p, hp => by
    simp only [foldF, Term.vars, List.mem_append] at hp
    rcases hp with hp | hp
    · rcases foldF_leaf g p hp with ⟨x, hx, e⟩ | h
      · exact Or.inl ⟨x, by simp [Term.vars, hx], e⟩
      · exact Or.inr h
    · by_cases hb : Free S s b
      · simp only [ite_eq_left hb, Term.vars, List.mem_singleton] at hp
        exact Or.inr (hp ▸ hb)
      · rw [ite_eq_right hb] at hp
        rcases foldF_leaf b p hp with ⟨x, hx, e⟩ | h
        · exact Or.inl ⟨x, by simp [Term.vars, hx], e⟩
        · exact Or.inr h

theorem foldV_leaf (t : Pat) : ∀ p ∈ (foldV S s t).vars,
    (∃ x ∈ t.vars, p = .var x) ∨ Free S s p := by
  intro p hp
  unfold foldV at hp
  by_cases ht : Free S s t
  · simp only [ite_eq_left ht, Term.vars, List.mem_singleton] at hp
    exact Or.inr (hp ▸ ht)
  · rw [ite_eq_right ht] at hp
    exact foldF_leaf t p hp

/-- A name of a folded first-order term is first-order. -/
theorem foldF_leaf_fo : ∀ (t : Pat), t.firstOrder = true → ∀ p ∈ (foldF S s t).vars,
    p.firstOrder = true
  | .var x, _, p, hp => by
    simp only [foldF, Term.vars, List.mem_singleton] at hp
    subst hp
    rfl
  | .sym _, _, p, hp => by simp [foldF, Term.vars] at hp
  | .app g b, hfo, p, hp => by
    obtain ⟨hg, hb', -⟩ := Term.fo_app hfo
    simp only [foldF, Term.vars, List.mem_append] at hp
    rcases hp with hp | hp
    · exact foldF_leaf_fo g hg p hp
    · by_cases hb : Free S s b
      · simp only [ite_eq_left hb, Term.vars, List.mem_singleton] at hp
        exact hp ▸ hb'
      · rw [ite_eq_right hb] at hp
        exact foldF_leaf_fo b hb' p hp

theorem foldV_leaf_fo {t : Pat} (hfo : t.firstOrder = true) : ∀ p ∈ (foldV S s t).vars,
    p.firstOrder = true := by
  intro p hp
  unfold foldV at hp
  by_cases ht : Free S s t
  · simp only [ite_eq_left ht, Term.vars, List.mem_singleton] at hp
    exact hp ▸ hfo
  · rw [ite_eq_right ht] at hp
    exact foldF_leaf_fo t hfo p hp

/-- A folded term with each name replaced by the term it names is the
term. -/
theorem foldF_join : ∀ t : Pat, (foldF S s t).bind id = t
  | .var _ => rfl
  | .sym _ => rfl
  | .app g b => by
    simp only [foldF, Term.bind]
    rw [foldF_join g]
    by_cases hb : Free S s b
    · rw [ite_eq_left hb]
      rfl
    · rw [ite_eq_right hb, foldF_join b]

theorem foldV_join (t : Pat) : (foldV S s t).bind id = t := by
  unfold foldV
  by_cases ht : Free S s t
  · rw [ite_eq_left ht]
    rfl
  · rw [ite_eq_right ht]
    exact foldF_join t

/-- A folded first-order term is first-order. -/
theorem foldF_fo : ∀ t : Pat, t.firstOrder = true →
    (foldF S s t).firstOrder = true ∧ ((∀ x, t ≠ .var x) → ∀ p, foldF S s t ≠ .var p)
  | .var x, _ => ⟨rfl, fun h => absurd rfl (h x)⟩
  | .sym _, _ => ⟨rfl, fun _ p => by simp [foldF]⟩
  | .app g b, hfo => by
    obtain ⟨hg, hb', hgv⟩ := Term.fo_app hfo
    obtain ⟨ihg, ihgv⟩ := foldF_fo g hg
    refine ⟨?_, fun _ p => by simp [foldF]⟩
    simp only [foldF]
    refine Term.fo_app_mk ihg ?_ (ihgv hgv)
    by_cases hb : Free S s b
    · rw [ite_eq_left hb]
      rfl
    · rw [ite_eq_right hb]
      exact (foldF_fo b hb').1

theorem foldV_fo {t : Pat} (hfo : t.firstOrder = true) : (foldV S s t).firstOrder = true := by
  unfold foldV
  by_cases ht : Free S s t
  · rw [ite_eq_left ht]
    rfl
  · rw [ite_eq_right ht]
    exact (foldF_fo t hfo).1

/-- A variable all of whose places in a term are inside the free subterm `u`
has all its places in a name of the folded term inside `u`. -/
theorem outF_leaf {u : Pat} (hu : Free S s u) {y : Nat} : ∀ t : Pat, y ∉ outF u t →
    ∀ p ∈ (foldF S s t).vars, y ∈ p.vars → y ∉ outV u p
  | .var x, h, p, hp, hy => by
    simp only [foldF, Term.vars, List.mem_singleton] at hp
    subst hp
    simp only [Term.vars, List.mem_singleton] at hy
    subst hy
    exact absurd (by simp [outF]) h
  | .sym _, _, p, hp, _ => by simp [foldF, Term.vars] at hp
  | .app g b, h, p, hp, hy => by
    simp only [outF, List.mem_append, not_or] at h
    simp only [foldF, Term.vars, List.mem_append] at hp
    rcases hp with hp | hp
    · exact outF_leaf hu g h.1 p hp hy
    · by_cases hb : Free S s b
      · simp only [ite_eq_left hb, Term.vars, List.mem_singleton] at hp
        subst hp
        exact h.2
      · rw [ite_eq_right hb] at hp
        have hbu : b ≠ u := fun e => hb (e ▸ hu)
        rw [ite_eq_right hbu] at h
        exact outF_leaf hu b h.2 p hp hy

theorem outV_leaf {u : Pat} (hu : Free S s u) {y : Nat} {t : Pat} (h : y ∉ outV u t) :
    ∀ p ∈ (foldV S s t).vars, y ∈ p.vars → y ∉ outV u p := by
  intro p hp hy
  unfold foldV at hp
  by_cases ht : Free S s t
  · simp only [ite_eq_left ht, Term.vars, List.mem_singleton] at hp
    subst hp
    exact h
  · rw [ite_eq_right ht] at hp
    have htu : t ≠ u := fun e => ht (e ▸ hu)
    unfold outV at h
    rw [ite_eq_right htu] at h
    exact outF_leaf hu t h p hp hy

/-- A term with a variable all of whose places are inside arguments equal to
`u` is larger than `u`. -/
theorem size_lt_of_not_outF {u : Pat} {y : Nat} : ∀ p : Pat, y ∈ p.vars → y ∉ outF u p →
    u.size < p.size
  | .var x, hy, h => by
    simp only [Term.vars, List.mem_singleton] at hy
    subst hy
    exact absurd (by simp [outF]) h
  | .sym _, hy, _ => by simp [Term.vars] at hy
  | .app g b, hy, h => by
    simp only [outF, List.mem_append, not_or] at h
    simp only [Term.vars, List.mem_append] at hy
    simp only [Term.size]
    rcases hy with hy | hy
    · have := size_lt_of_not_outF g hy h.1
      omega
    · by_cases e : b = u
      · subst e
        omega
      · rw [ite_eq_right e] at h
        have := size_lt_of_not_outF b hy h.2
        omega

/-- Two names of the folded pattern of a store that share a variable, one of
them free, are one name. -/
theorem leaf_disjoint {p u : Pat} (hp : p ∈ (foldV S s s.t).vars)
    (hu' : u ∈ (foldV S s s.t).vars) (hu : Free S s u) {y : Nat} (hyp : y ∈ p.vars)
    (hyu : y ∈ u.vars) : p = u := by
  by_contra hne
  have h1 := outV_leaf hu (hu.inside y hyu) p hp hyp
  unfold outV at h1
  rw [ite_eq_right hne] at h1
  have hsz := size_lt_of_not_outF p hyp h1
  rcases foldV_leaf s.t p hp with ⟨x, -, rfl⟩ | hpf
  · simp only [Term.vars, List.mem_singleton] at hyp
    subst hyp
    exact h1 (by simp [outF])
  · have h2 := outV_leaf hpf (hpf.inside y hyp) u hu' hyu
    unfold outV at h2
    rw [ite_eq_right (Ne.symm hne)] at h2
    have := size_lt_of_not_outF u hyu h2
    omega

end leaves

/-! ## The fold, computed -/

/-- `foldF` with `Free` decided. -/
def foldFc (S : Sorts) (r : Raw) : Pat → Term Pat
  | .var x => .var (.var x)
  | .sym f => .sym f
  | .app g b => .app (foldFc S r g) (if freeB S r b then .var b else foldFc S r b)

/-- `foldV` with `Free` decided. -/
def foldVc (S : Sorts) (r : Raw) (t : Pat) : Term Pat :=
  if freeB S r t then .var t else foldFc S r t

theorem foldFc_eq (hS : S.WellFormed) {r : Raw} (hR : r.Roomy S) : ∀ t : Pat,
    t.firstOrder = true → (∀ y ∈ t.vars, y < r.c.length) → foldFc S r t = foldF S r.store t
  | .var _, _, _ => rfl
  | .sym _, _, _ => rfl
  | .app g b, hfo, hv => by
    obtain ⟨hg, hb, -⟩ := Term.fo_app hfo
    have hvg : ∀ y ∈ g.vars, y < r.c.length := fun y hy => hv y (by simp [Term.vars, hy])
    have hvb : ∀ y ∈ b.vars, y < r.c.length := fun y hy => hv y (by simp [Term.vars, hy])
    simp only [foldFc, foldF]
    rw [foldFc_eq hS hR g hg hvg]
    congr 1
    by_cases hf : Free S r.store b
    · rw [ite_eq_left hf, ite_eq_left ((freeB_iff hS hR hb hvb).2 hf)]
    · rw [ite_eq_right hf, ite_eq_right fun h => hf ((freeB_iff hS hR hb hvb).1 h),
        foldFc_eq hS hR b hb hvb]

theorem foldVc_eq (hS : S.WellFormed) {r : Raw} (hR : r.Roomy S) {t : Pat}
    (hfo : t.firstOrder = true) (hv : ∀ y ∈ t.vars, y < r.c.length) :
    foldVc S r t = foldV S r.store t := by
  unfold foldVc foldV
  by_cases hf : Free S r.store t
  · rw [ite_eq_left hf, ite_eq_left ((freeB_iff hS hR hfo hv).2 hf)]
  · rw [ite_eq_right hf, ite_eq_right fun h => hf ((freeB_iff hS hR hfo hv).1 h),
      foldFc_eq hS hR t hfo hv]

/-! ## The folded store -/

/-- The names of the folded pattern, once each, in the order they first
occur. -/
def foldNames (S : Sorts) (r : Raw) : List Pat := firsts (foldVc S r r.t).vars

/-- The sorts of a name: the sorts of a variable, or the sorts of a
subterm. -/
def foldConj (S : Sorts) (r : Raw) : Pat → Conj
  | .var x => r.conj x
  | u => clo S r u

/-- The exclusions, over the numbers of the names. -/
def foldXs (S : Sorts) (r : Raw) : List (Eqns Nat) :=
  r.xs.map fun θ => Eqns.ren (fun x => (foldNames S r).idxOf (.var x)) (eqnsOf θ)

/-- The store the folded store is assembled from: the folded pattern with
its names numbered, the sorts of the names, and the exclusions renamed. -/
def foldStore (S : Sorts) (r : Raw) : Store :=
  ⟨(foldVc S r r.t).rename fun p => (foldNames S r).idxOf p,
    fun w => ((foldNames S r).map (foldConj S r)).getD w ∅, foldXs S r⟩

/-- The folded store. -/
def foldRaw (S : Sorts) (r : Raw) : Raw :=
  assembled S (foldStore S r).t ((foldNames S r).map (foldConj S r)) (foldStore S r).x

theorem foldConj_notVar {r : Raw} {p : Pat} (h : ∀ x, p ≠ .var x) :
    foldConj S r p = clo S r p := by
  cases p with
  | var x => exact absurd rfl (h x)
  | sym _ => rfl
  | app _ _ => rfl

/-- The sorts of a name hold of its instances. -/
theorem foldConj_holds {r : Raw} {p : Pat} (hfo : p.firstOrder = true) {σ : Nat → GTerm}
    (hσ : σ ∈ r.store.Pos S) : MemC S (foldConj S r p) (p.bind σ) := by
  cases p with
  | var x => exact hσ x
  | sym _ => exact fun n hn => clo_mem hfo hn hσ
  | app _ _ => exact fun n hn => clo_mem hfo hn hσ

section folded

variable {r : Raw}

/-- What is used of the names of the folded pattern of a store. -/
structure Names (S : Sorts) (r : Raw) : Prop where
  eq : foldVc S r r.t = foldV S r.store r.t
  mem : ∀ p, p ∈ foldNames S r ↔ p ∈ (foldV S r.store r.t).vars
  nodup : (foldNames S r).Nodup
  lt : ∀ p ∈ (foldV S r.store r.t).vars, (foldNames S r).idxOf p < (foldNames S r).length
  get : ∀ p ∈ (foldV S r.store r.t).vars,
    (foldNames S r).getD ((foldNames S r).idxOf p) (.sym "") = p
  conj : ∀ p ∈ (foldV S r.store r.t).vars,
    ((foldNames S r).map (foldConj S r)).getD ((foldNames S r).idxOf p) ∅ = foldConj S r p
  fo : ∀ p ∈ (foldV S r.store r.t).vars, p.firstOrder = true
  vars : ∀ p ∈ (foldV S r.store r.t).vars, ∀ y ∈ p.vars, y < r.c.length
  cover : ∀ y, y < r.c.length → ∃ p ∈ (foldV S r.store r.t).vars, y ∈ p.vars
  kept : ∀ θ ∈ r.x, ∀ x ∈ (eqnsOf θ).vars, .var x ∈ (foldV S r.store r.t).vars

theorem names_of_roomy (hS : S.WellFormed) (hR : r.Roomy S) : Names S r := by
  have hr := hR.shaped
  have hT : foldVc S r r.t = foldV S r.store r.t :=
    foldVc_eq hS hR hr.fo fun y hy => (hr.len y).1 hy
  have hmem : ∀ p, p ∈ foldNames S r ↔ p ∈ (foldV S r.store r.t).vars := by
    intro p
    unfold foldNames
    rw [hT]
    exact mem_firsts
  have hlt : ∀ p ∈ (foldV S r.store r.t).vars,
      (foldNames S r).idxOf p < (foldNames S r).length :=
    fun p hp => List.idxOf_lt_length_iff.2 ((hmem p).2 hp)
  have hvars : ∀ p ∈ (foldV S r.store r.t).vars, ∀ y ∈ p.vars, y < r.c.length :=
    fun p hp y hy => (hr.len y).1 (foldV_vars S r.store r.t p hp y hy)
  have hfo : ∀ p ∈ (foldV S r.store r.t).vars, p.firstOrder = true :=
    fun p hp => foldV_leaf_fo hr.fo p hp
  have hcover : ∀ y, y < r.c.length → ∃ p ∈ (foldV S r.store r.t).vars, y ∈ p.vars := by
    intro y hy
    have h' : y ∈ ((foldV S r.store r.t).bind id).vars := by
      rw [foldV_join]
      exact (hr.len y).2 hy
    exact Term.mem_vars_bind.1 h'
  refine ⟨hT, hmem, ?_, hlt, fun p hp => ?_, fun p hp => ?_, hfo, hvars, hcover, ?_⟩
  · unfold foldNames
    exact (firsts_spec _).1
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hlt p hp),
      List.getElem_idxOf (hlt p hp)]
  · simp [List.getD_eq_getElem?_getD, hlt p hp, List.getElem_idxOf (hlt p hp)]
  · intro θ hθ x hx
    have hN := hr.ex θ hθ
    have hxl : x < r.c.length := by
      obtain ⟨q, hq, hv⟩ := List.mem_flatMap.1 hx
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hq
      simp only [Term.vars, List.cons_append, List.nil_append, List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact hN.dom b hb
      · exact (hN.ran b hb x hv).1
    obtain ⟨p, hp, hxp⟩ := hcover x hxl
    rcases foldV_leaf r.store.t p hp with ⟨x', -, rfl⟩ | hf
    · simp only [Term.vars, List.mem_singleton] at hxp
      exact hxp ▸ hp
    · exact absurd hx (hf.not_excl hS hR (hfo p hp) (hvars p hp) θ hθ x hxp)

/-- The sorts of a name are the declared sorts that hold of its instance at
every solution. -/
theorem foldConj_iff (hR : r.Roomy S) (hN : Names S r) {p : Pat}
    (hp : p ∈ (foldV S r.store r.t).vars) (n : Name) :
    n ∈ foldConj S r p ↔ n ∈ Sorts.names S ∧ ∀ σ ∈ r.store.Sol S, mem S n (p.bind σ) = true := by
  have hr := hR.shaped
  obtain ⟨σ₀, hσ₀⟩ := hR.sol
  rcases foldV_leaf r.store.t p hp with ⟨x, -, rfl⟩ | hf
  · exact hr.up x (hN.vars _ hp x (by simp [Term.vars])) n
  · rw [foldConj_notVar hf.app]
    constructor
    · intro hn
      exact ⟨(mem_clo.1 hn).1, fun σ hσ => clo_mem (hN.fo p hp) hn hσ.1⟩
    · rintro ⟨-, h⟩
      exact mem_clo_of_all hr (hN.fo p hp) (hN.vars p hp) hσ₀ h

/-- The store is the store the folded store is assembled from, with each
number replaced by the name it numbers. -/
theorem foldStore_linked (hS : S.WellFormed) (hR : r.Roomy S) :
    Linked S (foldStore S r) r.store fun w => (foldNames S r).getD w (.sym "") := by
  have hr := hR.shaped
  have hN := names_of_roomy hS hR
  obtain ⟨σ₀, hσ₀⟩ := hR.sol
  refine ⟨?_, fun σ hσ => ⟨fun w => ?_, fun E' hE' hu => ?_⟩, fun σ₂ hσ₂ => ?_⟩
  · show r.t = ((foldVc S r r.t).rename fun p => (foldNames S r).idxOf p).bind _
    rw [hN.eq]
    simp only [Term.rename, Term.bind_bind, Term.bind]
    conv_lhs => rw [← foldV_join (S := S) (s := r.store) r.t]
    exact Term.bind_congr fun p hp => (hN.get p hp).symm
  · show MemC S (((foldNames S r).map (foldConj S r)).getD w ∅)
      (((foldNames S r).getD w (.sym "")).bind σ)
    by_cases hw : w < (foldNames S r).length
    · have e1 : ((foldNames S r).map (foldConj S r)).getD w ∅ =
          foldConj S r (foldNames S r)[w] := by simp [List.getD_eq_getElem?_getD, hw]
      have e2 : (foldNames S r).getD w (.sym "") = (foldNames S r)[w] := by
        simp [List.getD_eq_getElem?_getD, hw]
      rw [e1, e2]
      exact foldConj_holds (hN.fo _ ((hN.mem _).1 (List.getElem_mem hw))) hσ.1
    · have e1 : ((foldNames S r).map (foldConj S r)).getD w ∅ = ∅ := by
        simp [List.getD_eq_getElem?_getD, hw]
      rw [e1]
      intro n hn
      simp at hn
  · obtain ⟨θ, hθ, rfl⟩ := List.mem_map.1 hE'
    rw [Raw.mem_xs] at hθ
    rw [unifies_ren] at hu
    refine hσ.2 (eqnsOf θ) (Raw.mem_store_x.2 ⟨θ, hθ, rfl⟩)
      (unifies_congr (fun q hq v hv => ?_) hu)
    show ((foldNames S r).getD ((foldNames S r).idxOf (.var v)) (.sym "")).bind σ = σ v
    rw [hN.get _ (hN.kept θ hθ v (List.mem_flatMap.2 ⟨q, hq, hv⟩))]
    rfl
  · -- an instance of each free name with the value its number has
    have hinst : ∀ p, p ∈ (foldV S r.store r.t).vars → Free S r.store p →
        ∃ σp : Nat → GTerm, (∀ y ∈ p.vars, MemC S (r.conj y) (σp y)) ∧
          p.bind σp = σ₂ ((foldNames S r).idxOf p) := by
      intro p hp hf
      have hm : MemC S (clo S r p) (σ₂ ((foldNames S r).idxOf p)) := by
        have := hσ₂.1 ((foldNames S r).idxOf p)
        change MemC S (((foldNames S r).map (foldConj S r)).getD _ ∅) _ at this
        rwa [hN.conj p hp, foldConj_notVar hf.app] at this
      obtain ⟨σ, hσ, e⟩ := hf.inst hr (hN.fo p hp) (hN.vars p hp) hσ₀ hm
      exact ⟨σ, fun y _ => hσ.1 y, e⟩
    classical
    have : Nonempty (Nat → GTerm) := ⟨σ₀⟩
    choose! G hG using hinst
    let σ : Nat → GTerm := fun y =>
      if h : ∃ p, p ∈ (foldV S r.store r.t).vars ∧ Free S r.store p ∧ y ∈ p.vars
      then G (Classical.choose h) y else σ₂ ((foldNames S r).idxOf (.var y))
    have hσF : ∀ p ∈ (foldV S r.store r.t).vars, Free S r.store p →
        ∀ y ∈ p.vars, σ y = G p y := by
      intro p hp hf y hy
      have hex : ∃ p, p ∈ (foldV S r.store r.t).vars ∧ Free S r.store p ∧ y ∈ p.vars :=
        ⟨p, hp, hf, hy⟩
      obtain ⟨h1, -, h3⟩ := Classical.choose_spec hex
      have : Classical.choose hex = p := leaf_disjoint (s := r.store) h1 hp hf h3 hy
      simp only [σ, hex, ↓reduceDIte, this]
    have hσV : ∀ x, .var x ∈ (foldV S r.store r.t).vars →
        σ x = σ₂ ((foldNames S r).idxOf (.var x)) := by
      intro x hx
      have hno : ¬ ∃ p, p ∈ (foldV S r.store r.t).vars ∧ Free S r.store p ∧ x ∈ p.vars := by
        rintro ⟨p, hp, hf, hy⟩
        exact hf.app x (leaf_disjoint (s := r.store) hx hp hf (by simp [Term.vars]) hy).symm
      simp only [σ, hno, ↓reduceDIte]
    refine ⟨σ, ⟨fun y => ?_, fun E hE hu => ?_⟩, fun w hw => ?_⟩
    · show MemC S (r.conj y) (σ y)
      by_cases hy : y < r.c.length
      · obtain ⟨p, hp, hyp⟩ := hN.cover y hy
        rcases foldV_leaf r.store.t p hp with ⟨x, -, rfl⟩ | hf
        · simp only [Term.vars, List.mem_singleton] at hyp
          subst hyp
          rw [hσV y hp]
          have := hσ₂.1 ((foldNames S r).idxOf (.var y))
          change MemC S (((foldNames S r).map (foldConj S r)).getD _ ∅) _ at this
          rwa [hN.conj _ hp] at this
        · rw [hσF p hp hf y hyp]
          exact (hG p hp hf).1 y hyp
      · rw [Raw.Normal.conj_of_ge r (Nat.le_of_not_lt hy)]
        intro n hn
        simp at hn
    · obtain ⟨θ, hθ, rfl⟩ := Raw.mem_store_x.1 hE
      refine hσ₂.2 (Eqns.ren (fun x => (foldNames S r).idxOf (.var x)) (eqnsOf θ))
        (List.mem_map.2 ⟨θ, Raw.mem_xs.2 hθ, rfl⟩)
        (unifies_ren.2 (unifies_congr (fun q hq v hv => ?_) hu))
      exact hσV v (hN.kept θ hθ v (List.mem_flatMap.2 ⟨q, hq, hv⟩))
    · have hw' : w ∈ ((foldVc S r r.t).rename fun p => (foldNames S r).idxOf p).vars := hw
      rw [hN.eq, Term.vars_rename] at hw'
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hw'
      rw [hN.get p hp]
      rcases foldV_leaf r.store.t p hp with ⟨x, -, rfl⟩ | hf
      · exact hσV x hp
      · rw [Term.bind_congr (hσF p hp hf)]
        exact (hG p hp hf).2

/-- The store assembled from the folded pattern, the sorts of its names and
any list of the renamed exclusions is determined by its pattern and what it
denotes, it denotes what the store does, its pattern is the folded pattern,
and the exclusions it keeps are listed once each. -/
theorem assembled_fold (hS : S.WellFormed) (hR : r.Roomy S) {X' : List (Eqns Nat)}
    (hX : ∀ E, E ∈ X' ↔ E ∈ foldXs S r) :
    (assembled S (foldStore S r).t ((foldNames S r).map (foldConj S r)) X').Shaped S ∧
      (assembled S (foldStore S r).t ((foldNames S r).map (foldConj S r)) X').store.Den S =
        r.store.Den S ∧
      (assembled S (foldStore S r).t ((foldNames S r).map (foldConj S r)) X').t =
        foldPat S r.store ∧
      (antichain (covers ((foldNames S r).map (foldConj S r)).length)
        (normExs S ⟨(foldStore S r).t, (foldNames S r).map (foldConj S r), ∅⟩ X')).Nodup := by
  have hr := hR.shaped
  have hN := names_of_roomy hS hR
  have hL := foldStore_linked hS hR
  obtain ⟨σ₀, hσ₀⟩ := hR.sol
  let sX : Store := ⟨(foldStore S r).t, (foldStore S r).c, X'⟩
  have hsolX : sX.Sol S = (foldStore S r).Sol S := by
    ext σ
    show (σ ∈ sX.Pos S ∧ ∀ E ∈ X', ¬ Eqns.Unifies σ E) ↔
      (σ ∈ (foldStore S r).Pos S ∧ ∀ E ∈ foldXs S r, ¬ Eqns.Unifies σ E)
    exact ⟨fun h => ⟨h.1, fun E hE => h.2 E ((hX E).2 hE)⟩,
      fun h => ⟨h.1, fun E hE => h.2 E ((hX E).1 hE)⟩⟩
  have hne : (sX.Sol S).Nonempty := by rw [hsolX]; exact ⟨_, hL.down σ₀ hσ₀⟩
  have htv : ∀ w ∈ sX.t.vars, w < (foldNames S r).length := by
    intro w hw
    have hw' : w ∈ ((foldVc S r r.t).rename fun p => (foldNames S r).idxOf p).vars := hw
    rw [hN.eq, Term.vars_rename] at hw'
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hw'
    exact hN.lt p hp
  have hget : ∀ w (hw : w < (foldNames S r).length),
      (foldNames S r)[w] ∈ (foldV S r.store r.t).vars ∧
        (foldNames S r).idxOf (foldNames S r)[w] = w :=
    fun w hw => ⟨(hN.mem _).1 (List.getElem_mem hw), hN.nodup.idxOf_getElem w hw⟩
  have hvars : ∀ w, w ∈ sX.t.vars ↔ w < (foldNames S r).length := by
    refine fun w => ⟨htv w, fun hw => ?_⟩
    show w ∈ ((foldVc S r r.t).rename fun p => (foldNames S r).idxOf p).vars
    rw [hN.eq, Term.vars_rename]
    exact List.mem_map.2 ⟨_, (hget w hw).1, (hget w hw).2⟩
  have hfin : sX.Fin (foldNames S r).length := by
    refine ⟨?_, htv, fun w hw => ?_, ?_, ?_⟩
    · show ((foldVc S r r.t).rename fun p => (foldNames S r).idxOf p).firstOrder = true
      rw [hN.eq]
      exact Term.fo_bind (foldV_fo hr.fo) fun _ _ => rfl
    · show ((foldNames S r).map (foldConj S r)).getD w ∅ = ∅
      simp [List.getD_eq_getElem?_getD, hw]
    · intro E' hE' q hq
      obtain ⟨θ, hθ, rfl⟩ := List.mem_map.1 ((hX E').1 hE')
      rw [Raw.mem_xs] at hθ
      obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hq'
      exact ⟨rfl, rename_fo ((hr.ex θ hθ).fo b hb) _⟩
    · intro E' hE' q hq w hw
      obtain ⟨θ, hθ, rfl⟩ := List.mem_map.1 ((hX E').1 hE')
      rw [Raw.mem_xs] at hθ
      obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
      have hw' : w ∈ (q'.1.vars ++ q'.2.vars).map
          fun x => (foldNames S r).idxOf (Term.var x) := by
        simpa [Term.vars_rename] using hw
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hw'
      exact hN.lt _ (hN.kept θ hθ x (List.mem_flatMap.2 ⟨q', hq', hx⟩))
  have hocc : FirstOcc sX.t.vars := by
    show FirstOcc ((foldVc S r r.t).rename fun p =>
      (firsts (foldVc S r r.t).vars).idxOf p).vars
    rw [Term.vars_rename]
    exact firstOcc_map_firsts _
  have hcL : ∀ v n, n ∈ ((foldNames S r).map (foldConj S r)).getD v ∅ ↔
      v < (foldNames S r).length ∧ n ∈ Sorts.names S ∧
        ∀ σ ∈ sX.Sol S, mem S n (σ v) = true := by
    rw [hsolX]
    intro v n
    by_cases hv : v < (foldNames S r).length
    · obtain ⟨hp, hidx⟩ := hget v hv
      have e1 : ((foldNames S r).map (foldConj S r)).getD v ∅ =
          foldConj S r (foldNames S r)[v] := by simp [List.getD_eq_getElem?_getD, hv]
      have e2 : (foldNames S r).getD v (.sym "") = (foldNames S r)[v] := by
        simp [List.getD_eq_getElem?_getD, hv]
      rw [e1, foldConj_iff hR hN hp]
      constructor
      · rintro ⟨hn, h⟩
        refine ⟨hv, hn, fun σ hσ => ?_⟩
        obtain ⟨σ', hσ', e⟩ := hL.up σ hσ
        have := e v ((hvars v).2 hv)
        simp only [e2] at this
        rw [← this]
        exact h σ' hσ'
      · rintro ⟨-, hn, h⟩
        refine ⟨hn, fun σ' hσ' => ?_⟩
        have := h _ (hL.down σ' hσ')
        simpa only [e2] using this
    · have e1 : ((foldNames S r).map (foldConj S r)).getD v ∅ = ∅ := by
        simp [List.getD_eq_getElem?_getD, hv]
      rw [e1]
      simp [hv]
  obtain ⟨hsh, hsol'⟩ := assembled_shaped hS hfin hocc hvars hne (by simp) hcL
  have hnd := assembled_nodup hS hfin hne (by simp) hcL
  refine ⟨hsh, ?_, ?_, hnd⟩
  · show {g | ∃ σ ∈ (assembled S sX.t ((foldNames S r).map (foldConj S r)) sX.x).store.Sol S,
      g = _} = _
    rw [hsol', hsolX]
    exact hL.den.symm
  · show ((foldVc S r r.t).rename fun p => (firsts (foldVc S r r.t).vars).idxOf p) = _
    rw [hN.eq]
    rfl

/-- The folded store is determined by its pattern and what it denotes, it
denotes what the store does, and its pattern is the folded pattern. -/
theorem foldRaw_spec (hS : S.WellFormed) (hR : r.Roomy S) :
    (foldRaw S r).Shaped S ∧ (foldRaw S r).store.Den S = r.store.Den S ∧
      (foldRaw S r).t = foldPat S r.store := by
  obtain ⟨h1, h2, h3, -⟩ := assembled_fold hS hR (X' := foldXs S r) fun _ => Iff.rfl
  exact ⟨h1, h2, h3⟩

end folded

/-! ## The folded canonical store -/

/-- The raw store is the folded canonical store of a normal store: it is
determined by its pattern and what it denotes, it denotes what the normal
store does, and its pattern is the folded pattern of the normal store. -/
def FoldOf (S : Sorts) (n r : Raw) : Prop :=
  r.Shaped S ∧ r.store.Den S = n.store.Den S ∧ r.t = foldPat S n.store

/-- A normal store has one folded canonical store. -/
theorem FoldOf.eq (hS : S.WellFormed) {n r r' : Raw} (h : FoldOf S n r) (h' : FoldOf S n r') :
    r = r' :=
  h.1.eq_of_t hS h'.1 (h.2.2.trans h'.2.2.symm) (h.2.1.trans h'.2.1.symm)

/-- Normal stores with the same folded canonical store are the same. -/
theorem FoldOf.inj (hS : S.WellFormed) {n n' r : Raw} (hn : n.Normal S) (hn' : n'.Normal S)
    (h : FoldOf S n r) (h' : FoldOf S n' r) : n = n' :=
  hn.eq hS hn' (h.2.1.symm.trans h'.2.1)

/-- The store assembled from a store that satisfies `Inv` has a solution, and
each of its variables has infinitely many values in its sorts. -/
theorem roomy_ofTight (hS : S.WellFormed) {s : CStore} (hI : Inv S s) :
    (ofTight S s).Roomy S := by
  obtain ⟨hsh, hsol, -, -⟩ := ofTight_shaped hS hI
  obtain ⟨-, h₁, h₂⟩ := renum_spec s.t.vars
  have hinv : ∀ v ∈ s.store.t.vars,
      (fun w => (firsts s.t.vars).getD w 0) ((fun v => (firsts s.t.vars).idxOf v) v) = v :=
    fun v hv => (h₁ v hv).2
  have hrest : ∀ v, ({g | MemC S (s.conj v) g} \ {g | g ∈ gone s.x v}).Infinite :=
    fun v => (hI.infinite hS v).sdiff (List.finite_toSet _)
  have hsub : ∀ w, w < (ofTight S s).c.length →
      {g | MemC S (s.conj ((firsts s.t.vars).getD w 0)) g} \
          {g | g ∈ gone s.x ((firsts s.t.vars).getD w 0)} ⊆
        {g | MemC S ((ofTight S s).conj w) g} := by
    rintro w hw g ⟨hg, hgone⟩ n hn
    obtain ⟨τ, hτ, rfl⟩ := hI.exists_sol hS _ hg hgone
    have hτ' := (ren_fwd (S := S) (ρ := fun v => (firsts s.t.vars).idxOf v)
      (ρ' := fun w => (firsts s.t.vars).getD w 0) hI.full hinv hτ).1
    rw [← hsol] at hτ'
    exact ((hsh.up w hw n).1 hn).2 _ hτ'
  refine ⟨hsh, ?_, fun w hw => (hrest _).mono (hsub w hw)⟩
  obtain ⟨g, hg, hgone⟩ := (hrest 0).nonempty
  obtain ⟨τ, hτ, -⟩ := hI.exists_sol hS 0 hg hgone
  have hτ' := (ren_fwd (S := S) (ρ := fun v => (firsts s.t.vars).idxOf v)
      (ρ' := fun w => (firsts s.t.vars).getD w 0) hI.full hinv hτ).1
  rw [← hsol] at hτ'
  exact ⟨_, hτ'⟩

/-- Folding the store assembled from a store tight on the variables its
exclusions mention gives the folded canonical store of what it denotes. -/
theorem foldRaw_ofTight (hS : S.WellFormed) {s : CStore} (hI : Inv S s) (hX : XTight S s)
    {P : Prob} (hP : P.FO) (hden : s.store.Den S = P.Den S) :
    ∃ n, P.norm S hS = some n ∧ FoldOf S n (foldRaw S (ofTight S s)) := by
  obtain ⟨n, hn, -, hd, hf⟩ := foldPat_ofTight_norm hS hI hX hP hden
  obtain ⟨hsh, hd', ht⟩ := foldRaw_spec hS (roomy_ofTight hS hI)
  exact ⟨n, hn, hsh, hd'.trans hd, ht.trans hf⟩

/-- The same of the store assembled from any list of the renamed exclusions
of the fold. -/
theorem assembled_ofTight (hS : S.WellFormed) {s : CStore} (hI : Inv S s) (hX : XTight S s)
    {P : Prob} (hP : P.FO) (hden : s.store.Den S = P.Den S) {X' : List (Eqns Nat)}
    (hX' : ∀ E, E ∈ X' ↔ E ∈ foldXs S (ofTight S s)) :
    ∃ n, P.norm S hS = some n ∧
      FoldOf S n (assembled S (foldStore S (ofTight S s)).t
        ((foldNames S (ofTight S s)).map (foldConj S (ofTight S s))) X') := by
  obtain ⟨n, hn, -, hd, hf⟩ := foldPat_ofTight_norm hS hI hX hP hden
  obtain ⟨hsh, hd', ht, -⟩ := assembled_fold hS (roomy_ofTight hS hI) hX'
  exact ⟨n, hn, hsh, hd'.trans hd, ht.trans hf⟩

end Sorts
end RwLog
