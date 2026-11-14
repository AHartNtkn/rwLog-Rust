/-
# Deciding that sorts are well formed

`Sorts.WellFormed` (`Trusted/Semantics.lean`) says that the terms common to
finitely many sorts are none, one, or infinitely many. It is decided here
(`wellFormed_iff`, and the `Decidable` instance): over the conjunctions of
declared sorts,

* `big S` holds those with two different members, and
* `fin S` those with finitely many,

each a least fixpoint, and the sorts are well formed exactly when no
conjunction is in both. With it `ProgramOf.WellFormed` is decidable (L56).
-/
import RwLog.Sorts.Empty
import RwLog.Sorts.Trusted
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Fintype.Pi

namespace RwLog
namespace Sorts

open Function

variable {S : Sorts}

/-- Every sort of `c` accepts the root, and each argument can be filled: the
sorts required of it are in `L`, the conjunctions that have a member. -/
def LiveKey (S : Sorts) (L : Finset Conj) (c : Conj) (key : Sym × Nat) : Prop :=
  Accepts S c key.1 key.2 ∧ ∀ i < key.2, kidC S c key.1 key.2 i ∈ L

instance (S : Sorts) (L : Finset Conj) (c : Conj) (key : Sym × Nat) :
    Decidable (LiveKey S L c key) := by
  unfold LiveKey; infer_instance

theorem memC_ofFn {c : Conj} {f : Sym} {k : Nat} (hacc : Accepts S c f k) {w : Fin k → GTerm}
    (hw : ∀ i : Fin k, MemC S (kidC S c f k i) (w i)) : MemC S c (Term.mk f (List.ofFn w)) := by
  refine memC_mk.mpr ⟨by simpa using hacc, ?_⟩
  intro i hi
  simp only [List.length_ofFn] at hi ⊢
  simpa using hw ⟨i, hi⟩

theorem LiveKey.fn {c : Conj} {f : Sym} {k : Nat} (h : LiveKey S (live S) c (f, k)) :
    ∃ w : Fin k → GTerm, ∀ i : Fin k, MemC S (kidC S c f k i) (w i) :=
  ⟨fun i => Classical.choose (mem_live_iff.1 (h.2 i i.2)),
    fun i => Classical.choose_spec (mem_live_iff.1 (h.2 i i.2))⟩

theorem liveKey_of_memC {c : Conj} {f : Sym} {ts : List GTerm} (h : MemC S c (Term.mk f ts)) :
    LiveKey S (live S) c (f, ts.length) :=
  ⟨(memC_mk.1 h).1, fun i hi => mem_live_iff.2 ⟨ts[i], (memC_mk.1 h).2 i hi⟩⟩

theorem restOK_of_not_caseKey {c : Conj} {f : Sym} {k : Nat} (hacc : Accepts S c f k)
    (hkey : (f, k) ∉ caseKeys S c) : RestOK S c := by
  intro n hn
  have := hacc n hn
  rw [Option.isSome_iff_exists] at this
  obtain ⟨ks, hs⟩ := this
  obtain ⟨d, hd, hcase⟩ := step_cases hs
  rcases hcase with ⟨cs, hcs, h1, h2, _⟩ | ⟨_, ex, r, hr, _, _⟩
  · exfalso
    apply hkey
    simp only [caseKeys, Finset.mem_biUnion]
    refine ⟨n, hn, ?_⟩
    simp only [hd, List.mem_toFinset, List.mem_map]
    exact ⟨cs, hcs, by simp [h1, h2]⟩
  · simp [hd, hr]

/-- An argument is smaller than the term. -/
theorem size_lt_mk {f : Sym} {ts : List GTerm} {u : GTerm} (hu : u ∈ ts) :
    u.size < (Term.mk f ts).size := by
  obtain ⟨f', ts', e, hlt⟩ := exists_mk (Term.mk f ts)
  obtain ⟨-, rfl⟩ := Term.mk_inj e
  exact hlt u hu

/-- When every sort of `c` has a rest, `c` has infinitely many members. -/
theorem restOK_infinite {c : Conj} (h : RestOK S c) : {t | MemC S c t}.Infinite := by
  intro hfin
  have hpre : ((fun g : Sym => (Term.mk g [] : GTerm)) ⁻¹' {t | MemC S c t}).Finite :=
    hfin.preimage fun a _ b _ e => (Term.mk_inj e).1
  have hsub : ((usedSyms S : Set Sym))ᶜ ⊆ (fun g : Sym => (Term.mk g [] : GTerm)) ⁻¹' {t | MemC S c t} :=
    fun g hg => restOK_fresh h (by simpa using hg)
  exact (Set.Finite.infinite_compl (Finset.finite_toSet (usedSyms S))) (hpre.subset hsub)

/-! ## Two different members -/

/-- One round: the conjunctions with two different members, given that those
in `P` have. -/
def growBig (S : Sorts) (L P : Finset Conj) : Finset Conj :=
  (names S).powerset.filter fun c =>
    RestOK S c ∨
    (∃ k₁ ∈ caseKeys S c, ∃ k₂ ∈ caseKeys S c, k₁ ≠ k₂ ∧ LiveKey S L c k₁ ∧ LiveKey S L c k₂) ∨
    ∃ key ∈ caseKeys S c, LiveKey S L c key ∧ ∃ i < key.2, kidC S c key.1 key.2 i ∈ P

/-- The conjunctions with two different members. -/
def big (S : Sorts) : Finset Conj := saturate (names S).powerset (growBig S (live S))

theorem mem_big_iff {c : Conj} :
    c ∈ big S ↔ ∃ t₁ t₂, t₁ ≠ t₂ ∧ MemC S c t₁ ∧ MemC S c t₂ := by
  constructor
  · revert c
    apply saturate.induction
    intro P hP c hc
    simp only [growBig, Finset.mem_inter, Finset.mem_filter] at hc
    rcases hc.1.2 with hr | ⟨⟨f₁, k₁⟩, -, ⟨f₂, k₂⟩, -, hne, h₁, h₂⟩ | ⟨⟨f, k⟩, -, hl, i, hi, hk⟩
    · obtain ⟨g₁, hg₁⟩ := Infinite.exists_notMem_finset (usedSyms S)
      obtain ⟨g₂, hg₂⟩ := Infinite.exists_notMem_finset (insert g₁ (usedSyms S))
      rw [Finset.mem_insert, not_or] at hg₂
      exact ⟨_, _, fun e => hg₂.1 (Term.mk_inj e).1.symm, restOK_fresh hr hg₁,
        restOK_fresh hr hg₂.2⟩
    · obtain ⟨w₁, hw₁⟩ := h₁.fn
      obtain ⟨w₂, hw₂⟩ := h₂.fn
      refine ⟨_, _, ?_, memC_ofFn h₁.1 hw₁, memC_ofFn h₂.1 hw₂⟩
      intro e
      obtain ⟨rfl, e'⟩ := Term.mk_inj e
      have := congrArg List.length e'
      simp only [List.length_ofFn] at this
      subst this
      exact hne rfl
    · obtain ⟨w, hw⟩ := hl.fn
      obtain ⟨u₁, u₂, hne, hu₁, hu₂⟩ := hP _ hk
      have hmem : ∀ u, MemC S (kidC S c f k i) u → ∀ j : Fin k,
          MemC S (kidC S c f k j) (update w ⟨i, hi⟩ u j) := by
        intro u hu j
        by_cases hj : j = ⟨i, hi⟩
        · subst hj; simpa using hu
        · rw [update_of_ne hj]; exact hw j
      refine ⟨_, _, ?_, memC_ofFn hl.1 (hmem u₁ hu₁), memC_ofFn hl.1 (hmem u₂ hu₂)⟩
      intro e
      have e' := List.ofFn_injective (Term.mk_inj e).2
      have := congrFun e' ⟨i, hi⟩
      simp only [update_self] at this
      exact hne this
  · rintro ⟨t₁, t₂, hne, h₁, h₂⟩
    induction hsz : t₁.size using Nat.strong_induction_on generalizing c t₁ t₂ with
    | _ sz ih =>
      obtain ⟨f₁, ts₁, rfl, hlt⟩ := exists_mk t₁
      obtain ⟨f₂, ts₂, rfl, -⟩ := exists_mk t₂
      have hsub := subset_names_of_memC h₁
      apply saturate.closed
      simp only [growBig, Finset.mem_inter, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨⟨hsub, ?_⟩, hsub⟩
      by_cases hr : RestOK S c
      · exact Or.inl hr
      · right
        have hk₁ : (f₁, ts₁.length) ∈ caseKeys S c := by
          by_contra h; exact hr (restOK_of_not_caseKey (memC_mk.1 h₁).1 h)
        have hk₂ : (f₂, ts₂.length) ∈ caseKeys S c := by
          by_contra h; exact hr (restOK_of_not_caseKey (memC_mk.1 h₂).1 h)
        by_cases hkey : (f₁, ts₁.length) = (f₂, ts₂.length)
        · right
          simp only [Prod.mk.injEq] at hkey
          obtain ⟨rfl, hlen⟩ := hkey
          have hts : ts₁ ≠ ts₂ := fun e => hne (by rw [e])
          have : ∃ i, ∃ (h₁' : i < ts₁.length) (h₂' : i < ts₂.length), ts₁[i] ≠ ts₂[i] := by
            by_contra hno
            apply hts
            apply List.ext_getElem hlen
            intro i h₁' h₂'
            by_contra hne'
            exact hno ⟨i, h₁', h₂', hne'⟩
          obtain ⟨i, hi₁, hi₂, hne'⟩ := this
          refine ⟨(f₁, ts₁.length), hk₁, liveKey_of_memC h₁, i, hi₁, ?_⟩
          have m₂ := (memC_mk.1 h₂).2 i hi₂
          rw [← hlen] at m₂
          exact ih _ (by subst hsz; exact hlt _ (List.getElem_mem hi₁)) (t₁ := ts₁[i])
            (t₂ := ts₂[i]) hne' ((memC_mk.1 h₁).2 i hi₁) m₂ rfl
        · exact Or.inl ⟨_, hk₁, _, hk₂, hkey, liveKey_of_memC h₁, liveKey_of_memC h₂⟩

/-! ## Finitely many members -/

/-- One round: the conjunctions with finitely many members, given that those
in `P` have. -/
def growFin (S : Sorts) (L P : Finset Conj) : Finset Conj :=
  (names S).powerset.filter fun c =>
    ¬ RestOK S c ∧
      ∀ key ∈ caseKeys S c, LiveKey S L c key → ∀ i < key.2, kidC S c key.1 key.2 i ∈ P

/-- The conjunctions with finitely many members. -/
def fin (S : Sorts) : Finset Conj := saturate (names S).powerset (growFin S (live S))

theorem finite_of_mem_fin : ∀ c ∈ fin S, {t | MemC S c t}.Finite := by
  apply saturate.induction
  intro P hP c hc
  simp only [growFin, Finset.mem_inter, Finset.mem_filter] at hc
  obtain ⟨hr, hkeys⟩ := hc.1.2
  classical
  let B : Sym × Nat → Set GTerm := fun key =>
    (fun w : Fin key.2 → GTerm => Term.mk key.1 (List.ofFn w)) ''
      {w | ∀ i : Fin key.2, MemC S (kidC S c key.1 key.2 i) (w i)}
  have hB : ∀ key ∈ (caseKeys S c).filter (LiveKey S (live S) c), (B key).Finite := by
    intro key hkey
    rw [Finset.mem_filter] at hkey
    refine Set.Finite.image _ ?_
    have : {w : Fin key.2 → GTerm | ∀ i : Fin key.2, MemC S (kidC S c key.1 key.2 i) (w i)} =
        Set.pi Set.univ fun i : Fin key.2 => {t | MemC S (kidC S c key.1 key.2 i) t} := by
      ext w; simp [Set.mem_pi]
    rw [this]
    exact Set.Finite.pi fun i => hP _ (hkeys key hkey.1 hkey.2 i i.2)
  refine (Set.Finite.biUnion (Finset.finite_toSet _) hB).subset ?_
  intro t ht
  obtain ⟨f, ts, rfl, -⟩ := exists_mk t
  have hk : (f, ts.length) ∈ caseKeys S c := by
    by_contra h; exact hr (restOK_of_not_caseKey (memC_mk.1 ht).1 h)
  simp only [Set.mem_iUnion, Finset.mem_coe, Finset.mem_filter]
  refine ⟨(f, ts.length), ⟨hk, liveKey_of_memC ht⟩, fun i => ts[i.1], fun i => (memC_mk.1 ht).2 i i.2, ?_⟩
  show Term.mk f (List.ofFn fun i : Fin ts.length => ts[i.1]) = Term.mk f ts
  rw [List.ofFn_getElem]

theorem mem_fin_of_finite : ∀ (n : Nat) (c : Conj), c ⊆ names S → {t | MemC S c t}.Finite →
    (∀ t, MemC S c t → t.size ≤ n) → c ∈ fin S := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c hsub hfin hbound
    apply saturate.closed
    simp only [growFin, Finset.mem_inter, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨⟨hsub, fun hr => restOK_infinite hr hfin, ?_⟩, hsub⟩
    rintro ⟨f, k⟩ - hl i hi
    obtain ⟨w, hw⟩ := hl.fn
    let g : GTerm → GTerm := fun u => Term.mk f (List.ofFn (update w ⟨i, hi⟩ u))
    have hg : ∀ u, MemC S (kidC S c f k i) u → MemC S c (g u) := by
      intro u hu
      refine memC_ofFn hl.1 fun j => ?_
      by_cases hj : j = ⟨i, hi⟩
      · subst hj; simpa using hu
      · rw [update_of_ne hj]; exact hw j
    have ginj : Injective g := by
      intro u₁ u₂ e
      have := congrFun (List.ofFn_injective (Term.mk_inj e).2) ⟨i, hi⟩
      simpa using this
    have hlt : ∀ u, u.size < (g u).size := fun u =>
      size_lt_mk (by
        rw [List.mem_ofFn]
        exact ⟨(⟨i, hi⟩ : Fin k), by simp⟩)
    have hpos : 0 < n := by
      have := hbound _ (hg (w ⟨i, hi⟩) (hw ⟨i, hi⟩))
      have := hlt (w ⟨i, hi⟩)
      omega
    refine ih (n - 1) (by omega) _ kidC_subset_names ?_ ?_
    · exact (hfin.preimage (f := g) fun a _ b _ e => ginj e).subset fun u hu => hg u hu
    · intro u hu
      have := hbound _ (hg u hu)
      have := hlt u
      omega

theorem mem_fin_iff {c : Conj} (hsub : c ⊆ names S) : c ∈ fin S ↔ {t | MemC S c t}.Finite := by
  constructor
  · exact finite_of_mem_fin c
  · intro hfin
    obtain ⟨n, hn⟩ := (hfin.image Term.size).bddAbove
    exact mem_fin_of_finite n c hsub hfin fun t ht => hn ⟨t, ht, rfl⟩

/-! ## The decision -/

/-- Sorts are well formed exactly when no conjunction of declared sorts has
two different members and finitely many. -/
theorem wellFormed_iff : S.WellFormed ↔ (big S ∩ fin S) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  simp only [Finset.mem_inter, not_and]
  have set_eq : ∀ ns : List Name,
      {t : GTerm | ∀ n ∈ ns, S.Mem n t} = {t | MemC S ns.toFinset t} := by
    intro ns; ext t
    simp only [Set.mem_ofPred_eq, memC_iff_Mem, List.mem_toFinset]
  constructor
  · intro h c hc hf
    obtain ⟨t₁, t₂, hne, h₁, h₂⟩ := mem_big_iff.1 hc
    have hfin := (mem_fin_iff (subset_names_of_memC h₁)).1 hf
    have e : c.toList.toFinset = c := Finset.toList_toFinset c
    rcases h c.toList with he | ⟨t, ht⟩ | hi
    · rw [set_eq, e] at he
      have : t₁ ∈ {t | MemC S c t} := h₁
      rw [he] at this; exact this
    · rw [set_eq, e] at ht
      have m₁ : t₁ ∈ {t | MemC S c t} := h₁
      have m₂ : t₂ ∈ {t | MemC S c t} := h₂
      rw [ht] at m₁ m₂
      exact hne (m₁.trans m₂.symm)
    · rw [set_eq, e] at hi
      exact hi hfin
  · intro h ns
    rw [set_eq]
    by_cases hemp : ∃ t, MemC S ns.toFinset t
    · obtain ⟨t, ht⟩ := hemp
      by_cases hone : ∀ t', MemC S ns.toFinset t' → t' = t
      · right; left
        exact ⟨t, Set.eq_singleton_iff_unique_mem.2 ⟨ht, hone⟩⟩
      · right; right
        simp only [not_forall] at hone
        obtain ⟨t', ht', hne⟩ := hone
        intro hfin
        exact h _ (mem_big_iff.2 ⟨t', t, hne, ht', ht⟩)
          ((mem_fin_iff (subset_names_of_memC ht)).2 hfin)
    · left
      exact Set.eq_empty_of_forall_notMem fun t ht => hemp ⟨t, ht⟩

instance (S : Sorts) : Decidable S.WellFormed := decidable_of_iff _ wellFormed_iff.symm

end Sorts

/-- L56. Whether a program with a query is well formed is decidable. -/
instance (P : Program) (q : Rel) : Decidable (P.WellFormed q) := by
  unfold ProgramOf.WellFormed; infer_instance

/-- The check made when a program is read. -/
def ProgramOf.check (P : Program) (q : Rel) : Bool := decide (P.WellFormed q)

/-- The check is exact. -/
theorem ProgramOf.check_iff (P : Program) (q : Rel) : P.check q = true ↔ P.WellFormed q := by
  simp [ProgramOf.check]

end RwLog
