/-
# The roots of the values of a variable

A variable of sorts `c` that is excluded from each term of a list `G` takes
the members of `c` that are not in `G`. `sole S c G` is the root of all of
them when they have one root (`sole_sound`), and when it finds none, either
there is no such value or two of them have different roots (`sole_none`, for
well-formed sorts). A variable whose values have one root is replaced by that
root applied to new variables, so this is the test that a store is tight.
-/
import RwLog.Sorts.InclBut

namespace RwLog
namespace Sorts

open Function

variable {S : Sorts}

/-- The roots the declarations of `c` name, or a term of `G` has, of a member
of `c` that is not in `G`. -/
def survivors (S : Sorts) (c : Conj) (G : List GTerm) : Finset (Sym × Nat) :=
  let L := live S
  (caseKeys S c ∪ (G.filterMap Term.key).toFinset).filter fun key =>
    LiveKey S L c key ∧ onlyIn S c key.1 key.2 G = false

/-- The one root of the members of `c` that are not in `G`. -/
def sole (S : Sorts) (c : Conj) (G : List GTerm) : Option (Sym × Nat) :=
  if RestOK S c then none else only (survivors S c G)

/-- When not every sort of `c` has a rest, the root of a member that is not
in `G` is among the survivors. -/
theorem mem_survivors {c : Conj} {G : List GTerm} (hr : ¬ RestOK S c) {f : Sym}
    {ts : List GTerm} (ht : MemC S c (Term.mk f ts)) (hG : Term.mk f ts ∉ G) :
    (f, ts.length) ∈ survivors S c G := by
  simp only [survivors, Finset.mem_filter, Finset.mem_union]
  refine ⟨Or.inl (Finset.mem_filter.1 (mem_liveKeys_of_memC hr ht)).1, liveKey_of_memC ht, ?_⟩
  by_contra h
  rw [Bool.not_eq_false, onlyIn_iff] at h
  obtain ⟨args, hmem, hlen, hones⟩ := h
  have : ts = args := by
    refine List.ext_getElem hlen.symm fun j h1 h2 => ?_
    have := hones j h2 (by simp)
    rw [hlen] at this
    exact (count_one.1 this).2 _ ((memC_mk.1 ht).2 j h1)
  exact hG (this ▸ hmem)

/-- A surviving root is the root of a member that is not in `G`. -/
theorem exists_of_survivor (hS : S.WellFormed) {c : Conj} {G : List GTerm} {key : Sym × Nat}
    (h : key ∈ survivors S c G) :
    ∃ ts, ts.length = key.2 ∧ MemC S c (Term.mk key.1 ts) ∧ Term.mk key.1 ts ∉ G := by
  obtain ⟨f, k⟩ := key
  simp only [survivors, Finset.mem_filter] at h
  obtain ⟨-, hl, hno⟩ := h
  obtain ⟨w, hw⟩ := hl.fn
  by_cases hone : ∀ j : Fin k, count S (kidC S c f k j) = .one (w j)
  · refine ⟨List.ofFn w, by simp, memC_ofFn hl.1 hw, fun hG => ?_⟩
    have : onlyIn S c f k G = true := onlyIn_iff.2 ⟨List.ofFn w, hG, by simp, by
      intro j hj _
      simp only [List.length_ofFn] at hj ⊢
      simpa using hone ⟨j, hj⟩⟩
    rw [this] at hno; cases hno
  · push Not at hone
    obtain ⟨j, hj⟩ := hone
    have hinf : {u | MemC S (kidC S c f k j) u}.Infinite := by
      cases hc : count S (kidC S c f k j) with
      | none => exact absurd ⟨_, hw j⟩ (count_none.1 hc)
      | one v =>
        rw [← (count_one.1 hc).2 _ (hw j)] at hc
        exact absurd hc hj
      | many => exact count_many_infinite hS hc
    obtain ⟨u, hu, hnot⟩ := exists_avoid hinf G _ (ofFn_update_injective f w j)
    exact ⟨_, by simp, memC_ofFn hl.1 (memC_update hw j hu), hnot⟩

/-- Every value has the root `sole` finds. -/
theorem sole_sound {c : Conj} {G : List GTerm} {key : Sym × Nat} (h : sole S c G = some key)
    {t : GTerm} (ht : MemC S c t) (hG : t ∉ G) : t.key = some key := by
  unfold sole at h
  split at h
  · cases h
  · rename_i hr
    obtain ⟨f, ts, rfl, -⟩ := exists_mk t
    have := mem_survivors hr ht hG
    rw [only_eq_some.1 h, Finset.mem_singleton] at this
    simp [Term.key, Term.spine_mk, this]

/-- When `sole` finds no root and there is a value, two values have different
roots. -/
theorem sole_none (hS : S.WellFormed) {c : Conj} {G : List GTerm} (h : sole S c G = none)
    {t : GTerm} (ht : MemC S c t) (hG : t ∉ G) :
    ∃ t₁ t₂, MemC S c t₁ ∧ t₁ ∉ G ∧ MemC S c t₂ ∧ t₂ ∉ G ∧ t₁.key ≠ t₂.key := by
  unfold sole at h
  split at h
  · rename_i hr
    let bad : Finset Sym := usedSyms S ∪ ((G.filterMap Term.key).toFinset.image Prod.fst)
    have fresh : ∀ g, g ∉ bad → MemC S c (Term.mk g []) ∧ Term.mk g [] ∉ G := by
      intro g hg
      simp only [bad, Finset.mem_union, not_or] at hg
      refine ⟨restOK_fresh hr hg.1, fun hm => hg.2 ?_⟩
      rw [Finset.mem_image]
      refine ⟨(g, 0), ?_, rfl⟩
      rw [List.mem_toFinset, List.mem_filterMap]
      exact ⟨_, hm, by simp [Term.key, Term.spine_mk]⟩
    obtain ⟨g₁, hg₁⟩ := Infinite.exists_notMem_finset bad
    obtain ⟨g₂, hg₂⟩ := Infinite.exists_notMem_finset (insert g₁ bad)
    simp only [Finset.mem_insert, not_or] at hg₂
    refine ⟨_, _, (fresh g₁ hg₁).1, (fresh g₁ hg₁).2, (fresh g₂ hg₂.2).1, (fresh g₂ hg₂.2).2, ?_⟩
    simp only [Term.key, Term.spine_mk, Option.map_some, List.length_nil, ne_eq,
      Option.some.injEq, Prod.mk.injEq, and_true]
    exact fun e => hg₂.1 e.symm
  · rename_i hr
    obtain ⟨f, ts, rfl, -⟩ := exists_mk t
    have hmem := mem_survivors hr ht hG
    have : ∃ key ∈ survivors S c G, key ≠ (f, ts.length) := by
      by_contra hno
      push Not at hno
      have : survivors S c G = {(f, ts.length)} :=
        Finset.eq_singleton_iff_unique_mem.2 ⟨hmem, hno⟩
      rw [only_eq_some.2 this] at h; cases h
    obtain ⟨key, hkey, hne⟩ := this
    obtain ⟨us, hlen, hu, huG⟩ := exists_of_survivor hS hkey
    refine ⟨_, _, ht, hG, hu, huG, ?_⟩
    simp only [Term.key, Term.spine_mk, Option.map_some, ne_eq, Option.some.injEq, hlen]
    exact fun e => hne e.symm

end Sorts
end RwLog
