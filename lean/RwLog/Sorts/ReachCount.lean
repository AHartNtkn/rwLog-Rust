/-
# Counting on the conjunctions a conjunction reaches

`count S c` looks as deep as there are sets of names. To find the one member
of a conjunction `c` it is enough to look at the conjunctions `c` reaches
(`Reach`): `one_of_stable` says that on a set of conjunctions closed under
reaching, a table of members that only holds the one member of a conjunction
and that no round extends holds the member of every conjunction of the set
that has just one, and `count_one_iff_of_stable` says so for the conjunctions
one conjunction reaches.
-/
import RwLog.Sorts.Count
import RwLog.Sorts.Reach

namespace RwLog
namespace Sorts

variable {S : Sorts}

/-- What a round asks of a conjunction for `t` to be its one member, given the
members in `M`: not every sort of it has a rest, the roots of its members are
one root, and `M` has a member for each argument of that root. -/
def OneStep (S : Sorts) (M : Conj → Option GTerm) (c : Conj) (t : GTerm) : Prop :=
  ¬ RestOK S c ∧ ∃ f ts, liveKeys S c = {(f, ts.length)} ∧
    (∀ i (h : i < ts.length), M (kidC S c f ts.length i) = some ts[i]) ∧ t = Term.mk f ts

/-- `M` only has the one member of a conjunction. -/
def OneSound (S : Sorts) (M : Conj → Option GTerm) : Prop :=
  ∀ c t, M c = some t → MemC S c t ∧ ∀ u, MemC S c u → u = t

/-- What a round adds to a table of one members is a one member. -/
theorem OneStep.sound {M : Conj → Option GTerm} (hM : OneSound S M) {c : Conj} {t : GTerm}
    (h : OneStep S M c t) : MemC S c t ∧ ∀ u, MemC S c u → u = t := by
  obtain ⟨hr, f, ts, hk, hts, rfl⟩ := h
  have hmem : (f, ts.length) ∈ liveKeys S c := by rw [hk]; exact Finset.mem_singleton_self _
  refine ⟨memC_mk.2 ⟨(Finset.mem_filter.1 hmem).2.1, fun i hi => (hM _ _ (hts i hi)).1⟩, ?_⟩
  intro u hu
  obtain ⟨g, us, rfl, -⟩ := exists_mk u
  have := mem_liveKeys_of_memC hr hu
  rw [hk, Finset.mem_singleton, Prod.mk.injEq] at this
  obtain ⟨rfl, hl⟩ := this
  congr 1
  refine List.ext_getElem hl fun i h₁ h₂ => ?_
  have := (memC_mk.1 hu).2 i h₁
  rw [hl] at this
  exact (hM _ _ (hts i h₂)).2 _ this

/-- On a set of conjunctions closed under reaching, a table that only has
one members and that no round extends has the member of every conjunction of
the set with just one. -/
theorem one_of_stable {R : Conj → Prop} {M : Conj → Option GTerm}
    (hclosed : ∀ c d, R c → Kid S c d → R d) (hM : OneSound S M)
    (hstable : ∀ c t, R c → OneStep S M c t → (M c).isSome = true) :
    ∀ (t : GTerm) (c : Conj), R c → MemC S c t → (∀ u, MemC S c u → u = t) → M c = some t := by
  intro t
  induction h : t.size using Nat.strong_induction_on generalizing t with
  | _ m ih =>
    intro c hc ht hu
    obtain ⟨f, ts, rfl, hsz⟩ := exists_mk t
    have hr : ¬ RestOK S c := fun hr =>
      restOK_infinite hr ((Set.finite_singleton (Term.mk f ts)).subset fun u hu' => hu u hu')
    have hkey := mem_liveKeys_of_memC hr ht
    have hone : liveKeys S c = {(f, ts.length)} := by
      refine Finset.eq_singleton_iff_unique_mem.2 ⟨hkey, ?_⟩
      rintro ⟨g, k⟩ hg
      have hl := (Finset.mem_filter.1 hg).2
      obtain ⟨w, hw⟩ := hl.fn
      obtain ⟨rfl, e⟩ := Term.mk_inj (hu _ (memC_ofFn hl.1 hw))
      have : k = ts.length := by simpa using congrArg List.length e
      rw [this]
    have hkids : ∀ i (hi : i < ts.length), M (kidC S c f ts.length i) = some ts[i] := by
      intro i hi
      refine ih _ (by subst h; exact hsz _ (List.getElem_mem hi)) ts[i] rfl _
        (hclosed c _ hc ⟨hr, (f, ts.length), (Finset.mem_filter.1 hkey).1,
          (Finset.mem_filter.1 hkey).2.1, i, hi, rfl⟩)
        ((memC_mk.1 ht).2 i hi) ?_
      intro u hu'
      have hmem : MemC S c (Term.mk f (ts.set i u)) := by
        refine memC_mk.2 ⟨by simpa using (memC_mk.1 ht).1, fun j hj => ?_⟩
        simp only [List.length_set] at hj ⊢
        by_cases e : i = j
        · subst e; simpa using hu'
        · simpa [List.getElem_set_of_ne e] using (memC_mk.1 ht).2 j hj
      have e := (Term.mk_inj (hu _ hmem)).2
      have := congrArg (fun l => l[i]?) e
      simpa [hi] using this
    obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.1
      (hstable c _ hc ⟨hr, f, ts, hone, hkids, rfl⟩)
    rw [ht', hu _ (hM _ _ ht').1]

/-- The same, for the conjunctions one conjunction reaches: the table has
`t` for `c₀` exactly when `t` is the one member of `c₀`. -/
theorem count_one_iff_of_stable {c₀ : Conj} {M : Conj → Option GTerm} (hM : OneSound S M)
    (hstable : ∀ c t, Reach S c₀ c → OneStep S M c t → (M c).isSome = true) (t : GTerm) :
    M c₀ = some t ↔ count S c₀ = .one t := by
  rw [count_one]
  exact ⟨hM c₀ t, fun ⟨ht, hu⟩ =>
    one_of_stable (R := Reach S c₀) (fun _ _ h k => h.step k) hM hstable t c₀ .refl ht hu⟩

/-- When the table has nothing for `c₀`, `c₀` has no member or more than
one. -/
theorem count_ne_one_of_stable {c₀ : Conj} {M : Conj → Option GTerm} (hM : OneSound S M)
    (hstable : ∀ c t, Reach S c₀ c → OneStep S M c t → (M c).isSome = true)
    (h : M c₀ = none) : count S c₀ = (if c₀ ∈ live S then .many else .none) := by
  split
  · rename_i hl
    cases hc : count S c₀ with
    | none => exact absurd (mem_live_iff.1 hl) (count_none.1 hc)
    | one t => rw [(count_one_iff_of_stable hM hstable t).2 hc] at h; cases h
    | many => rfl
  · rename_i hl
    exact count_none.2 fun hm => hl (mem_live_iff.2 hm)

end Sorts
end RwLog
