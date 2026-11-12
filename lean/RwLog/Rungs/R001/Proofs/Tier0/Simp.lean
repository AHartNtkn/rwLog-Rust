/-
# Tier 0 proofs, part 0: what refutation and simplification keep

* A store contained in another (as a multiset) is refuted only if the larger
  one is (`refutes_subperm`). Every match on the smaller store is a match on
  the larger one, with the same equations, and a firing that lowers the
  smaller store's weight lowers the larger one's too: the atoms only the
  larger store holds either stay beside the successor or are removed with the
  matched ones. This keeps the interfaces of an unrefuted answer unrefuted
  (`prompt_pruning`).
* Simplifying a span instantiates its two sides, so every pair of terms the
  result relates (whatever its store) the original relates too
  (`simplify_pairs`).
-/
import RwLog.Rungs.R001.Proofs.Kernel
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace RwLog

namespace R001

namespace Tier0

theorem nodup_eraseDups {α : Type} [BEq α] [LawfulBEq α] (l : List α) : l.eraseDups.Nodup := by
  induction h : l.length using Nat.strong_induction_on generalizing l with
  | _ n ih =>
  cases l with
  | nil => simp
  | cons a as =>
    rw [List.eraseDups_cons]
    refine List.nodup_cons.2 ⟨by simp, ih _ ?_ _ rfl⟩
    have := List.length_filter_le (fun b => !b == a) as
    simp only [List.length_cons] at h
    omega

theorem matchAll_mono {ts ts' : List Pat} (hs : ∀ t ∈ ts, t ∈ ts') :
    ∀ (ps : List Pat) (θ : PSubst) (r : PSubst × List Pat),
      r ∈ matchAll ps ts θ → r ∈ matchAll ps ts' θ
  | [], θ, r, h => by simpa [matchAll] using h
  | p :: ps, θ, r, h => by
    simp only [matchAll, List.mem_flatMap] at h ⊢
    obtain ⟨t, ht, hr⟩ := h
    refine ⟨t, hs t ht, ?_⟩
    cases h₁ : matchInto p t θ with
    | none => rw [h₁] at hr; simp at hr
    | some θ₁ =>
      rw [h₁] at hr
      simp only [List.mem_map] at hr ⊢
      obtain ⟨r', hr', rfl⟩ := hr
      exact ⟨r', matchAll_mono hs ps θ₁ r' hr', rfl⟩

/-- The weight of a store, as a multiset. -/
theorem storeWeight_coe (T : Theory) (c : Store) :
    T.storeWeight c = ((c : Multiset Pat).map fun a => T.base ^ a.size).sum := by
  simp [Theory.storeWeight]

/-- Summing over the distinct members never exceeds summing over all of them. -/
theorem sum_toFinset_le (f : Pat → Nat) (s : Multiset Pat) :
    ∑ x ∈ s.toFinset, f x ≤ (s.map f).sum := by
  rw [Finset.sum_multiset_map_count]
  refine Finset.sum_le_sum fun x hx => ?_
  have : 1 ≤ s.count x := Multiset.count_pos.2 (Multiset.mem_toFinset.1 hx)
  calc f x = 1 • f x := (one_nsmul _).symm
    _ ≤ s.count x • f x := Nat.mul_le_mul_right _ this

/-- The weight of a deduplicated list is the sum over its distinct members. -/
theorem storeWeight_eraseDups (T : Theory) (l : Store) :
    T.storeWeight l.eraseDups = ∑ x ∈ (l : Multiset Pat).toFinset, T.base ^ x.size := by
  rw [Theory.storeWeight, ← List.sum_toFinset _ (nodup_eraseDups l)]
  congr 1
  ext x
  simp

/-- Replacing the same atoms in a larger store lowers its weight whenever it
lowers the smaller store's, and keeps the successors in the same relation. -/
theorem replace_mono (T : Theory) {c' c : Store} (h : c'.Subperm c) (ms bs : Store)
    (hw : T.storeWeight (c'.replace ms bs) < T.storeWeight c') :
    T.storeWeight (c.replace ms bs) < T.storeWeight c ∧
      (c'.replace ms bs).Subperm (c.replace ms bs) := by
  set w : Pat → Nat := fun a => T.base ^ a.size
  set p : Pat → Bool := fun a => !ms.contains a
  obtain ⟨D, hD⟩ := Multiset.le_iff_exists_add.1 (Multiset.coe_le.2 h)
  have hF : ((c.filter p : List Pat) : Multiset Pat) =
      ((c'.filter p : List Pat) : Multiset Pat) + D.filter (p · = true) := by
    have := congrArg (Multiset.filter (p · = true)) hD
    simpa [Multiset.filter_add] using this
  have hW : T.storeWeight c = T.storeWeight c' + ((D.filter (p · = true)).map w).sum +
      ((D.filter fun a => ¬ p a = true).map w).sum := by
    have e1 : (D.map w).sum = ((D.filter (p · = true)).map w).sum +
        ((D.filter fun a => ¬ p a = true).map w).sum := by
      rw [← Multiset.sum_add, ← Multiset.map_add, Multiset.filter_add_not]
    rw [storeWeight_coe, storeWeight_coe, hD, Multiset.map_add, Multiset.sum_add, add_assoc, ← e1]
  refine ⟨?_, ?_⟩
  · have hle : T.storeWeight (c.replace ms bs) ≤
        T.storeWeight (c'.replace ms bs) + ((D.filter (p · = true)).map w).sum := by
      simp only [Store.replace]
      rw [storeWeight_eraseDups, storeWeight_eraseDups, ← Multiset.coe_add, ← Multiset.coe_add,
        hF, add_comm _ (D.filter (p · = true)), add_assoc, Multiset.toFinset_add]
      calc ∑ x ∈ (D.filter (p · = true)).toFinset ∪ (↑(c'.filter p) + ↑bs : Multiset Pat).toFinset,
            T.base ^ x.size
          ≤ ∑ x ∈ (D.filter (p · = true)).toFinset, T.base ^ x.size +
              ∑ x ∈ (↑(c'.filter p) + ↑bs : Multiset Pat).toFinset, T.base ^ x.size :=
            Nat.le_of_add_right_le (Finset.sum_union_inter).le
        _ ≤ ((D.filter (p · = true)).map w).sum +
              ∑ x ∈ (↑(c'.filter p) + ↑bs : Multiset Pat).toFinset, T.base ^ x.size :=
            Nat.add_le_add_right (sum_toFinset_le w _) _
        _ = _ := Nat.add_comm _ _
    omega
  · simp only [Store.replace]
    refine (nodup_eraseDups _).subperm fun x hx => ?_
    simp only [List.mem_eraseDups, List.mem_append, List.mem_filter] at hx ⊢
    rcases hx with ⟨hx, hp⟩ | hx
    · exact Or.inl ⟨h.subset hx, hp⟩
    · exact Or.inr hx

/-- Refuting a store refutes every store that contains it (as a multiset). -/
theorem refutes_subperm (T : Theory) : ∀ (n : Nat) (c' c : Store), T.storeWeight c' = n →
    c'.Subperm c → T.refutes? c' = true → T.refutes? c = true := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro c' c hn hsub h
  rw [Theory.refutes?] at h ⊢
  simp only [List.any_eq_true] at h ⊢
  obtain ⟨ρ, hρ, f, hf, hF⟩ := h
  refine ⟨ρ, hρ, ?_⟩
  simp only [TRule.firings, List.mem_map] at hf ⊢
  obtain ⟨r, hr, rfl⟩ := hf
  have hr' := matchAll_mono (fun a ha => hsub.subset ha) _ _ _ hr
  cases hb : ρ.body with
  | fail => exact ⟨_, ⟨r, hr', rfl⟩, rfl⟩
  | conj eqs cs =>
    refine ⟨_, ⟨r, hr', rfl⟩, ?_⟩
    rw [hb] at hF
    simp only [firingOfEqs] at hF ⊢
    by_cases hd : ρ.decreasing = true
    · split_ifs at hF ⊢
      · dsimp only at hF ⊢
        split_ifs at hF with hw
        obtain ⟨hw', hs'⟩ := replace_mono T hsub r.2 (cs.map (Term.bind r.1.apply)) hw
        simp only [hw', ↓reduceIte]
        exact ih _ (hn ▸ hw) _ _ rfl hs' hF
      · cases hs : solve (eqs.map fun e => (e.1.bind r.1.apply, e.2.bind r.1.apply)) <;>
          simp only [hs] at hF ⊢
        exact absurd hF Bool.false_ne_true
    · split_ifs at hF ⊢
      cases hs : solve (eqs.map fun e => (e.1.bind r.1.apply, e.2.bind r.1.apply)) <;>
        simp only [hs] at hF ⊢
      exact absurd hF Bool.false_ne_true

/-- The store of an interface of an unrefuted span is unrefuted. -/
theorem storeOn_unref {T : Theory} {x : Span} (hx : T.refutes? x.c = false) (p : Pat) :
    T.refutes? (x.storeOn p) = false := by
  cases h : T.refutes? (x.storeOn p)
  · rfl
  · rw [← hx]
    exact (refutes_subperm T _ _ _ rfl (List.filter_sublist).subperm h).symm

theorem simplifyWithin_inst (T : Theory) : ∀ (n : Nat) (s s' : Span),
    T.simplifyWithin n s = some s' → ∃ θ : Nat → Pat, s'.l = s.l.bind θ ∧ s'.r = s.r.bind θ
  | n, s, s', h => by
    unfold Theory.simplifyWithin at h
    split at h
    · simp at h
    · split at h
      · rename_i m θ _
        obtain ⟨θ', h1, h2⟩ := simplifyWithin_inst T m _ _ h
        exact ⟨fun v => (θ v).bind θ', by rw [h1]; simp [Span.inst], by rw [h2]; simp [Span.inst]⟩
      · simp only [Option.some.injEq] at h
        subst h
        exact ⟨Term.var, by simp [Term.bind_var_id], by simp [Term.bind_var_id]⟩

/-- Every pair a simplified span relates, the original relates too. -/
theorem simplify_pairs {T : Theory} {s s' : Span} (h : T.simplify s = some s') :
    s'.den.at Set.univ ⊆ s.den.at Set.univ := by
  obtain ⟨θ, h1, h2⟩ := simplifyWithin_inst T _ _ _ h
  rintro ⟨u, v⟩ ⟨S, ⟨σ, hx⟩, -⟩
  simp only [Prod.mk.injEq] at hx
  obtain ⟨rfl, rfl, -⟩ := hx
  refine ⟨s.c.at fun w => (θ w).bind σ, ⟨fun w => (θ w).bind σ, ?_⟩, Set.subset_univ _⟩
  simp only [h1, h2, Term.bind_bind]

end Tier0

end R001

end RwLog
