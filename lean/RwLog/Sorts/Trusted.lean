/-
# The computed membership is the trusted one

`Sorts.Mem` (`Trusted/Semantics.lean`) says which ground terms belong to a
sort. `Sorts.mem` (`Sorts/Decl.lean`) computes it. They agree, so every fact
proved about `mem` (emptiness, inclusion) is a fact about the sorts of the
language.
-/
import RwLog.Sorts.Conj

namespace RwLog
namespace Sorts

theorem _root_.RwLog.SortDef.step_of_caseOf_some {d : SortDef} {f : Sym} {n : Nat}
    {as : List (Option Name)} (h : d.caseOf f n = some as) : d.step f n = some as := by
  unfold SortDef.caseOf at h
  unfold SortDef.step
  cases hf : d.cases.find? (fun c => c.1 = f ∧ c.2.length = n) with
  | none => rw [hf] at h; cases h
  | some c => rw [hf] at h; simp only [Option.map_some, Option.some.injEq] at h; simp [h]

theorem _root_.RwLog.SortDef.step_of_caseOf_none {d : SortDef} {f : Sym} {n : Nat}
    (h : d.caseOf f n = none) :
    d.step f n = match d.rest with
      | some (ex, k) => if (f, n) ∈ ex then none else some (List.replicate n k)
      | none => none := by
  unfold SortDef.caseOf at h
  unfold SortDef.step
  cases hf : d.cases.find? (fun c => c.1 = f ∧ c.2.length = n) with
  | none => rfl
  | some c => rw [hf] at h; cases h

theorem mem_of_Mem {S : Sorts} {n : Name} {t : GTerm} (h : S.Mem n t) : mem S n t = true := by
  induction h with
  | @case n d t f ts as hd hsp hc _ ih =>
    obtain ⟨f', ts', rfl, -⟩ := exists_mk t
    rw [Term.spine_mk] at hsp
    obtain ⟨rfl, rfl⟩ : f' = f ∧ ts' = ts := by simpa using hsp
    refine mem_mk.2 ⟨as, by simp [step, hd, SortDef.step_of_caseOf_some hc], ?_⟩
    intro i hi
    cases ha : as[i]? with
    | none => rfl
    | some o =>
      cases o with
      | none => rfl
      | some m => exact ih i m ts'[i] ha (List.getElem?_eq_getElem hi)
  | @rest n d t f ts ex a hd hsp hc hr hex _ ih =>
    obtain ⟨f', ts', rfl, -⟩ := exists_mk t
    rw [Term.spine_mk] at hsp
    obtain ⟨rfl, rfl⟩ : f' = f ∧ ts' = ts := by simpa using hsp
    refine mem_mk.2 ⟨List.replicate ts'.length a, ?_, ?_⟩
    · simp [step, hd, SortDef.step_of_caseOf_none hc, hr, hex]
    · intro i hi
      simp only [List.getElem?_replicate, hi, ite_true, Option.getD_some]
      cases a with
      | none => rfl
      | some m => exact ih m ts'[i] rfl (List.getElem_mem hi)

theorem Mem_of_mem {S : Sorts} : ∀ (k : Nat) (t : GTerm) (n : Name), t.size ≤ k →
    mem S n t = true → S.Mem n t := by
  intro k
  induction k with
  | zero => intro t n hk; cases t <;> simp [Term.size] at hk
  | succ k ih =>
    intro t n hk h
    obtain ⟨f, ts, rfl, hsz⟩ := exists_mk t
    obtain ⟨ks, hstep, hargs⟩ := mem_mk.1 h
    unfold step at hstep
    cases hd : S.lookup n with
    | none => simp [hd] at hstep
    | some d =>
      simp only [hd, Option.bind_some] at hstep
      have hmem : ∀ (i : Nat) (hi : i < ts.length) (m : Name), ks[i]? = some (some m) →
          S.Mem m ts[i] := by
        intro i hi m hm
        have := hargs i hi
        simp only [hm, Option.getD_some, memO] at this
        exact ih _ _ (by have := hsz _ (List.getElem_mem hi); omega) this
      cases hc : d.caseOf f ts.length with
      | some as =>
        rw [SortDef.step_of_caseOf_some hc] at hstep
        cases hstep
        refine Sorts.Mem.case hd (Term.spine_mk f ts) hc ?_
        intro i m u hm hu
        obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 hu
        exact hmem i hi m hm
      | none =>
        rw [SortDef.step_of_caseOf_none hc] at hstep
        cases hr : d.rest with
        | none => simp [hr] at hstep
        | some p =>
          obtain ⟨ex, a⟩ := p
          simp only [hr] at hstep
          by_cases hex : (f, ts.length) ∈ ex
          · simp [hex] at hstep
          · simp only [hex, ite_false, Option.some.injEq] at hstep
            subst hstep
            refine Sorts.Mem.rest hd (Term.spine_mk f ts) hc hr hex ?_
            intro m u ha hu
            obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hu
            exact hmem i hi m (by simp [hi, ha])

/-- The computed membership decides the trusted one. -/
theorem mem_iff_Mem {S : Sorts} {n : Name} {t : GTerm} : mem S n t = true ↔ S.Mem n t :=
  ⟨Mem_of_mem _ t n le_rfl, mem_of_Mem⟩

instance (S : Sorts) (n : Name) (t : GTerm) : Decidable (S.Mem n t) :=
  decidable_of_iff _ mem_iff_Mem

/-- A conjunction of sorts holds of a term exactly when the term belongs to
each of them. -/
theorem memC_iff_Mem {S : Sorts} {c : Conj} {t : GTerm} : MemC S c t ↔ ∀ n ∈ c, S.Mem n t := by
  simp only [MemC, mem_iff_Mem]

end Sorts
end RwLog
