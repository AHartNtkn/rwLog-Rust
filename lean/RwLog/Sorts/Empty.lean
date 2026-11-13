/-
# Emptiness of a conjunction of sorts

`live S` is the set of conjunctions of the names of `S` that have a member.
It is computed by saturation: a conjunction has a member when every sort in it
has a rest (then a symbol no declaration mentions is a member), or when some
root symbol that one of its sorts has a case for is accepted by all of them
with every argument position already known to have a member.
-/
import RwLog.Sorts.Conj
import RwLog.Lib.Saturate
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.String.Basic

namespace RwLog
namespace Sorts

/-- The sorts a declaration names for arguments. -/
def _root_.RwLog.SortDef.kidNames (d : SortDef) : List Name :=
  d.cases.flatMap (fun c => c.2.filterMap id) ++ (d.rest.bind (·.2)).toList

/-- Every name declared or mentioned. -/
def names (S : Sorts) : Finset Name := (S.flatMap fun p => p.1 :: p.2.kidNames).toFinset

/-- The roots some sort of `c` has a case for. -/
def caseKeys (S : Sorts) (c : Conj) : Finset (Sym × Nat) :=
  c.biUnion fun n =>
    match S.lookup n with
    | some d => (d.cases.map fun cs => (cs.1, cs.2.length)).toFinset
    | none => ∅

/-- Every sort of `c` is declared and has a rest. -/
def RestOK (S : Sorts) (c : Conj) : Prop :=
  ∀ n ∈ c, ((S.lookup n).bind (·.rest)).isSome = true

instance (S : Sorts) (c : Conj) : Decidable (RestOK S c) := by unfold RestOK; infer_instance

/-- One round: the conjunctions that have a member given that those in `P` do. -/
def grow (S : Sorts) (P : Finset Conj) : Finset Conj :=
  (names S).powerset.filter fun c =>
    RestOK S c ∨ ∃ key ∈ caseKeys S c,
      Accepts S c key.1 key.2 ∧ ∀ i < key.2, kidC S c key.1 key.2 i ∈ P

/-- The conjunctions that have a member. -/
def live (S : Sorts) : Finset Conj := saturate (names S).powerset (grow S)

theorem mem_of_lookup {α β : Type} [BEq α] [LawfulBEq α] {l : List (α × β)} {a : α} {b : β}
    (h : l.lookup a = some b) : (a, b) ∈ l := by
  induction l with
  | nil => simp at h
  | cons p l ih =>
    obtain ⟨a', b'⟩ := p
    simp only [List.lookup_cons] at h
    split at h
    · rename_i heq
      have : a = a' := by simpa using heq
      cases h; subst this; simp
    · exact List.mem_cons_of_mem _ (ih h)

/-- What `step` returns, case by case. -/
theorem step_cases {S : Sorts} {n : Name} {f : Sym} {k : Nat} {ks : List (Option Name)}
    (h : step S n f k = some ks) :
    ∃ d, S.lookup n = some d ∧
      ((∃ cs ∈ d.cases, cs.1 = f ∧ cs.2.length = k ∧ ks = cs.2) ∨
       ((∀ cs ∈ d.cases, ¬ (cs.1 = f ∧ cs.2.length = k)) ∧
          ∃ ex r, d.rest = some (ex, r) ∧ (f, k) ∉ ex ∧ ks = List.replicate k r)) := by
  unfold step at h
  cases hd : S.lookup n with
  | none => simp [hd] at h
  | some d =>
    refine ⟨d, rfl, ?_⟩
    simp only [hd, Option.bind_some] at h
    unfold SortDef.step at h
    split at h
    · rename_i cs hc
      have h1 := List.mem_of_find?_eq_some hc
      have h2 := List.find?_some hc
      simp only [decide_eq_true_eq] at h2
      cases h
      exact Or.inl ⟨cs, h1, h2.1, h2.2, rfl⟩
    · rename_i hc
      rw [List.find?_eq_none] at hc
      right
      refine ⟨fun cs hcs => by simpa using hc cs hcs, ?_⟩
      split at h
      · rename_i ex r hr
        split at h
        · cases h
        · rename_i hex; cases h; exact ⟨ex, r, hr, hex, rfl⟩
      · cases h

theorem kidC_subset_names {S : Sorts} {c : Conj} {f : Sym} {k i : Nat} :
    kidC S c f k i ⊆ names S := by
  intro m hm
  obtain ⟨n, _, ks, hs, hg⟩ := mem_kidC.mp hm
  obtain ⟨d, hd, hcase⟩ := step_cases hs
  have hmem := mem_of_lookup hd
  simp only [names, List.mem_toFinset, List.mem_flatMap]
  refine ⟨(n, d), hmem, List.mem_cons_of_mem _ ?_⟩
  simp only [SortDef.kidNames, List.mem_append, List.mem_flatMap, List.mem_filterMap, id]
  rcases hcase with ⟨cs, hcs, _, _, rfl⟩ | ⟨_, ex, r, hr, _, rfl⟩
  · exact Or.inl ⟨cs, hcs, some m, List.mem_of_getElem? hg, rfl⟩
  · right
    have : r = some m := by
      have := List.mem_of_getElem? hg
      rw [List.mem_replicate] at this
      exact this.2.symm
    simp [hr, this]

/-- A conjunction with a member only names declared sorts. -/
theorem subset_names_of_memC {S : Sorts} {c : Conj} {t : GTerm} (h : MemC S c t) :
    c ⊆ names S := by
  intro n hn
  obtain ⟨f, ts, rfl, _⟩ := exists_mk t
  obtain ⟨ks, hs, _⟩ := mem_mk.mp (h n hn)
  obtain ⟨d, hd, _⟩ := step_cases hs
  simp only [names, List.mem_toFinset, List.mem_flatMap]
  exact ⟨(n, d), mem_of_lookup hd, by simp⟩

/-- The symbols the declarations mention. -/
def usedSyms (S : Sorts) : Finset Sym :=
  (S.flatMap fun p => p.2.cases.map (·.1) ++
    (match p.2.rest with
      | some (ex, _) => ex.map (·.1)
      | none => [])).toFinset

theorem restOK_memC {S : Sorts} {c : Conj} (h : RestOK S c) : ∃ t, MemC S c t := by
  obtain ⟨g, hg⟩ := Infinite.exists_notMem_finset (usedSyms S)
  refine ⟨Term.mk g [], fun n hn => ?_⟩
  have hr := h n hn
  cases hd : S.lookup n with
  | none => simp [hd] at hr
  | some d =>
    cases hrest : d.rest with
    | none => simp [hd, hrest] at hr
    | some er =>
      obtain ⟨ex, r⟩ := er
      have hmem := mem_of_lookup hd
      have hnc : ∀ cs ∈ d.cases, cs.1 ≠ g := by
        intro cs hcs e
        apply hg
        simp only [usedSyms, List.mem_toFinset, List.mem_flatMap, List.mem_append, List.mem_map]
        exact ⟨(n, d), hmem, Or.inl ⟨cs, hcs, e⟩⟩
      have hne : (g, 0) ∉ ex := by
        intro e
        apply hg
        simp only [usedSyms, List.mem_toFinset, List.mem_flatMap, List.mem_append, List.mem_map]
        exact ⟨(n, d), hmem, Or.inr (by simp only [hrest]; exact List.mem_map.mpr ⟨(g, 0), e, rfl⟩)⟩
      refine mem_mk.mpr ⟨[], ?_, by simp⟩
      simp only [step, hd, Option.bind_some, SortDef.step, List.length_nil]
      have : d.cases.find? (fun c => decide (c.1 = g ∧ c.2.length = 0)) = none := by
        rw [List.find?_eq_none]
        intro cs hcs
        simp [hnc cs hcs]
      rw [this]
      simp [hrest, hne]

theorem mem_live_iff {S : Sorts} {c : Conj} : c ∈ live S ↔ ∃ t, MemC S c t := by
  constructor
  · revert c
    apply saturate.induction
    intro P hP c hc
    simp only [grow, Finset.mem_inter, Finset.mem_filter] at hc
    rcases hc.1.2 with hr | ⟨key, _, hacc, hk⟩
    · exact restOK_memC hr
    · obtain ⟨f, k⟩ := key
      simp only at hacc hk
      have : Nonempty GTerm := ⟨Term.sym ""⟩
      choose! w hw using fun i (hi : i < k) => hP _ (hk i hi)
      refine ⟨Term.mk f (List.ofFn fun i : Fin k => w i), memC_mk.mpr ⟨by simpa using hacc, ?_⟩⟩
      intro i hi
      simp only [List.length_ofFn] at hi ⊢
      simpa using hw i hi
  · rintro ⟨t, ht⟩
    induction hsz : t.size using Nat.strong_induction_on generalizing c t with
    | _ sz ih =>
      obtain ⟨f, ts, rfl, hlt⟩ := exists_mk t
      have hsub := subset_names_of_memC ht
      obtain ⟨hacc, hall⟩ := memC_mk.mp ht
      apply saturate.closed
      simp only [grow, Finset.mem_inter, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨⟨hsub, ?_⟩, hsub⟩
      by_cases hkey : (f, ts.length) ∈ caseKeys S c
      · right
        refine ⟨(f, ts.length), hkey, hacc, fun i hi => ?_⟩
        exact ih _ (by subst hsz; exact hlt _ (List.getElem_mem hi)) _ (hall i hi) rfl
      · left
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

/-- Whether a conjunction of sorts has a member is decidable. -/
instance (S : Sorts) (c : Conj) : Decidable (∃ t, MemC S c t) :=
  decidable_of_iff _ mem_live_iff

end Sorts
end RwLog
