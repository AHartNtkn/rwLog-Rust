/-
# Emptiness on the conjunctions a conjunction reaches

`live S` saturates over every set of names. To decide whether one conjunction
`c` has a member it is enough to look at the conjunctions `c` *reaches*: `c`,
and the conjunction of each argument of each root that a reached conjunction
has a case for and accepts, unless every sort of it has a rest (then it has a
member whatever its arguments reach). `live_of_stable` says that a set of conjunctions
closed under reaching, with a marking that is sound and that no round
extends, marks exactly its conjunctions that have a member.
-/
import RwLog.Sorts.Empty

namespace RwLog
namespace Sorts

/-- `d` is reached from `c` in one step. -/
def Kid (S : Sorts) (c d : Conj) : Prop :=
  ¬ RestOK S c ∧ ∃ key ∈ caseKeys S c, Accepts S c key.1 key.2 ∧ ∃ i < key.2, d = kidC S c key.1 key.2 i

/-- The conjunctions `c` reaches. -/
inductive Reach (S : Sorts) (c : Conj) : Conj → Prop
  | refl : Reach S c c
  | step {d e : Conj} : Reach S c d → Kid S d e → Reach S c e

/-- What a round of `grow` asks of a conjunction, given that those in `L`
have a member. -/
def Grows (S : Sorts) (L : Conj → Prop) (c : Conj) : Prop :=
  RestOK S c ∨ ∃ key ∈ caseKeys S c,
    Accepts S c key.1 key.2 ∧ ∀ i < key.2, L (kidC S c key.1 key.2 i)

/-- A conjunction a round adds to conjunctions with a member has a member. -/
theorem memC_of_grows {S : Sorts} {c : Conj} (h : Grows S (fun d => ∃ t, MemC S d t) c) :
    ∃ t, MemC S c t := by
  rcases h with hr | ⟨⟨f, k⟩, _, hacc, hk⟩
  · exact restOK_memC hr
  · have : Nonempty GTerm := ⟨Term.sym ""⟩
    choose! w hw using hk
    refine ⟨Term.mk f (List.ofFn fun i : Fin k => w i), memC_mk.mpr ⟨by simpa using hacc, ?_⟩⟩
    intro i hi
    simp only [List.length_ofFn] at hi ⊢
    simpa using hw i hi

/-- A conjunction with a member either has a rest in every sort, or accepts
a root one of its sorts has a case for. -/
theorem grows_of_memC {S : Sorts} {c : Conj} {f : Sym} {ts : List GTerm}
    (h : MemC S c (Term.mk f ts)) (L : Conj → Prop)
    (hL : (f, ts.length) ∈ caseKeys S c → ∀ i (hi : i < ts.length),
      MemC S (kidC S c f ts.length i) ts[i] → L (kidC S c f ts.length i)) :
    Grows S L c := by
  obtain ⟨hacc, hall⟩ := memC_mk.mp h
  by_cases hkey : (f, ts.length) ∈ caseKeys S c
  · exact Or.inr ⟨(f, ts.length), hkey, hacc, fun i hi => hL hkey i hi (hall i hi)⟩
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

/-- On a set of conjunctions closed under reaching, a marking that only marks
conjunctions with a member and that no round extends marks every conjunction
of the set that has a member. -/
theorem live_of_stable {S : Sorts} {R L : Conj → Prop}
    (hclosed : ∀ c d, R c → Kid S c d → R d)
    (hstable : ∀ c, R c → Grows S L c → L c) :
    ∀ c, R c → (∃ t, MemC S c t) → L c := by
  intro c hc ⟨t, ht⟩
  induction hsz : t.size using Nat.strong_induction_on generalizing c t with
  | _ sz ih =>
    obtain ⟨f, ts, rfl, hlt⟩ := exists_mk t
    by_cases hr : RestOK S c
    · exact hstable c hc (Or.inl hr)
    refine hstable c hc (grows_of_memC ht L fun hkey i hi hm => ?_)
    refine ih _ (by subst hsz; exact hlt _ (List.getElem_mem hi)) _
      (hclosed c _ hc ⟨hr, (f, ts.length), hkey, (memC_mk.mp ht).1, i, hi, rfl⟩) _ hm rfl

/-- The same, for the conjunctions one conjunction reaches. -/
theorem live_iff_of_stable {S : Sorts} {c₀ : Conj} {L : Conj → Prop}
    (hsound : ∀ c, L c → ∃ t, MemC S c t)
    (hstable : ∀ c, Reach S c₀ c → Grows S L c → L c) :
    L c₀ ↔ c₀ ∈ live S := by
  rw [mem_live_iff]
  exact ⟨hsound c₀, live_of_stable (R := Reach S c₀) (fun _ _ h k => h.step k) hstable c₀ .refl⟩

/-- Every conjunction reached from a conjunction of names is one. -/
theorem Reach.subset_names {S : Sorts} {c d : Conj} (h : Reach S c d) (hc : c ⊆ names S) :
    d ⊆ names S := by
  induction h with
  | refl => exact hc
  | step _ hk _ =>
    obtain ⟨_, key, _, _, i, _, rfl⟩ := hk
    exact kidC_subset_names

/-- A conjunction reached in one step or more is a conjunction of names. -/
theorem Reach.eq_or_subset_names {S : Sorts} {c d : Conj} (h : Reach S c d) :
    d = c ∨ d ⊆ names S := by
  cases h with
  | refl => exact Or.inl rfl
  | step _ hk =>
    obtain ⟨_, key, _, _, i, _, rfl⟩ := hk
    exact Or.inr kidC_subset_names

open Classical in
/-- The conjunctions `c` reaches, as a finite set. Its size is what deciding
whether `c` has a member is charged by. -/
noncomputable def reachSet (S : Sorts) (c : Conj) : Finset Conj :=
  (insert c (names S).powerset).filter (Reach S c)

theorem mem_reachSet {S : Sorts} {c d : Conj} : d ∈ reachSet S c ↔ Reach S c d := by
  simp only [reachSet, Finset.mem_filter, Finset.mem_insert, Finset.mem_powerset]
  exact ⟨fun h => h.2, fun h => ⟨h.eq_or_subset_names, h⟩⟩

end Sorts
end RwLog
