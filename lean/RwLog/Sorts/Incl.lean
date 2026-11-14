/-
# Inclusion of a conjunction of sorts in a sort

`Out S c n` says some member of the conjunction `c` is not in the sort `n`.
It is decided by saturation over pairs, like emptiness. A member of `c`
outside `n` has one of three shapes:

* a root that `n` rejects, with every argument position of `c` inhabited;
* a root both accept, with one argument outside the sort `n` requires there;
* when every sort of `c` has a rest: a symbol no declaration mentions, which
  `n` rejects for having no rest, or accepts with an argument outside the sort
  its rest requires.
-/
import RwLog.Sorts.Empty
import Mathlib.Data.Finset.Prod

namespace RwLog
namespace Sorts

/-- Some member of `c` is not in the sort `n`. -/
def Out (S : Sorts) (c : Conj) (n : Name) : Prop := ∃ t, MemC S c t ∧ mem S n t = false

/-- The roots the rest of `n` excludes. -/
def exKeys (S : Sorts) (n : Name) : Finset (Sym × Nat) :=
  match (S.lookup n).bind (·.rest) with
  | some (ex, _) => ex.toFinset
  | none => ∅

/-- The sorts the rests of `c` require of arguments. -/
def restKids (S : Sorts) (c : Conj) : Conj :=
  c.biUnion fun s => (((S.lookup s).bind (·.rest)).bind (·.2)).toFinset

theorem mem_caseKeys {S : Sorts} {c : Conj} {f : Sym} {k : Nat} :
    (f, k) ∈ caseKeys S c ↔
      ∃ s ∈ c, ∃ d, S.lookup s = some d ∧ ∃ cs ∈ d.cases, cs.1 = f ∧ cs.2.length = k := by
  simp only [caseKeys, Finset.mem_biUnion]
  constructor
  · rintro ⟨s, hs, h⟩
    cases hd : S.lookup s with
    | none => simp [hd] at h
    | some d =>
      simp only [hd, List.mem_toFinset, List.mem_map, Prod.mk.injEq] at h
      obtain ⟨cs, hcs, h1, h2⟩ := h
      exact ⟨s, hs, d, hd, cs, hcs, h1, h2⟩
  · rintro ⟨s, hs, d, hd, cs, hcs, h1, h2⟩
    refine ⟨s, hs, ?_⟩
    simp only [hd, List.mem_toFinset, List.mem_map, Prod.mk.injEq]
    exact ⟨cs, hcs, h1, h2⟩

theorem mem_restKids {S : Sorts} {c : Conj} {m : Name} :
    m ∈ restKids S c ↔ ∃ s ∈ c, ∃ d ex, S.lookup s = some d ∧ d.rest = some (ex, some m) := by
  simp only [restKids, Finset.mem_biUnion, Option.mem_toFinset, Option.mem_def]
  constructor
  · rintro ⟨s, hs, h⟩
    cases hd : S.lookup s with
    | none => simp [hd] at h
    | some d =>
      cases hr : d.rest with
      | none => simp [hd, hr] at h
      | some er =>
        obtain ⟨ex, r⟩ := er
        simp only [hd, hr, Option.bind_some] at h
        exact ⟨s, hs, d, ex, hd, by rw [hr, h]⟩
  · rintro ⟨s, hs, d, ex, hd, hr⟩
    exact ⟨s, hs, by simp [hd, hr]⟩

/-- When no sort of `c` has a case for the root, the arguments are in the
sorts the rests require. -/
theorem kidC_of_rest {S : Sorts} {c : Conj} {f : Sym} {k i : Nat}
    (hkey : (f, k) ∉ caseKeys S c) (hacc : Accepts S c f k) (hi : i < k) :
    kidC S c f k i = restKids S c := by
  ext m
  rw [mem_kidC, mem_restKids]
  constructor
  · rintro ⟨s, hs, ks, hst, hg⟩
    obtain ⟨d, hd, hcase⟩ := step_cases hst
    rcases hcase with ⟨cs, hcs, h1, h2, _⟩ | ⟨_, ex, r, hr, _, rfl⟩
    · exact absurd (mem_caseKeys.mpr ⟨s, hs, d, hd, cs, hcs, h1, h2⟩) hkey
    · have := List.mem_of_getElem? hg
      rw [List.mem_replicate] at this
      exact ⟨s, hs, d, ex, hd, by rw [hr, this.2]⟩
  · rintro ⟨s, hs, d, ex, hd, hr⟩
    have := hacc s hs
    rw [Option.isSome_iff_exists] at this
    obtain ⟨ks, hst⟩ := this
    refine ⟨s, hs, ks, hst, ?_⟩
    obtain ⟨d', hd', hcase⟩ := step_cases hst
    rw [hd] at hd'; cases hd'
    rcases hcase with ⟨cs, hcs, h1, h2, _⟩ | ⟨_, ex', r, hr', _, rfl⟩
    · exact absurd (mem_caseKeys.mpr ⟨s, hs, d, hd, cs, hcs, h1, h2⟩) hkey
    · rw [hr] at hr'; cases hr'
      simp [hi]

theorem restKids_subset_names {S : Sorts} {c : Conj} : restKids S c ⊆ names S := by
  intro m hm
  obtain ⟨s, _, d, ex, hd, hr⟩ := mem_restKids.mp hm
  simp only [names, List.mem_toFinset, List.mem_flatMap]
  refine ⟨(s, d), mem_of_lookup hd, List.mem_cons_of_mem _ ?_⟩
  simp [SortDef.kidNames, hr]

/-- The sort the rest of `n` requires of arguments. -/
def restKid (S : Sorts) (n : Name) : Option Name := ((S.lookup n).bind (·.rest)).bind (·.2)

theorem restKid_eq {S : Sorts} {n m : Name} :
    restKid S n = some m ↔ ∃ d ex, S.lookup n = some d ∧ d.rest = some (ex, some m) := by
  unfold restKid
  cases hd : S.lookup n with
  | none => simp
  | some d =>
    cases hr : d.rest with
    | none => simp [hr]
    | some er => obtain ⟨ex, r⟩ := er; simp [hr]

theorem stepKid_eq {S : Sorts} {n : Name} {f : Sym} {k i : Nat} {m : Name} :
    (step S n f k).bind (·[i]?) = some (some m) ↔
      ∃ ks, step S n f k = some ks ∧ ks[i]? = some (some m) := by
  cases step S n f k <;> simp

/-- One round for `Out`. -/
def growOut (S : Sorts) (P : Finset (Conj × Name)) : Finset (Conj × Name) :=
  let L := live S
  ((names S).powerset ×ˢ names S).filter fun p =>
    (RestOK S p.1 ∧ ((S.lookup p.2).bind (·.rest)).isSome = false) ∨
    (RestOK S p.1 ∧ ∃ m ∈ names S,
        restKid S p.2 = some m ∧ (restKids S p.1, m) ∈ P) ∨
    ∃ key ∈ caseKeys S p.1 ∪ caseKeys S {p.2} ∪ exKeys S p.2,
      Accepts S p.1 key.1 key.2 ∧ (∀ i < key.2, kidC S p.1 key.1 key.2 i ∈ L) ∧
        ((step S p.2 key.1 key.2).isSome = false ∨
          ∃ i < key.2, ∃ m ∈ names S,
            (step S p.2 key.1 key.2).bind (·[i]?) = some (some m) ∧
              (kidC S p.1 key.1 key.2 i, m) ∈ P)

/-- The pairs `(c, n)`, with `n` a mentioned name, such that `c` has a member
outside `n`. -/
def outs (S : Sorts) : Finset (Conj × Name) :=
  saturate ((names S).powerset ×ˢ names S) (growOut S)

theorem mem_false_of_kid {S : Sorts} {n : Name} {f : Sym} {ts : List GTerm}
    {ks : List (Option Name)} {i : Nat} {m : Name} (hs : step S n f ts.length = some ks)
    (hi : i < ts.length) (hg : ks[i]? = some (some m)) (hm : mem S m ts[i] = false) :
    mem S n (Term.mk f ts) = false := by
  by_contra h
  rw [Bool.not_eq_false] at h
  obtain ⟨ks', hs', hall⟩ := mem_mk.mp h
  rw [hs] at hs'; cases hs'
  have := hall i hi
  simp [hg, memO, hm] at this

section

variable {S : Sorts}

/-! ## Why a sort rejects a term -/

theorem mem_mk_false {n : Name} {f : Sym} {ts : List GTerm} :
    mem S n (Term.mk f ts) = false ↔ step S n f ts.length = none ∨
      ∃ i, ∃ _ : i < ts.length, ∃ ks m, step S n f ts.length = some ks ∧
        ks[i]? = some (some m) ∧ mem S m ts[i] = false := by
  constructor
  · intro htn
    cases hs : step S n f ts.length with
    | none => left; rfl
    | some ks =>
      right
      by_contra hno
      have : mem S n (Term.mk f ts) = true := by
        refine mem_mk.mpr ⟨ks, hs, fun i hi => ?_⟩
        cases hg : ks[i]? with
        | none => rfl
        | some o =>
          cases o with
          | none => rfl
          | some m =>
            simp only [Option.getD_some, memO]
            by_contra hm
            rw [Bool.not_eq_true] at hm
            exact hno ⟨i, hi, ks, m, rfl, hg, hm⟩
      rw [this] at htn; cases htn
  · rintro (hs | ⟨i, hi, ks, m, hs, hg, hm⟩)
    · by_contra h
      rw [Bool.not_eq_false] at h
      obtain ⟨ks, hs', _⟩ := mem_mk.mp h
      rw [hs] at hs'; cases hs'
    · exact mem_false_of_kid hs hi hg hm

/-! ## Symbols no declaration mentions -/

theorem fresh_not_case {g : Sym} (hg : g ∉ usedSyms S) {s : Name} {d : SortDef}
    (hd : S.lookup s = some d) : ∀ cs ∈ d.cases, cs.1 ≠ g := by
  intro cs hcs e
  apply hg
  simp only [usedSyms, List.mem_toFinset, List.mem_flatMap, List.mem_append, List.mem_map]
  exact ⟨(s, d), mem_of_lookup hd, Or.inl ⟨cs, hcs, e⟩⟩

theorem step_fresh {g : Sym} (hg : g ∉ usedSyms S) {s : Name} {d : SortDef}
    {ex : List (Sym × Nat)} {r : Option Name} (k : Nat) (hd : S.lookup s = some d)
    (hr : d.rest = some (ex, r)) : step S s g k = some (List.replicate k r) := by
  have gex : (g, k) ∉ ex := by
    intro e
    apply hg
    simp only [usedSyms, List.mem_toFinset, List.mem_flatMap, List.mem_append, List.mem_map]
    exact ⟨(s, d), mem_of_lookup hd, Or.inr (by simp only [hr]; exact List.mem_map.mpr ⟨(g, k), e, rfl⟩)⟩
  simp only [step, hd, Option.bind_some, SortDef.step]
  have : d.cases.find? (fun c => decide (c.1 = g ∧ c.2.length = k)) = none := by
    rw [List.find?_eq_none]
    intro cs hcs
    simp [fresh_not_case hg hd cs hcs]
  rw [this]
  simp [hr, gex]

theorem fresh_not_caseKey {g : Sym} (hg : g ∉ usedSyms S) (c : Conj) (k : Nat) :
    (g, k) ∉ caseKeys S c := by
  intro h
  obtain ⟨s, _, d, hd, cs, hcs, h1, _⟩ := mem_caseKeys.mp h
  exact fresh_not_case hg hd cs hcs h1

theorem accepts_fresh {g : Sym} (hg : g ∉ usedSyms S) {c : Conj} (hr : RestOK S c) (k : Nat) :
    Accepts S c g k := by
  intro s hs
  have := hr s hs
  cases hd : S.lookup s with
  | none => simp [hd] at this
  | some d =>
    cases hrest : d.rest with
    | none => simp [hd, hrest] at this
    | some er => obtain ⟨ex, r⟩ := er; simp [step_fresh hg k hd hrest]

end

theorem outs_sound {S : Sorts} : ∀ p ∈ outs S, Out S p.1 p.2 := by
  apply saturate.induction
  rintro P hP ⟨c, n⟩ hc
  simp only [growOut, Finset.mem_inter, Finset.mem_filter, restKid_eq, stepKid_eq] at hc
  obtain ⟨g, hg⟩ := Infinite.exists_notMem_finset (usedSyms S)
  have gcase : ∀ s d, S.lookup s = some d → ∀ cs ∈ d.cases, cs.1 ≠ g :=
    fun s d hd => fresh_not_case hg hd
  have gstep : ∀ s d ex r k, S.lookup s = some d → d.rest = some (ex, r) →
      step S s g k = some (List.replicate k r) := fun s d ex r k hd hr => step_fresh hg k hd hr
  have gkey : ∀ k, (g, k) ∉ caseKeys S c := fresh_not_caseKey hg c
  have gacc : RestOK S c → ∀ k, Accepts S c g k := fun hr k => accepts_fresh hg hr k
  rcases hc.1.2 with ⟨hr, hn⟩ | ⟨hr, m, _, ⟨d, ex, hd, hn⟩, hp⟩ | ⟨key, _, hacc, hlive, hn⟩
  · -- a fresh constant, which `n` rejects for having no rest
    refine ⟨Term.mk g [], memC_mk.mpr ⟨gacc hr 0, by simp⟩, ?_⟩
    by_contra h
    rw [Bool.not_eq_false] at h
    obtain ⟨ks, hs, _⟩ := mem_mk.mp h
    obtain ⟨d, hd, hcase⟩ := step_cases hs
    rcases hcase with ⟨cs, hcs, h1, _⟩ | ⟨_, ex, r, hr', _⟩
    · exact gcase n d hd cs hcs h1
    · simp [hd, hr'] at hn
  · -- a fresh unary symbol over a term outside the rest sort of `n`
    obtain ⟨w, hw, hwm⟩ := hP _ hp
    refine ⟨Term.mk g [w], memC_mk.mpr ⟨gacc hr 1, ?_⟩, ?_⟩
    · intro i hi
      simp only [List.length_singleton] at hi ⊢
      have : i = 0 := by omega
      subst this
      rw [kidC_of_rest (gkey 1) (gacc hr 1) (by omega)]
      simpa using hw
    · exact mem_false_of_kid (ts := [w]) (i := 0) (m := m) (gstep n d ex (some m) 1 hd hn)
        (by simp) (by simp) (by simpa using hwm)
  · obtain ⟨f, k⟩ := key
    simp only at hacc hlive hn
    have hlive' : ∀ i < k, ∃ t, MemC S (kidC S c f k i) t := fun i hi => mem_live_iff.mp (hlive i hi)
    have : Nonempty GTerm := ⟨Term.sym ""⟩
    choose! w hw using hlive'
    rcases hn with hn | ⟨i, hi, m, _, ⟨ks, hs, hg'⟩, hp⟩
    · refine ⟨Term.mk f (List.ofFn fun j : Fin k => w j), memC_mk.mpr ⟨by simpa using hacc, ?_⟩, ?_⟩
      · intro j hj
        simp only [List.length_ofFn] at hj ⊢
        simpa using hw j hj
      · by_contra h
        rw [Bool.not_eq_false] at h
        obtain ⟨ks, hs, _⟩ := mem_mk.mp h
        simp only [List.length_ofFn] at hs
        simp [hs] at hn
    · obtain ⟨u, hu, hum⟩ := hP _ hp
      refine ⟨Term.mk f (List.ofFn fun j : Fin k => if j.1 = i then u else w j),
        memC_mk.mpr ⟨by simpa using hacc, ?_⟩, ?_⟩
      · intro j hj
        simp only [List.length_ofFn] at hj ⊢
        simp only [List.getElem_ofFn]
        split
        · rename_i e; subst e; exact hu
        · exact hw j hj
      · refine mem_false_of_kid (i := i) (by simpa using hs) (by simpa using hi) hg' ?_
        simpa using hum

theorem outs_complete {S : Sorts} {c : Conj} {n : Name} (hn : n ∈ names S) (h : Out S c n) :
    (c, n) ∈ outs S := by
  obtain ⟨t, ht, htn⟩ := h
  induction hsz : t.size using Nat.strong_induction_on generalizing c n t with
  | _ sz ih =>
    obtain ⟨f, ts, rfl, hlt⟩ := exists_mk t
    have hsub := subset_names_of_memC ht
    obtain ⟨hacc, hall⟩ := memC_mk.mp ht
    apply saturate.closed
    have hU : (c, n) ∈ (names S).powerset ×ˢ names S := by
      simp [Finset.mem_product, hsub, hn]
    simp only [growOut, Finset.mem_inter, Finset.mem_filter, restKid_eq, stepKid_eq]
    refine ⟨⟨hU, ?_⟩, hU⟩
    -- why `n` rejects the term
    have hwhy : (step S n f ts.length).isSome = false ∨
        ∃ i, ∃ _ : i < ts.length, ∃ ks m, step S n f ts.length = some ks ∧
          ks[i]? = some (some m) ∧ mem S m ts[i] = false := by
      rcases mem_mk_false.1 htn with h | h
      · exact Or.inl (by simp [h])
      · exact Or.inr h
    by_cases hkey : (f, ts.length) ∈ caseKeys S c ∪ caseKeys S {n} ∪ exKeys S n
    · right; right
      refine ⟨(f, ts.length), hkey, hacc, fun i hi => mem_live_iff.mpr ⟨_, hall i hi⟩, ?_⟩
      rcases hwhy with h | ⟨i, hi, ks, m, hs, hg, hm⟩
      · exact Or.inl h
      · right
        have hmn : m ∈ names S := kidC_subset_names (c := {n}) (i := i)
          (mem_kidC.mpr ⟨n, by simp, ks, hs, hg⟩)
        refine ⟨i, hi, m, hmn, ⟨ks, hs, hg⟩, ?_⟩
        exact ih _ (by subst hsz; exact hlt _ (List.getElem_mem hi)) hmn _ (hall i hi) hm rfl
    · simp only [Finset.mem_union, not_or] at hkey
      obtain ⟨⟨hkc, hkn⟩, hke⟩ := hkey
      have hrest : RestOK S c := by
        intro s hs
        have := hacc s hs
        rw [Option.isSome_iff_exists] at this
        obtain ⟨ks, hst⟩ := this
        obtain ⟨d, hd, hcase⟩ := step_cases hst
        rcases hcase with ⟨cs, hcs, h1, h2, _⟩ | ⟨_, ex, r, hr, _, _⟩
        · exact absurd (mem_caseKeys.mpr ⟨s, hs, d, hd, cs, hcs, h1, h2⟩) hkc
        · simp [hd, hr]
      rcases hwhy with h | ⟨i, hi, ks, m, hs, hg, hm⟩
      · left
        refine ⟨hrest, ?_⟩
        cases hd : S.lookup n with
        | none => simp
        | some d =>
          cases hr : d.rest with
          | none => simp [hr]
          | some er =>
            exfalso
            obtain ⟨ex, r⟩ := er
            have hfind : d.cases.find? (fun c => decide (c.1 = f ∧ c.2.length = ts.length)) = none := by
              rw [List.find?_eq_none]
              intro cs hcs
              simp only [decide_eq_true_eq]
              intro ⟨h1, h2⟩
              exact hkn (mem_caseKeys.mpr ⟨n, by simp, d, hd, cs, hcs, h1, h2⟩)
            have hnex : (f, ts.length) ∉ ex := by
              intro e
              apply hke
              simp [exKeys, hd, hr, e]
            simp only [step, hd, Option.bind_some, SortDef.step, hfind, hr] at h
            simp [hnex] at h
      · right; left
        obtain ⟨d, hd, hcase⟩ := step_cases hs
        rcases hcase with ⟨cs, hcs, h1, h2, _⟩ | ⟨_, ex, r, hr, _, rfl⟩
        · exact absurd (mem_caseKeys.mpr ⟨n, by simp, d, hd, cs, hcs, h1, h2⟩) hkn
        · have hrm : r = some m := by
            have := List.mem_of_getElem? hg
            rw [List.mem_replicate] at this
            exact this.2.symm
          subst hrm
          have hmn : m ∈ names S := kidC_subset_names (c := {n}) (i := i)
            (mem_kidC.mpr ⟨n, by simp, _, hs, hg⟩)
          refine ⟨hrest, m, hmn, ⟨d, ex, hd, hr⟩, ?_⟩
          have hkid := hall i hi
          rw [kidC_of_rest hkc hacc hi] at hkid
          exact ih _ (by subst hsz; exact hlt _ (List.getElem_mem hi)) hmn _ hkid hm rfl

/-- A name no declaration mentions is the empty sort. -/
theorem mem_false_of_not_names {S : Sorts} {n : Name} (hn : n ∉ names S) (t : GTerm) :
    mem S n t = false := by
  by_contra h
  rw [Bool.not_eq_false] at h
  have : MemC S {n} t := fun m hm => by
    rw [Finset.mem_singleton] at hm; subst hm; exact h
  exact hn (subset_names_of_memC this (by simp))

theorem out_iff {S : Sorts} {c : Conj} {n : Name} :
    Out S c n ↔ if n ∈ names S then (c, n) ∈ outs S else c ∈ live S := by
  split
  · rename_i hn
    exact ⟨outs_complete hn, fun h => outs_sound _ h⟩
  · rename_i hn
    rw [mem_live_iff]
    exact ⟨fun ⟨t, ht, _⟩ => ⟨t, ht⟩, fun ⟨t, ht⟩ => ⟨t, ht, mem_false_of_not_names hn t⟩⟩

instance (S : Sorts) (c : Conj) (n : Name) : Decidable (Out S c n) :=
  decidable_of_iff _ out_iff.symm

/-- Every member of `c` is in `n`. -/
def Incl (S : Sorts) (c : Conj) (n : Name) : Prop := ∀ t, MemC S c t → mem S n t = true

theorem incl_iff_not_out {S : Sorts} {c : Conj} {n : Name} : Incl S c n ↔ ¬ Out S c n := by
  constructor
  · rintro h ⟨t, ht, hf⟩
    rw [h t ht] at hf; cases hf
  · intro h t ht
    by_contra hm
    rw [Bool.not_eq_true] at hm
    exact h ⟨t, ht, hm⟩

instance (S : Sorts) (c : Conj) (n : Name) : Decidable (Incl S c n) :=
  decidable_of_iff _ incl_iff_not_out.symm

end Sorts
end RwLog
