/-
# How many members a conjunction has

A conjunction of sorts has no member, one, or more than one, and `count`
computes which, with the member when there is one (`count_none`, `count_one`,
`count_many`). When the sorts are well formed, more than one is infinitely
many (`count_many_infinite`).

The member is built from the root down (`one`): a conjunction has exactly one
member when not every sort of it has a rest, one root can be filled, and each
argument of that root has exactly one member.
-/
import RwLog.Sorts.WF

namespace RwLog
namespace Sorts

open Function

variable {S : Sorts}

/-- The values of a list of options, when each has one. -/
def gather {α : Type} : List (Option α) → Option (List α)
  | [] => some []
  | a :: l => a.bind fun x => (gather l).map (x :: ·)

theorem gather_eq_some {α : Type} : ∀ {l : List (Option α)} {ys : List α},
    gather l = some ys ↔ l = ys.map some
  | [], ys => by cases ys <;> simp [gather]
  | a :: l, ys => by
    cases a with
    | none => cases ys <;> simp [gather]
    | some x =>
      cases ys with
      | nil => simp [gather]
      | cons y ys =>
        simp only [gather, Option.bind_some, Option.map_eq_some_iff, List.map_cons,
          List.cons.injEq, Option.some.injEq]
        constructor
        · rintro ⟨zs, hz, rfl, rfl⟩
          exact ⟨rfl, gather_eq_some.1 hz⟩
        · rintro ⟨rfl, h⟩
          exact ⟨ys, gather_eq_some.2 h, rfl, rfl⟩

theorem gather_range {α : Type} {k : Nat} {g : Nat → Option α} {ys : List α} :
    gather ((List.range k).map g) = some ys ↔
      ys.length = k ∧ ∀ i (h : i < ys.length), g i = some ys[i] := by
  rw [gather_eq_some]
  constructor
  · intro h
    have hl : ys.length = k := by simpa using (congrArg List.length h).symm
    refine ⟨hl, fun i hi => ?_⟩
    have := congrArg (fun l => l[i]?) h
    simpa [hl ▸ hi, List.getElem?_eq_getElem hi] using this
  · rintro ⟨rfl, h⟩
    refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
    simp only [List.length_map, List.length_range] at h₁
    simp [h i h₁]

theorem gather_isSome {α : Type} : ∀ {l : List (Option α)},
    (gather l).isSome = true ↔ ∀ o ∈ l, o.isSome = true
  | [] => by simp [gather]
  | a :: l => by
    cases a with
    | none => simp [gather]
    | some x => simp [gather, gather_isSome (l := l)]

/-- The roots of members of `c`, when not every sort of `c` has a rest. -/
def liveKeys (S : Sorts) (c : Conj) : Finset (Sym × Nat) :=
  (caseKeys S c).filter (LiveKey S (live S) c)

/-- The member of a set that has exactly one. -/
def only {α : Type} [DecidableEq α] (K : Finset α) : Option α :=
  if h : K.card = 1 then
    some (K.choose (fun _ => True) (by
      obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 h
      exact ⟨a, by simp, by simp⟩))
  else none

theorem only_eq_some {α : Type} [DecidableEq α] {K : Finset α} {a : α} :
    only K = some a ↔ K = {a} := by
  unfold only
  constructor
  · intro h
    split at h
    · rename_i hc
      obtain ⟨b, rfl⟩ := Finset.card_eq_one.1 hc
      simp only [Option.some.injEq] at h
      have := Finset.choose_mem (fun _ => True) ({b} : Finset α) (by exact ⟨b, by simp, by simp⟩)
      rw [h] at this
      rw [Finset.mem_singleton.1 this]
    · cases h
  · rintro rfl
    simp only [Finset.card_singleton, ↓reduceDIte, Option.some.injEq]
    have := Finset.choose_mem (fun _ => True) ({a} : Finset α) (by exact ⟨a, by simp, by simp⟩)
    rw [Finset.mem_singleton.1 this]

/-- The one member of `c`, looking at most `n` deep. -/
def one (S : Sorts) : Nat → Conj → Option GTerm
  | 0, _ => none
  | n + 1, c =>
    if RestOK S c then none
    else (only (liveKeys S c)).bind fun key =>
      (gather ((List.range key.2).map fun i => one S n (kidC S c key.1 key.2 i))).map
        (Term.mk key.1)

theorem one_succ {n : Nat} {c : Conj} {t : GTerm} :
    one S (n + 1) c = some t ↔ ¬ RestOK S c ∧ ∃ f ts, liveKeys S c = {(f, ts.length)} ∧
      (∀ i (h : i < ts.length), one S n (kidC S c f ts.length i) = some ts[i]) ∧
      t = Term.mk f ts := by
  simp only [one]
  by_cases hr : RestOK S c
  · simp [hr]
  · simp only [hr, ↓reduceIte, not_false_eq_true, true_and, Option.bind_eq_some_iff,
      Option.map_eq_some_iff, only_eq_some, gather_range]
    constructor
    · rintro ⟨⟨f, k⟩, hk, ts, ⟨hl, h⟩, rfl⟩
      subst hl
      exact ⟨f, ts, hk, h, rfl⟩
    · rintro ⟨f, ts, hk, h, rfl⟩
      exact ⟨(f, ts.length), hk, ts, ⟨rfl, h⟩, rfl⟩

theorem one_isSome_succ {n : Nat} {c : Conj} :
    (one S (n + 1) c).isSome = true ↔ ¬ RestOK S c ∧ ∃ key, liveKeys S c = {key} ∧
      ∀ i < key.2, (one S n (kidC S c key.1 key.2 i)).isSome = true := by
  simp only [one]
  by_cases hr : RestOK S c
  · simp [hr]
  · simp only [hr, ↓reduceIte, not_false_eq_true, true_and, Option.isSome_iff_exists,
      Option.bind_eq_some_iff, only_eq_some]
    constructor
    · rintro ⟨t, key, hk, ht⟩
      refine ⟨key, hk, fun i hi => ?_⟩
      have : (gather ((List.range key.2).map fun i => one S n (kidC S c key.1 key.2 i))).isSome
          = true := by
        rw [Option.map_eq_some_iff] at ht
        obtain ⟨ts, hts, -⟩ := ht
        simp [hts]
      rw [gather_isSome] at this
      exact Option.isSome_iff_exists.1 (this _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩))
    · rintro ⟨key, hk, h⟩
      have : (gather ((List.range key.2).map fun i => one S n (kidC S c key.1 key.2 i))).isSome
          = true := by
        rw [gather_isSome]
        intro o ho
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ho
        exact Option.isSome_iff_exists.2 (h i (List.mem_range.1 hi))
      obtain ⟨ts, hts⟩ := Option.isSome_iff_exists.1 this
      exact ⟨Term.mk key.1 ts, key, hk, by simp [hts]⟩

/-- Looking deeper finds the same member. -/
theorem one_mono : ∀ {n : Nat} {c : Conj} {t : GTerm}, one S n c = some t →
    one S (n + 1) c = some t
  | 0, _, _, h => by simp [one] at h
  | n + 1, c, t, h => by
    obtain ⟨hr, f, ts, hk, hts, rfl⟩ := one_succ.1 h
    exact one_succ.2 ⟨hr, f, ts, hk, fun i hi => one_mono (hts i hi), rfl⟩

theorem mem_liveKeys_of_memC {c : Conj} (hr : ¬ RestOK S c) {f : Sym} {ts : List GTerm}
    (h : MemC S c (Term.mk f ts)) : (f, ts.length) ∈ liveKeys S c := by
  refine Finset.mem_filter.2 ⟨?_, liveKey_of_memC h⟩
  by_contra hk
  exact hr (restOK_of_not_caseKey (memC_mk.1 h).1 hk)

/-- What `one` finds is a member, and the only one. -/
theorem one_sound : ∀ {n : Nat} {c : Conj} {t : GTerm}, one S n c = some t →
    MemC S c t ∧ ∀ u, MemC S c u → u = t
  | 0, _, _, h => by simp [one] at h
  | n + 1, c, t, h => by
    obtain ⟨hr, f, ts, hk, hts, rfl⟩ := one_succ.1 h
    have hmem : (f, ts.length) ∈ liveKeys S c := by rw [hk]; exact Finset.mem_singleton_self _
    refine ⟨memC_mk.2 ⟨(Finset.mem_filter.1 hmem).2.1, fun i hi => (one_sound (hts i hi)).1⟩, ?_⟩
    intro u hu
    obtain ⟨g, us, rfl, -⟩ := exists_mk u
    have := mem_liveKeys_of_memC hr hu
    rw [hk, Finset.mem_singleton, Prod.mk.injEq] at this
    obtain ⟨rfl, hl⟩ := this
    congr 1
    refine List.ext_getElem hl fun i h₁ h₂ => ?_
    have := (memC_mk.1 hu).2 i h₁
    rw [hl] at this
    exact (one_sound (hts i h₂)).2 _ this

/-- One round: the conjunctions with one member, given that those in `P` have. -/
def growOne (S : Sorts) (P : Finset Conj) : Finset Conj :=
  (names S).powerset.filter fun c =>
    ¬ RestOK S c ∧ ∃ key ∈ liveKeys S c, liveKeys S c = {key} ∧
      ∀ i < key.2, kidC S c key.1 key.2 i ∈ P

/-- The conjunctions of declared sorts that `one` finds a member of. -/
def found (S : Sorts) (n : Nat) : Finset Conj :=
  (names S).powerset.filter fun c => (one S n c).isSome = true

theorem found_succ (n : Nat) :
    found S (n + 1) = found S n ∪ (growOne S (found S n) ∩ (names S).powerset) := by
  ext c
  simp only [found, growOne, Finset.mem_filter, Finset.mem_powerset, Finset.mem_union,
    Finset.mem_inter]
  constructor
  · rintro ⟨hc, h⟩
    right
    obtain ⟨hr, key, hk, hkids⟩ := one_isSome_succ.1 h
    exact ⟨⟨hc, hr, key, by rw [hk]; exact Finset.mem_singleton_self _, hk,
      fun i hi => ⟨kidC_subset_names, hkids i hi⟩⟩, hc⟩
  · rintro (⟨hc, h⟩ | ⟨⟨hc, hr, key, -, hk, hkids⟩, -⟩)
    · obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 h
      exact ⟨hc, by rw [one_mono ht]; rfl⟩
    · exact ⟨hc, one_isSome_succ.2 ⟨hr, key, hk, fun i hi => (hkids i hi).2⟩⟩

theorem found_closed :
    growOne S (found S (names S).powerset.card) ∩ (names S).powerset ⊆
      found S (names S).powerset.card := by
  rw [saturate.chain (names S).powerset (growOne S) (found S) (by simp [found, one]) found_succ]
  exact saturate.closed _ _

/-- A conjunction with exactly one member is found. -/
theorem mem_found : ∀ (t : GTerm) {c : Conj}, MemC S c t → (∀ u, MemC S c u → u = t) →
    c ∈ found S (names S).powerset.card := by
  intro t
  induction h : t.size using Nat.strong_induction_on generalizing t with
  | _ m ih =>
    intro c ht hu
    obtain ⟨f, ts, rfl, hsz⟩ := exists_mk t
    have hsub : c ⊆ names S := subset_names_of_memC ht
    have hr : ¬ RestOK S c := fun hr =>
      restOK_infinite hr ((Set.finite_singleton (Term.mk f ts)).subset fun u hu' => hu u hu')
    have hkey := mem_liveKeys_of_memC hr ht
    refine found_closed (Finset.mem_inter.2 ⟨?_, Finset.mem_powerset.2 hsub⟩)
    simp only [growOne, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨hsub, hr, (f, ts.length), hkey, ?_, ?_⟩
    · refine Finset.eq_singleton_iff_unique_mem.2 ⟨hkey, ?_⟩
      rintro ⟨g, k⟩ hg
      have hl := (Finset.mem_filter.1 hg).2
      obtain ⟨w, hw⟩ := hl.fn
      have := Term.mk_inj (hu _ (memC_ofFn hl.1 hw))
      obtain ⟨rfl, e⟩ := this
      have : k = ts.length := by simpa using congrArg List.length e
      rw [this]
    · intro i hi
      refine ih _ (by subst h; exact hsz _ (List.getElem_mem hi)) ts[i] rfl
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

/-- `one` finds the member of a conjunction exactly when it has just one. -/
theorem one_eq_some {c : Conj} {t : GTerm} :
    one S (names S).powerset.card c = some t ↔ MemC S c t ∧ ∀ u, MemC S c u → u = t := by
  refine ⟨one_sound, fun ⟨ht, hu⟩ => ?_⟩
  have := mem_found t ht hu
  simp only [found, Finset.mem_filter] at this
  obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.1 this.2
  rw [ht', hu _ (one_sound ht').1]

/-- How many members a conjunction has. -/
inductive Count where
  /-- No member. -/
  | none
  /-- This member and no other. -/
  | one (t : GTerm)
  /-- More than one member. -/
  | many
  deriving DecidableEq

/-- How many members `c` has. -/
def count (S : Sorts) (c : Conj) : Count :=
  if c ∈ live S then
    match one S (names S).powerset.card c with
    | some t => .one t
    | none => .many
  else .none

theorem count_none {c : Conj} : count S c = .none ↔ ¬ ∃ t, MemC S c t := by
  rw [← mem_live_iff]
  unfold count
  split
  · rename_i h; simp only [h, not_true_eq_false, iff_false]; split <;> simp
  · rename_i h; simp [h]

theorem count_one {c : Conj} {t : GTerm} :
    count S c = .one t ↔ MemC S c t ∧ ∀ u, MemC S c u → u = t := by
  rw [← one_eq_some]
  unfold count
  constructor
  · intro h
    split at h
    · split at h
      · rename_i e; rw [e]; cases h; rfl
      · cases h
    · cases h
  · intro h
    simp only [mem_live_iff.2 ⟨t, (one_sound h).1⟩, ↓reduceIte, h]

theorem count_many {c : Conj} :
    count S c = .many ↔ ∃ t₁ t₂, t₁ ≠ t₂ ∧ MemC S c t₁ ∧ MemC S c t₂ := by
  constructor
  · intro h
    have hn : ∃ t, MemC S c t := by
      by_contra hn; rw [count_none.2 hn] at h; cases h
    obtain ⟨t, ht⟩ := hn
    by_contra hne
    have : count S c = .one t := count_one.2 ⟨ht, fun u hu => by
      by_contra e; exact hne ⟨u, t, e, hu, ht⟩⟩
    rw [this] at h; cases h
  · rintro ⟨t₁, t₂, hne, h₁, h₂⟩
    cases hs : count S c with
    | none => exact absurd ⟨t₁, h₁⟩ (count_none.1 hs)
    | one t => exact absurd (((count_one.1 hs).2 _ h₁).trans ((count_one.1 hs).2 _ h₂).symm) hne
    | many => rfl

/-- Among well-formed sorts, more than one member is infinitely many. -/
theorem count_many_infinite (hS : S.WellFormed) {c : Conj} (h : count S c = .many) :
    {t | MemC S c t}.Infinite := by
  obtain ⟨t₁, t₂, hne, h₁, h₂⟩ := count_many.1 h
  intro hfin
  have := wellFormed_iff.1 hS
  rw [Finset.eq_empty_iff_forall_notMem] at this
  exact this c (Finset.mem_inter.2 ⟨mem_big_iff.2 ⟨t₁, t₂, hne, h₁, h₂⟩,
    (mem_fin_iff (subset_names_of_memC h₁)).2 hfin⟩)

end Sorts
end RwLog
