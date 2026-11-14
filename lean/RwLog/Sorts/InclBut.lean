/-
# Inclusion but for some terms

`inclBut S c n G` decides whether every member of the conjunction `c` other
than the terms of the list `G` is in the sort `n` (`inclBut_iff`, for
well-formed sorts). A variable of sorts `c` that is excluded from each term
of `G` takes exactly those values, so this is what tells the sorts that hold
of all its values.

Root by root: where `n` rejects a root, the conjunction must have one term
with it and that term be in `G`; where `n` sorts the arguments, a term is
left out at one argument, so every other argument must have one value, and
the question is asked again of that argument with the terms of `G` that
agree on the others.
-/
import RwLog.Sorts.Count
import RwLog.Sorts.Incl
import RwLog.Sorts.Store

namespace RwLog
namespace Sorts

open Function

variable {S : Sorts}

/-- A member of `c` outside `n` whose root is one no declaration of `c` or
`n` names. -/
def FreshOut (S : Sorts) (c : Conj) (n : Name) : Prop :=
  RestOK S c ∧ (((S.lookup n).bind (·.rest)).isSome = false ∨
    ∃ m ∈ names S, restKid S n = some m ∧ Out S (restKids S c) m)

instance (S : Sorts) (c : Conj) (n : Name) : Decidable (FreshOut S c n) := by
  unfold FreshOut; infer_instance

/-- Such a member has any root the declarations do not mention. -/
theorem FreshOut.witness {c : Conj} {n : Name} (h : FreshOut S c n) {g : Sym}
    (hg : g ∉ usedSyms S) : ∃ ts, MemC S c (Term.mk g ts) ∧ mem S n (Term.mk g ts) = false := by
  obtain ⟨hr, hn | ⟨m, -, hm, w, hw, hwm⟩⟩ := h
  · refine ⟨[], memC_mk.mpr ⟨accepts_fresh hg hr 0, by simp⟩, ?_⟩
    by_contra h
    rw [Bool.not_eq_false] at h
    obtain ⟨ks, hs, _⟩ := mem_mk.mp h
    obtain ⟨d, hd, hcase⟩ := step_cases hs
    rcases hcase with ⟨cs, hcs, h1, _⟩ | ⟨_, ex, r, hr', _⟩
    · exact fresh_not_case hg hd cs hcs h1
    · simp [hd, hr'] at hn
  · obtain ⟨d, ex, hd, hn⟩ := restKid_eq.1 hm
    refine ⟨[w], memC_mk.mpr ⟨accepts_fresh hg hr 1, ?_⟩, ?_⟩
    · intro i hi
      simp only [List.length_singleton] at hi ⊢
      have : i = 0 := by omega
      subst this
      rw [kidC_of_rest (fresh_not_caseKey hg c 1) (accepts_fresh hg hr 1) (by omega)]
      simpa using hw
    · exact mem_false_of_kid (ts := [w]) (i := 0) (m := m) (step_fresh hg 1 hd hn)
        (by simp) (by simp) (by simpa using hwm)

/-- A member of `c` outside `n` with a root no declaration of `c` or `n`
names. -/
theorem freshOut_of_mem {c : Conj} {n : Name} {f : Sym} {ts : List GTerm}
    (hkey : (f, ts.length) ∉ caseKeys S c ∪ caseKeys S {n} ∪ exKeys S n)
    (ht : MemC S c (Term.mk f ts)) (hf : mem S n (Term.mk f ts) = false) : FreshOut S c n := by
  obtain ⟨hacc, hall⟩ := memC_mk.mp ht
  simp only [Finset.mem_union, not_or] at hkey
  obtain ⟨⟨hkc, hkn⟩, hke⟩ := hkey
  refine ⟨restOK_of_not_caseKey hacc hkc, ?_⟩
  rcases mem_mk_false.1 hf with h | ⟨i, hi, ks, m, hs, hg, hm⟩
  · left
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
  · right
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
      refine ⟨m, hmn, restKid_eq.2 ⟨d, ex, hd, hr⟩, ts[i], ?_, hm⟩
      have hkid := hall i hi
      rwa [kidC_of_rest hkc hacc hi] at hkid

/-! ## The terms of `G` with a root -/

/-- The arguments, but perhaps for one, are the one member each of the sorts
`c` requires of them. -/
def Ones (S : Sorts) (c : Conj) (f : Sym) (skip : Option Nat) (args : List GTerm) : Prop :=
  ∀ j (h : j < args.length), some j ≠ skip →
    count S (kidC S c f args.length j) = .one args[j]

instance (S : Sorts) (c : Conj) (f : Sym) (skip : Option Nat) (args : List GTerm) :
    Decidable (Ones S c f skip args) := by unfold Ones; infer_instance

/-- A term of `G` with root `f` and `k` arguments is the one member of `c`
with that root. -/
def onlyIn (S : Sorts) (c : Conj) (f : Sym) (k : Nat) (G : List GTerm) : Bool :=
  G.any fun g =>
    match g.spine with
    | some (f', args) => decide (f' = f ∧ args.length = k ∧ Ones S c f none args)
    | none => false

theorem onlyIn_iff {c : Conj} {f : Sym} {k : Nat} {G : List GTerm} :
    onlyIn S c f k G = true ↔
      ∃ args, Term.mk f args ∈ G ∧ args.length = k ∧ Ones S c f none args := by
  simp only [onlyIn, List.any_eq_true]
  constructor
  · rintro ⟨g, hg, h⟩
    obtain ⟨f', args, rfl, -⟩ := exists_mk g
    simp only [Term.spine_mk, decide_eq_true_eq] at h
    obtain ⟨rfl, hl, ho⟩ := h
    exact ⟨args, hg, hl, ho⟩
  · rintro ⟨args, hg, hl, ho⟩
    exact ⟨_, hg, by simp [Term.spine_mk, hl, ho]⟩

/-- Argument `i` of the terms of `G` with root `f` and `k` arguments whose
other arguments are the one member each of their sorts. -/
def proj (S : Sorts) (c : Conj) (f : Sym) (k i : Nat) (G : List GTerm) : List GTerm :=
  G.filterMap fun g =>
    match g.spine with
    | some (f', args) =>
      if f' = f ∧ args.length = k ∧ Ones S c f (some i) args then args[i]? else none
    | none => none

theorem mem_proj {c : Conj} {f : Sym} {k i : Nat} {G : List GTerm} {u : GTerm} :
    u ∈ proj S c f k i G ↔
      ∃ args, Term.mk f args ∈ G ∧ args.length = k ∧ Ones S c f (some i) args ∧
        args[i]? = some u := by
  simp only [proj, List.mem_filterMap]
  constructor
  · rintro ⟨g, hg, h⟩
    obtain ⟨f', args, rfl, -⟩ := exists_mk g
    simp only [Term.spine_mk] at h
    split at h
    · rename_i hc
      obtain ⟨rfl, hl, ho⟩ := hc
      exact ⟨args, hg, hl, ho, h⟩
    · cases h
  · rintro ⟨args, hg, hl, ho, hi⟩
    exact ⟨_, hg, by simp [Term.spine_mk, hl, ho, hi]⟩

/-- The sizes of the terms of a list, added. -/
def sumSize (G : List GTerm) : Nat := (G.map Term.size).sum

theorem size_pos (g : GTerm) : 0 < g.size := by cases g <;> simp [Term.size]

theorem proj_le (c : Conj) (f : Sym) (k i : Nat) : ∀ G : List GTerm,
    sumSize (proj S c f k i G) + G.length ≤ sumSize G
  | [] => by simp [proj, sumSize]
  | g :: G => by
    have ih := proj_le c f k i G
    obtain ⟨f', args, rfl, -⟩ := exists_mk g
    simp only [proj, sumSize, List.filterMap_cons, Term.spine_mk, List.map_cons, List.sum_cons,
      List.length_cons] at ih ⊢
    have hp := size_pos (Term.mk f' args)
    split
    · rename_i hn
      omega
    · rename_i u hu
      split at hu
      · have := size_lt_mk (f := f') (List.mem_of_getElem? hu)
        simp only [List.map_cons, List.sum_cons]
        omega
      · cases hu

theorem proj_lt (c : Conj) (f : Sym) (k i : Nat) {G : List GTerm} (h : G ≠ []) :
    sumSize (proj S c f k i G) < sumSize G := by
  have := proj_le (S := S) c f k i G
  have : 0 < G.length := List.length_pos_iff.2 h
  omega

/-! ## The decision -/

/-- Is every member of `c` that is not in `G` in `n`? -/
def inclBut (S : Sorts) (c : Conj) (n : Name) (G : List GTerm) : Bool :=
  if _ : G = [] then decide (Incl S c n)
  else
    let L := live S
    decide (¬ FreshOut S c n) &&
    decide (∀ key ∈ caseKeys S c ∪ caseKeys S {n} ∪ exKeys S n ∪ (G.filterMap Term.key).toFinset,
      (!decide (LiveKey S L c key) ||
        match step S n key.1 key.2 with
        | none => onlyIn S c key.1 key.2 G
        | some ks =>
          (List.range key.2).all fun i =>
            match ks[i]? with
            | some (some m) =>
              inclBut S (kidC S c key.1 key.2 i) m (proj S c key.1 key.2 i G)
            | _ => true) = true)
termination_by sumSize G
decreasing_by all_goals exact proj_lt _ _ _ _ (by assumption)

/-- Infinitely many terms are not all sent into a list by an injection. -/
theorem exists_avoid {d : Conj} (hinf : {u | MemC S d u}.Infinite) (G : List GTerm)
    (F : GTerm → GTerm) (hF : Injective F) : ∃ u, MemC S d u ∧ F u ∉ G := by
  by_contra hno
  push Not at hno
  exact hinf ((Set.Finite.preimage hF.injOn (List.finite_toSet G)).subset fun u hu => hno u hu)

theorem ofFn_update_injective {k : Nat} (f : Sym) (w : Fin k → GTerm) (i : Fin k) :
    Injective fun u : GTerm => Term.mk f (List.ofFn (update w i u)) := by
  intro u₁ u₂ e
  have := congrFun (List.ofFn_injective (Term.mk_inj e).2) i
  simpa using this

theorem memC_update {c : Conj} {f : Sym} {k : Nat} {w : Fin k → GTerm}
    (hw : ∀ j : Fin k, MemC S (kidC S c f k j) (w j)) (i : Fin k) {u : GTerm}
    (hu : MemC S (kidC S c f k i) u) : ∀ j : Fin k, MemC S (kidC S c f k j) (update w i u j) := by
  intro j
  by_cases e : j = i
  · subst e; simpa using hu
  · rw [update_of_ne e]; exact hw j

theorem inclBut_iff (hS : S.WellFormed) : ∀ (G : List GTerm) (c : Conj) (n : Name),
    inclBut S c n G = true ↔ ∀ t, MemC S c t → mem S n t = false → t ∈ G := by
  intro G
  induction hsz : sumSize G using Nat.strong_induction_on generalizing G with
  | _ sz ih =>
    intro c n
    rw [inclBut]
    split
    · rename_i hG
      subst hG
      rw [decide_eq_true_eq]
      constructor
      · intro h t ht hf
        rw [h t ht] at hf; cases hf
      · intro h t ht
        by_contra hne
        exact absurd (h t ht (by simpa using hne)) (by simp)
    · rename_i hG
      have IH : ∀ f k i m, inclBut S (kidC S c f k i) m (proj S c f k i G) = true ↔
          ∀ t, MemC S (kidC S c f k i) t → mem S m t = false → t ∈ proj S c f k i G :=
        fun f k i m => ih _ (by subst hsz; exact proj_lt _ _ _ _ hG) _ rfl _ _
      have hmany : ∀ {d : Conj} {u : GTerm}, MemC S d u → (∀ v, count S d ≠ .one v) →
          {u | MemC S d u}.Infinite := by
        intro d u hu hne
        cases hc : count S d with
        | none => exact absurd ⟨u, hu⟩ (count_none.1 hc)
        | one v => exact absurd hc (hne v)
        | many => exact count_many_infinite hS hc
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨hfresh, hkeys⟩ t ht hf
        obtain ⟨f, ts, rfl, -⟩ := exists_mk t
        by_cases hk : (f, ts.length) ∈ caseKeys S c ∪ caseKeys S {n} ∪ exKeys S n ∪
            (G.filterMap Term.key).toFinset
        · have h := hkeys _ hk
          simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
          rcases h with hnl | h
          · exact absurd (liveKey_of_memC ht) hnl
          rcases mem_mk_false.1 hf with hs | ⟨i, hi, ks, m, hs, hg, hm⟩
          · simp only [hs] at h
            obtain ⟨args, hmem, hlen, hones⟩ := onlyIn_iff.1 h
            have : ts = args := by
              refine List.ext_getElem hlen.symm fun j h1 h2 => ?_
              have := hones j h2 (by simp)
              rw [hlen] at this
              exact (count_one.1 this).2 _ ((memC_mk.1 ht).2 j h1)
            rw [this]; exact hmem
          · simp only [hs] at h
            rw [List.all_eq_true] at h
            have h := h i (List.mem_range.2 hi)
            simp only [hg] at h
            obtain ⟨args, hmem, hlen, hones, hi'⟩ :=
              mem_proj.1 ((IH f ts.length i m).1 h ts[i] ((memC_mk.1 ht).2 i hi) hm)
            have : ts = args := by
              refine List.ext_getElem hlen.symm fun j h1 h2 => ?_
              by_cases e : j = i
              · subst e
                rw [List.getElem?_eq_getElem h2] at hi'
                exact (Option.some.inj hi').symm
              · have := hones j h2 (by simpa using e)
                rw [hlen] at this
                exact (count_one.1 this).2 _ ((memC_mk.1 ht).2 j h1)
            rw [this]; exact hmem
        · exact absurd (freshOut_of_mem (fun h => hk (Finset.mem_union_left _ h)) ht hf) hfresh
      · intro h
        refine ⟨?_, ?_⟩
        · intro hfo
          obtain ⟨g, hg⟩ := Infinite.exists_notMem_finset
            (usedSyms S ∪ ((G.filterMap Term.key).toFinset.image Prod.fst))
          simp only [Finset.mem_union, not_or] at hg
          obtain ⟨ts, ht, hf⟩ := hfo.witness hg.1
          apply hg.2
          rw [Finset.mem_image]
          refine ⟨(g, ts.length), ?_, rfl⟩
          rw [List.mem_toFinset, List.mem_filterMap]
          exact ⟨_, h _ ht hf, by simp [Term.key, Term.spine_mk]⟩
        · rintro ⟨f, k⟩ -
          simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
          by_cases hl : LiveKey S (live S) c (f, k)
          swap
          · exact Or.inl hl
          right
          obtain ⟨w, hw⟩ := hl.fn
          cases hs : step S n f k with
          | none =>
            simp only
            rw [onlyIn_iff]
            have hout : ∀ w' : Fin k → GTerm, (∀ j : Fin k, MemC S (kidC S c f k j) (w' j)) →
                Term.mk f (List.ofFn w') ∈ G := fun w' hw' =>
              h _ (memC_ofFn hl.1 hw') (mem_mk_false.2 (Or.inl (by simpa using hs)))
            have hone : ∀ j : Fin k, ∃ u, count S (kidC S c f k j) = .one u := by
              intro j
              by_contra hne
              push Not at hne
              obtain ⟨u, hu, hnot⟩ := exists_avoid (hmany (hw j) hne) G _
                (ofFn_update_injective f w j)
              exact hnot (hout _ (memC_update hw j hu))
            choose gs hgs using hone
            refine ⟨List.ofFn gs, hout _ fun j => (count_one.1 (hgs j)).1, by simp, ?_⟩
            intro j hj _
            simp only [List.length_ofFn] at hj ⊢
            simpa using hgs ⟨j, hj⟩
          | some ks =>
            simp only
            rw [List.all_eq_true]
            intro i hi
            rw [List.mem_range] at hi
            cases hg : ks[i]? with
            | none => rfl
            | some o =>
              cases o with
              | none => rfl
              | some m =>
                simp only
                rw [IH]
                intro u hu hum
                have hw' := memC_update hw ⟨i, hi⟩ hu
                have hout : ∀ w' : Fin k → GTerm, (∀ j : Fin k, MemC S (kidC S c f k j) (w' j)) →
                    w' ⟨i, hi⟩ = u → Term.mk f (List.ofFn w') ∈ G := fun w' hw' e =>
                  h _ (memC_ofFn hl.1 hw') (mem_false_of_kid (i := i) (by simpa using hs)
                    (by simpa using hi) hg (by simpa [e] using hum))
                have hone : ∀ j : Fin k, j ≠ ⟨i, hi⟩ →
                    count S (kidC S c f k j) = .one (w j) := by
                  intro j hji
                  by_contra hne
                  have hne' : ∀ v, count S (kidC S c f k j) ≠ .one v := by
                    intro v hv
                    have e := (count_one.1 hv).2 _ (hw j)
                    rw [← e] at hv
                    exact hne hv
                  obtain ⟨v, hv, hnot⟩ := exists_avoid (hmany (hw j) hne') G _
                    (ofFn_update_injective f (update w ⟨i, hi⟩ u) j)
                  exact hnot (hout _ (memC_update hw' j hv)
                    (by rw [update_of_ne (Ne.symm hji)]; simp))
                rw [mem_proj]
                refine ⟨List.ofFn (update w ⟨i, hi⟩ u), hout _ hw' (by simp), by simp, ?_,
                  by simp [hi]⟩
                intro j hj hji
                simp only [List.length_ofFn] at hj ⊢
                have e : (⟨j, hj⟩ : Fin k) ≠ ⟨i, hi⟩ := by
                  intro e; apply hji; rw [Fin.mk.injEq] at e; rw [e]
                simpa [update_of_ne e] using hone ⟨j, hj⟩ e

end Sorts
end RwLog
