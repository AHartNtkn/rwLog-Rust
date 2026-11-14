/-
# Inclusion on the pairs a pair reaches

`outs S` saturates over every set of names with every name. To decide whether
one conjunction `c` has a member outside one sort `n` it is enough to look at
the pairs `(c, n)` *reaches* (`ReachOut`): the conjunction of an argument of a
root with the sort `n` requires there, and the sorts the rests of `c` require
with the sort the rest of `n` requires. `out_iff_of_stable` says that on those
pairs a marking that is sound and that no round extends marks exactly the
pairs whose conjunction has a member outside the sort.
-/
import RwLog.Sorts.Incl
import RwLog.Sorts.WF
import RwLog.Sorts.Reach

namespace RwLog
namespace Sorts

variable {S : Sorts}

/-- What a round of `growOut` asks of a pair, given that the conjunctions in
`L` have a member and the pairs in `P` a member outside. -/
def GrowsOut (S : Sorts) (L : Conj → Prop) (P : Conj → Name → Prop) (c : Conj) (n : Name) :
    Prop :=
  (RestOK S c ∧ ((S.lookup n).bind (·.rest)).isSome = false) ∨
  (RestOK S c ∧ ∃ m, restKid S n = some m ∧ P (restKids S c) m) ∨
  ∃ key ∈ caseKeys S c ∪ caseKeys S {n} ∪ exKeys S n,
    Accepts S c key.1 key.2 ∧ (∀ i < key.2, L (kidC S c key.1 key.2 i)) ∧
      ((step S n key.1 key.2).isSome = false ∨
        ∃ i < key.2, ∃ m, (step S n key.1 key.2).bind (·[i]?) = some (some m) ∧
          P (kidC S c key.1 key.2 i) m)

/-- The pair `(d, m)` is reached from the pair `(c, n)` in one step. -/
def KidOut (S : Sorts) (c : Conj) (n : Name) (d : Conj) (m : Name) : Prop :=
  (RestOK S c ∧ restKid S n = some m ∧ d = restKids S c) ∨
  ∃ key ∈ caseKeys S c ∪ caseKeys S {n} ∪ exKeys S n, Accepts S c key.1 key.2 ∧
    ∃ i < key.2, (step S n key.1 key.2).bind (·[i]?) = some (some m) ∧
      d = kidC S c key.1 key.2 i

/-- The pairs a pair reaches. -/
inductive ReachOut (S : Sorts) (c : Conj) (n : Name) : Conj → Name → Prop
  | refl : ReachOut S c n c n
  | step {d e : Conj} {m k : Name} : ReachOut S c n d m → KidOut S d m e k → ReachOut S c n e k

/-- A pair a round adds has a member of the conjunction outside the sort. -/
theorem out_of_growsOut {c : Conj} {n : Name}
    (h : GrowsOut S (fun d => ∃ t, MemC S d t) (Out S) c n) : Out S c n := by
  obtain ⟨g, hg⟩ := Infinite.exists_notMem_finset (usedSyms S)
  have gacc : RestOK S c → ∀ k, Accepts S c g k := fun hr k => accepts_fresh hg hr k
  rcases h with ⟨hr, hn⟩ | ⟨hr, m, hm, hp⟩ | ⟨key, _, hacc, hlive, hn⟩
  · refine ⟨Term.mk g [], memC_mk.mpr ⟨gacc hr 0, by simp⟩, ?_⟩
    by_contra h
    rw [Bool.not_eq_false] at h
    obtain ⟨ks, hs, _⟩ := mem_mk.mp h
    obtain ⟨d, hd, hcase⟩ := step_cases hs
    rcases hcase with ⟨cs, hcs, h1, _⟩ | ⟨_, ex, r, hr', _⟩
    · exact fresh_not_case hg hd cs hcs h1
    · simp [hd, hr'] at hn
  · obtain ⟨d, ex, hd, hn⟩ := restKid_eq.1 hm
    obtain ⟨w, hw, hwm⟩ := hp
    refine ⟨Term.mk g [w], memC_mk.mpr ⟨gacc hr 1, ?_⟩, ?_⟩
    · intro i hi
      simp only [List.length_singleton] at hi ⊢
      have : i = 0 := by omega
      subst this
      rw [kidC_of_rest (fresh_not_caseKey hg c 1) (gacc hr 1) (by omega)]
      simpa using hw
    · exact mem_false_of_kid (ts := [w]) (i := 0) (m := m) (step_fresh hg 1 hd hn)
        (by simp) (by simp) (by simpa using hwm)
  · obtain ⟨f, k⟩ := key
    simp only at hacc hlive hn
    have : Nonempty GTerm := ⟨Term.sym ""⟩
    choose! w hw using hlive
    rcases hn with hn | ⟨i, hi, m, hsk, hp⟩
    · refine ⟨Term.mk f (List.ofFn fun j : Fin k => w j), memC_mk.mpr ⟨by simpa using hacc, ?_⟩, ?_⟩
      · intro j hj
        simp only [List.length_ofFn] at hj ⊢
        simpa using hw j hj
      · by_contra h
        rw [Bool.not_eq_false] at h
        obtain ⟨ks, hs, _⟩ := mem_mk.mp h
        simp only [List.length_ofFn] at hs
        simp [hs] at hn
    · obtain ⟨ks, hs, hg'⟩ := stepKid_eq.1 hsk
      obtain ⟨u, hu, hum⟩ := hp
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

/-- A pair with a member of the conjunction outside the sort is added by a
round, when the pairs it reaches in one step through that member are in `P`. -/
theorem growsOut_of_out {c : Conj} {n : Name} {f : Sym} {ts : List GTerm}
    (ht : MemC S c (Term.mk f ts)) (htn : mem S n (Term.mk f ts) = false)
    (P : Conj → Name → Prop)
    (hP : ∀ d m i (hi : i < ts.length), KidOut S c n d m → MemC S d ts[i] →
      mem S m ts[i] = false → P d m) :
    GrowsOut S (fun d => ∃ t, MemC S d t) P c n := by
  obtain ⟨hacc, hall⟩ := memC_mk.mp ht
  have hwhy : (step S n f ts.length).isSome = false ∨
      ∃ i, ∃ _ : i < ts.length, ∃ ks m, step S n f ts.length = some ks ∧
        ks[i]? = some (some m) ∧ mem S m ts[i] = false := by
    rcases mem_mk_false.1 htn with h | h
    · exact Or.inl (by simp [h])
    · exact Or.inr h
  by_cases hkey : (f, ts.length) ∈ caseKeys S c ∪ caseKeys S {n} ∪ exKeys S n
  · right; right
    refine ⟨(f, ts.length), hkey, hacc, fun i hi => ⟨_, hall i hi⟩, ?_⟩
    rcases hwhy with h | ⟨i, hi, ks, m, hs, hg, hm⟩
    · exact Or.inl h
    · right
      have hsk : (step S n f ts.length).bind (·[i]?) = some (some m) := stepKid_eq.2 ⟨ks, hs, hg⟩
      exact ⟨i, hi, m, hsk, hP _ m i hi
        (Or.inr ⟨(f, ts.length), hkey, hacc, i, hi, hsk, rfl⟩) (hall i hi) hm⟩
  · simp only [Finset.mem_union, not_or] at hkey
    obtain ⟨⟨hkc, hkn⟩, hke⟩ := hkey
    have hrest : RestOK S c := restOK_of_not_caseKey hacc hkc
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
        have hrk : restKid S n = some m := restKid_eq.2 ⟨d, ex, hd, hr⟩
        have hkid := hall i hi
        rw [kidC_of_rest hkc hacc hi] at hkid
        exact ⟨hrest, m, hrk, hP _ m i hi (Or.inl ⟨hrest, hrk, rfl⟩) hkid hm⟩

/-- On a set of pairs closed under reaching, a marking that no round extends
marks every pair of the set whose conjunction has a member outside the
sort. -/
theorem out_of_stable {R P : Conj → Name → Prop}
    (hclosed : ∀ c n d m, R c n → KidOut S c n d m → R d m)
    (hstable : ∀ c n, R c n → GrowsOut S (fun d => ∃ t, MemC S d t) P c n → P c n) :
    ∀ c n, R c n → Out S c n → P c n := by
  intro c n hc ⟨t, ht, htn⟩
  induction hsz : t.size using Nat.strong_induction_on generalizing c n t with
  | _ sz ih =>
    obtain ⟨f, ts, rfl, hlt⟩ := exists_mk t
    refine hstable c n hc (growsOut_of_out ht htn P fun d m i hi hk hd hm => ?_)
    exact ih _ (by subst hsz; exact hlt _ (List.getElem_mem hi)) d m (hclosed c n d m hc hk) _
      hd hm rfl

/-- The same, for the pairs one pair reaches. -/
theorem out_iff_of_stable {c₀ : Conj} {n₀ : Name} {P : Conj → Name → Prop}
    (hsound : ∀ c n, P c n → Out S c n)
    (hstable : ∀ c n, ReachOut S c₀ n₀ c n →
      GrowsOut S (fun d => ∃ t, MemC S d t) P c n → P c n) :
    P c₀ n₀ ↔ Out S c₀ n₀ :=
  ⟨hsound c₀ n₀, out_of_stable (R := ReachOut S c₀ n₀) (fun _ _ _ _ h k => h.step k) hstable
    c₀ n₀ .refl⟩

theorem restKid_mem_names {n m : Name} (h : restKid S n = some m) : m ∈ names S := by
  obtain ⟨d, ex, hd, hr⟩ := restKid_eq.1 h
  simp only [names, List.mem_toFinset, List.mem_flatMap]
  refine ⟨(n, d), mem_of_lookup hd, List.mem_cons_of_mem _ ?_⟩
  simp [SortDef.kidNames, hr]

/-- A pair reached in one step is a conjunction of names with a name. -/
theorem KidOut.names {c d : Conj} {n m : Name} (h : KidOut S c n d m) :
    d ⊆ names S ∧ m ∈ names S := by
  rcases h with ⟨-, hm, rfl⟩ | ⟨key, -, -, i, -, hsk, rfl⟩
  · exact ⟨restKids_subset_names, restKid_mem_names hm⟩
  · obtain ⟨ks, hs, hg⟩ := stepKid_eq.1 hsk
    exact ⟨kidC_subset_names, kidC_subset_names (c := {n}) (i := i)
      (mem_kidC.mpr ⟨n, by simp, ks, hs, hg⟩)⟩

theorem ReachOut.eq_or_names {c d : Conj} {n m : Name} (h : ReachOut S c n d m) :
    (d = c ∧ m = n) ∨ (d ⊆ names S ∧ m ∈ names S) := by
  cases h with
  | refl => exact Or.inl ⟨rfl, rfl⟩
  | step _ hk => exact Or.inr hk.names

open Classical in
/-- The pairs a pair reaches, as a finite set. Its size is what deciding
whether a conjunction is included in a sort is charged by. -/
noncomputable def reachOutSet (S : Sorts) (c : Conj) (n : Name) : Finset (Conj × Name) :=
  (insert (c, n) ((names S).powerset ×ˢ names S)).filter fun p => ReachOut S c n p.1 p.2

theorem mem_reachOutSet {c d : Conj} {n m : Name} :
    (d, m) ∈ reachOutSet S c n ↔ ReachOut S c n d m := by
  simp only [reachOutSet, Finset.mem_filter, Finset.mem_insert, Finset.mem_product,
    Finset.mem_powerset, Prod.mk.injEq]
  exact ⟨fun h => h.2, fun h => ⟨h.eq_or_names, h⟩⟩

/-! ## Pairs and the conjunctions whose members they ask for, together

Whether a pair is out asks whether argument conjunctions have a member. A
*key* is a conjunction with a sort, or with none: with none it asks whether
the conjunction has a member. One marking of the keys a key reaches, sound
and that no round extends, answers both. -/

/-- A conjunction with a sort, or with none. -/
abbrev OutKey := Conj × Option Name

/-- The roots a round looks at for a key. -/
def keysOf (S : Sorts) : OutKey → Finset (Sym × Nat)
  | (c, none) => caseKeys S c
  | (c, some n) => caseKeys S c ∪ caseKeys S {n} ∪ exKeys S n

/-- The key `q` is reached from the key `p` in one step: an argument
conjunction of a root of `p`, with no sort, or a pair reached from a pair. -/
def KidG (S : Sorts) (p q : OutKey) : Prop :=
  (∃ key ∈ keysOf S p, Accepts S p.1 key.1 key.2 ∧
      ∃ i < key.2, q = (kidC S p.1 key.1 key.2 i, none)) ∨
    ∃ n m, p.2 = some n ∧ q.2 = some m ∧ KidOut S p.1 n q.1 m

/-- The keys a key reaches. -/
inductive ReachG (S : Sorts) (p : OutKey) : OutKey → Prop
  | refl : ReachG S p p
  | step {q r : OutKey} : ReachG S p q → KidG S q r → ReachG S p r

/-- What a key asks: a member, or a member outside the sort. -/
def TrueG (S : Sorts) : OutKey → Prop
  | (c, none) => ∃ t, MemC S c t
  | (c, some n) => Out S c n

/-- What a round asks of a key, given the keys in `M`. -/
def GrowsG (S : Sorts) (M : OutKey → Prop) : OutKey → Prop
  | (c, none) => Grows S (fun d => M (d, none)) c
  | (c, some n) => GrowsOut S (fun d => M (d, none)) (fun d m => M (d, some m)) c n

theorem Grows.mono {L L' : Conj → Prop} {c : Conj} (h : Grows S L c)
    (hL : ∀ key ∈ caseKeys S c, Accepts S c key.1 key.2 → ∀ i < key.2,
      L (kidC S c key.1 key.2 i) → L' (kidC S c key.1 key.2 i)) : Grows S L' c := by
  rcases h with h | ⟨key, hk, hacc, hall⟩
  · exact Or.inl h
  · exact Or.inr ⟨key, hk, hacc, fun i hi => hL key hk hacc i hi (hall i hi)⟩

theorem GrowsOut.mono {L L' : Conj → Prop} {P P' : Conj → Name → Prop} {c : Conj} {n : Name}
    (h : GrowsOut S L P c n)
    (hL : ∀ key ∈ caseKeys S c ∪ caseKeys S {n} ∪ exKeys S n, Accepts S c key.1 key.2 →
      ∀ i < key.2, L (kidC S c key.1 key.2 i) → L' (kidC S c key.1 key.2 i))
    (hP : ∀ d m, KidOut S c n d m → P d m → P' d m) : GrowsOut S L' P' c n := by
  rcases h with h | ⟨hr, m, hm, hp⟩ | ⟨key, hk, hacc, hall, hn⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨hr, m, hm, hP _ m (Or.inl ⟨hr, hm, rfl⟩) hp⟩)
  · refine Or.inr (Or.inr ⟨key, hk, hacc, fun i hi => hL key hk hacc i hi (hall i hi), ?_⟩)
    rcases hn with hn | ⟨i, hi, m, hsk, hp⟩
    · exact Or.inl hn
    · exact Or.inr ⟨i, hi, m, hsk, hP _ m (Or.inr ⟨key, hk, hacc, i, hi, hsk, rfl⟩) hp⟩

/-- A key a round adds to keys that hold, holds. -/
theorem trueG_of_growsG {M : OutKey → Prop} (hM : ∀ q, M q → TrueG S q) {p : OutKey}
    (h : GrowsG S M p) : TrueG S p := by
  obtain ⟨c, k⟩ := p
  cases k with
  | none =>
    have h' : Grows S (fun d => M (d, none)) c := h
    exact memC_of_grows (Grows.mono h' fun _ _ _ _ _ hl => hM (_, none) hl)
  | some n =>
    have h' : GrowsOut S (fun d => M (d, none)) (fun d m => M (d, some m)) c n := h
    exact out_of_growsOut (GrowsOut.mono h' (fun _ _ _ _ _ hl => hM (_, none) hl)
      fun _ _ _ hp => hM (_, some _) hp)

/-- On the keys a key reaches, a marking that is sound and that no round
extends marks exactly the keys that hold. -/
theorem trueG_iff_of_stable {p₀ : OutKey} {M : OutKey → Prop}
    (hsound : ∀ q, M q → TrueG S q)
    (hstable : ∀ q, ReachG S p₀ q → GrowsG S M q → M q) :
    ∀ q, ReachG S p₀ q → (M q ↔ TrueG S q) := by
  have hlive : ∀ c, ReachG S p₀ (c, none) → (∃ t, MemC S c t) → M (c, none) :=
    live_of_stable (R := fun c => ReachG S p₀ (c, none)) (L := fun c => M (c, none))
      (fun c d hc hk => by
        obtain ⟨-, key, hkey, hacc, i, hi, rfl⟩ := hk
        exact hc.step (Or.inl ⟨key, hkey, hacc, i, hi, rfl⟩))
      (fun c hc hg => hstable (c, none) hc hg)
  have hout : ∀ c n, ReachG S p₀ (c, some n) → Out S c n → M (c, some n) :=
    out_of_stable (R := fun c n => ReachG S p₀ (c, some n)) (P := fun c n => M (c, some n))
      (fun c n d m hc hk => hc.step (Or.inr ⟨n, m, rfl, rfl, hk⟩))
      (fun c n hc hg => hstable (c, some n) hc
        (show GrowsOut S (fun d => M (d, none)) (fun d m => M (d, some m)) c n from
          GrowsOut.mono hg
            (fun key hkey hacc i hi hl =>
              hlive _ (hc.step (Or.inl ⟨key, hkey, hacc, i, hi, rfl⟩)) hl)
            fun _ _ _ hp => hp))
  rintro ⟨c, k⟩ hq
  refine ⟨hsound _, ?_⟩
  cases k with
  | none => exact hlive c hq
  | some n => exact hout c n hq

theorem KidG.names {p q : OutKey} (h : KidG S p q) :
    q.1 ⊆ names S ∧ ∀ m, q.2 = some m → m ∈ names S := by
  rcases h with ⟨key, -, -, i, -, rfl⟩ | ⟨n, m, -, hm, hk⟩
  · exact ⟨kidC_subset_names, fun m h => by cases h⟩
  · refine ⟨hk.names.1, fun m' h => ?_⟩
    rw [hm] at h
    cases h
    exact hk.names.2

theorem ReachG.eq_or_names {p q : OutKey} (h : ReachG S p q) :
    q = p ∨ (q.1 ⊆ names S ∧ ∀ m, q.2 = some m → m ∈ names S) := by
  cases h with
  | refl => exact Or.inl rfl
  | step _ hk => exact Or.inr hk.names

open Classical in
/-- The keys a key reaches, as a finite set. Its size is what deciding
whether a conjunction is included in a sort is charged by. -/
noncomputable def reachGSet (S : Sorts) (p : OutKey) : Finset OutKey :=
  (insert p ((names S).powerset ×ˢ insert none ((names S).image some))).filter (ReachG S p)

theorem mem_reachGSet {p q : OutKey} : q ∈ reachGSet S p ↔ ReachG S p q := by
  simp only [reachGSet, Finset.mem_filter, Finset.mem_insert, Finset.mem_product,
    Finset.mem_powerset, Finset.mem_image]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  rcases h.eq_or_names with e | ⟨h1, h2⟩
  · exact Or.inl e
  · refine Or.inr ⟨h1, ?_⟩
    cases hk : q.2 with
    | none => exact Or.inl rfl
    | some m => exact Or.inr ⟨m, h2 m hk, rfl⟩

end Sorts
end RwLog
