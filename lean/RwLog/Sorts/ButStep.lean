/-
# Inclusion but for some terms, one root at a time

`Hold S c n G` says that every member of the conjunction `c` other than the
terms of `G` is in the sort `n`. For well-formed sorts it is what `inclBut`
decides, so it unfolds as `inclBut` does (`hold_iff`): with a term in `G`,
it holds exactly when no root outside the declarations has a member of `c`
outside `n`, and each root that matters asks what `AskKey` says. What the
roots ask again, of the arguments, is asked of terms that are smaller
together than the terms of `G` (`sum_proj_le`), so asking in any order comes
to an end.
-/
import RwLog.Sorts.InclBut

namespace RwLog
namespace Sorts

variable {S : Sorts}

/-- Every member of `c` other than the terms of `G` is in `n`. -/
def Hold (S : Sorts) (c : Conj) (n : Name) (G : List GTerm) : Prop :=
  ∀ t, MemC S c t → mem S n t = false → t ∈ G

theorem hold_nil {c : Conj} {n : Name} : Hold S c n [] ↔ Incl S c n := by
  constructor
  · intro h t ht
    by_contra hne
    exact absurd (h t ht (by simpa using hne)) (by simp)
  · intro h t ht hf
    rw [h t ht] at hf; cases hf

theorem hold_iff_inclBut (hS : S.WellFormed) (G : List GTerm) (c : Conj) (n : Name) :
    Hold S c n G ↔ inclBut S c n G = true :=
  (inclBut_iff hS G c n).symm

/-- A list with the same terms holds as much. -/
theorem Hold.congr {c : Conj} {n : Name} {G G' : List GTerm} (h : ∀ t, t ∈ G ↔ t ∈ G') :
    Hold S c n G ↔ Hold S c n G' :=
  ⟨fun hh t ht hf => (h t).1 (hh t ht hf), fun hh t ht hf => (h t).2 (hh t ht hf)⟩

/-- What a root asks: when the conjunction has a member with it, a root the
sort has no term with must have its one term in `G`, and where the sort
sorts an argument, the same is asked of the argument. -/
def AskKey (S : Sorts) (c : Conj) (n : Name) (G : List GTerm) (key : Sym × Nat) : Prop :=
  LiveKey S (live S) c key →
    match step S n key.1 key.2 with
    | none => onlyIn S c key.1 key.2 G = true
    | some ks => ∀ i < key.2, ∀ m, ks[i]? = some (some m) →
        Hold S (kidC S c key.1 key.2 i) m (proj S c key.1 key.2 i G)

/-- The roots that matter for a conjunction, a sort and terms left out. -/
def butKeys (S : Sorts) (c : Conj) (n : Name) (G : List GTerm) : Finset (Sym × Nat) :=
  caseKeys S c ∪ caseKeys S {n} ∪ exKeys S n ∪ (G.filterMap Term.key).toFinset

theorem hold_iff (hS : S.WellFormed) {G : List GTerm} (hG : G ≠ []) (c : Conj) (n : Name) :
    Hold S c n G ↔ ¬ FreshOut S c n ∧ ∀ key ∈ butKeys S c n G, AskKey S c n G key := by
  rw [hold_iff_inclBut hS, inclBut]
  simp only [hG, ↓reduceDIte, Bool.and_eq_true, decide_eq_true_eq]
  refine and_congr Iff.rfl (forall₂_congr fun key _ => ?_)
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
  unfold AskKey
  constructor
  · rintro (hnl | h) hl
    · exact absurd hl hnl
    · cases hs : step S n key.1 key.2 with
      | none => simp only [hs] at h ⊢; exact h
      | some ks =>
        simp only [hs] at h ⊢
        rw [List.all_eq_true] at h
        intro i hi m hm
        have := h i (List.mem_range.2 hi)
        simp only [hm] at this
        exact (hold_iff_inclBut hS _ _ _).2 this
  · intro h
    by_cases hl : LiveKey S (live S) c key
    · right
      have h := h hl
      cases hs : step S n key.1 key.2 with
      | none => simp only [hs] at h ⊢; exact h
      | some ks =>
        simp only [hs] at h ⊢
        rw [List.all_eq_true]
        intro i hi
        rw [List.mem_range] at hi
        cases hg : ks[i]? with
        | none => rfl
        | some o =>
          cases o with
          | none => rfl
          | some m => exact (hold_iff_inclBut hS _ _ _).1 (h i hi m hg)
    · exact Or.inl hl

/-! ## What is asked again is smaller -/

theorem size_foldl_app : ∀ (ts : List GTerm) (h : GTerm),
    (ts.foldl Term.app h).size = h.size + (ts.map Term.size).sum + ts.length
  | [], h => by simp
  | t :: ts, h => by
    simp only [List.foldl_cons, size_foldl_app ts, Term.size, List.map_cons, List.sum_cons,
      List.length_cons]
    omega

theorem size_mk (f : Sym) (ts : List GTerm) :
    (Term.mk f ts).size = 1 + (ts.map Term.size).sum + ts.length := by
  simp only [Term.mk, size_foldl_app, Term.size]

theorem sumSize_append (G G' : List GTerm) : sumSize (G ++ G') = sumSize G + sumSize G' := by
  simp [sumSize]

theorem proj_append (c : Conj) (f : Sym) (k i : Nat) (G G' : List GTerm) :
    proj S c f k i (G ++ G') = proj S c f k i G ++ proj S c f k i G' := by
  simp [proj]

/-- The sizes of what a root asks again, added over its arguments. -/
def projW (S : Sorts) (c : Conj) (G : List GTerm) (key : Sym × Nat) : Nat :=
  ((List.range key.2).map fun i => sumSize (proj S c key.1 key.2 i G)).sum

theorem projW_cons (c : Conj) (g : GTerm) (G : List GTerm) (key : Sym × Nat) :
    projW S c (g :: G) key = projW S c [g] key + projW S c G key := by
  unfold projW
  rw [← List.sum_map_add]
  refine congrArg List.sum (List.map_congr_left fun i _ => ?_)
  rw [← sumSize_append, ← proj_append]
  rfl

theorem proj_other (c : Conj) {f f' : Sym} {k : Nat} {args : List GTerm} (i : Nat)
    (h : (f, k) ≠ (f', args.length)) : proj S c f k i [Term.mk f' args] = [] := by
  have : ¬ (f' = f ∧ args.length = k ∧ Ones S c f (some i) args) := by
    rintro ⟨rfl, rfl, -⟩; exact h rfl
  simp [proj, Term.spine_mk, this]

theorem sumSize_proj_one_le (c : Conj) (f : Sym) (k i : Nat) (f' : Sym) (args : List GTerm) :
    sumSize (proj S c f k i [Term.mk f' args]) ≤ ((args.map Term.size)[i]?).getD 0 := by
  by_cases hc : f' = f ∧ args.length = k ∧ Ones S c f (some i) args
  · cases hu : args[i]? with
    | none => simp [proj, Term.spine_mk, hc, hu, sumSize]
    | some u => simp [proj, Term.spine_mk, hc, hu, sumSize]
  · simp [proj, Term.spine_mk, hc, sumSize]

theorem sum_map_le {α : Type} (f g : α → Nat) : ∀ l : List α, (∀ x ∈ l, f x ≤ g x) →
    (l.map f).sum ≤ (l.map g).sum
  | [], _ => by simp
  | a :: l, h => by
    have := sum_map_le f g l fun x hx => h x (List.mem_cons_of_mem _ hx)
    have := h a List.mem_cons_self
    simp only [List.map_cons, List.sum_cons]
    omega

theorem sum_range_getD : ∀ l : List Nat,
    ((List.range l.length).map fun i => l[i]?.getD 0).sum = l.sum
  | [] => by simp
  | a :: l => by
    have ih := sum_range_getD l
    simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
      List.sum_cons, List.getElem?_cons_zero, Option.getD_some]
    have e : ((fun i => (a :: l)[i]?.getD 0) ∘ Nat.succ) = fun i => l[i]?.getD 0 := by
      funext i; simp
    rw [e, ih]

theorem projW_one_le (c : Conj) (f' : Sym) (args : List GTerm) :
    projW S c [Term.mk f' args] (f', args.length) ≤ (args.map Term.size).sum := by
  unfold projW
  have h := sum_range_getD (args.map Term.size)
  rw [List.length_map] at h
  rw [← h]
  exact sum_map_le _ _ _ fun i _ => sumSize_proj_one_le c f' args.length i f' args

theorem projW_other (c : Conj) {key : Sym × Nat} {f' : Sym} {args : List GTerm}
    (h : key ≠ (f', args.length)) : projW S c [Term.mk f' args] key = 0 := by
  unfold projW
  rw [List.sum_eq_zero]
  intro x hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  rw [proj_other c i h]
  rfl

theorem sum_projW_one_le (c : Conj) (f' : Sym) (args : List GTerm) :
    ∀ K : List (Sym × Nat), K.Nodup →
      (K.map (projW S c [Term.mk f' args])).sum ≤ (args.map Term.size).sum
  | [], _ => by simp
  | key :: K, hK => by
    obtain ⟨hnot, hK'⟩ := List.nodup_cons.1 hK
    simp only [List.map_cons, List.sum_cons]
    by_cases e : key = (f', args.length)
    · subst e
      have h0 : (K.map (projW S c [Term.mk f' args])).sum = 0 := by
        rw [List.sum_eq_zero]
        intro x hx
        obtain ⟨k', hk', rfl⟩ := List.mem_map.1 hx
        exact projW_other c fun e' => hnot (e' ▸ hk')
      have := projW_one_le (S := S) c f' args
      omega
    · have := sum_projW_one_le c f' args K hK'
      rw [projW_other c e]
      omega

/-- What distinct roots ask again is, together, smaller than the terms left
out, by one for each of them at least. -/
theorem sum_proj_le (c : Conj) {K : List (Sym × Nat)} (hK : K.Nodup) : ∀ G : List GTerm,
    (K.map (projW S c G)).sum + G.length ≤ sumSize G
  | [] => by
    have : (K.map (projW S c [])).sum = 0 := by
      rw [List.sum_eq_zero]
      intro x hx
      obtain ⟨k', -, rfl⟩ := List.mem_map.1 hx
      simp [projW, proj, sumSize]
    simp [this, sumSize]
  | g :: G => by
    have ih := sum_proj_le c hK G
    obtain ⟨f', args, rfl, -⟩ := exists_mk g
    have h1 := sum_projW_one_le (S := S) c f' args K hK
    have h2 := size_mk f' args
    have e : (K.map (projW S c (Term.mk f' args :: G))).sum =
        (K.map (projW S c [Term.mk f' args])).sum + (K.map (projW S c G)).sum := by
      rw [← List.sum_map_add]
      exact congrArg List.sum (List.map_congr_left fun key _ => projW_cons c _ G key)
    simp only [sumSize, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    rw [e]
    omega

end Sorts
end RwLog
