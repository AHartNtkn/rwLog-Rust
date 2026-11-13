/-
# Tier 0 proofs, part 4: maxima and fresh answers

`maxima` keeps, among a list of answers, those no other member strictly
covers, one per class of equivalent answers; `fresh` filters out the answers
an old answer covers first. Every member of the list is covered by a kept one
(strict coverage has no infinite chains in a finite list), and the kept ones
never cover a later one.
-/
import RwLog.Rungs.R001.Proofs.Kernel

namespace RwLog

namespace R001

namespace Tier0

theorem countP_lt {α : Type} {p q : α → Bool} :
    ∀ {l : List α}, (∀ z ∈ l, p z = true → q z = true) → (∃ z ∈ l, q z = true ∧ p z = false) →
      l.countP p < l.countP q
  | [], _, ⟨_, hz, _⟩ => absurd hz List.not_mem_nil
  | a :: l, hpq, ⟨z, hz, hq, hp⟩ => by
    simp only [List.countP_cons]
    have hle : l.countP p ≤ l.countP q :=
      List.countP_mono_left fun x hx => hpq x (List.mem_cons_of_mem a hx)
    rcases List.mem_cons.1 hz with rfl | hz
    · simp only [hp, hq]; simp; omega
    · have ih := countP_lt (fun x hx => hpq x (List.mem_cons_of_mem a hx)) ⟨z, hz, hq, hp⟩
      have := hpq a List.mem_cons_self
      cases hpa : p a <;> cases hqa : q a <;> simp_all; omega

/-- The members of a list that no other member strictly covers. -/
def topOf (xs : List Span) : List Span :=
  xs.filter fun x => !xs.any fun y => y.covers? x && !x.covers? y

theorem top_cover (xs : List Span) : ∀ n, ∀ x ∈ xs, xs.countP (·.covers? x) ≤ n →
    ∃ t ∈ topOf xs, t.covers? x = true
  | n, x, hx, hn => by
    by_cases ht : x ∈ topOf xs
    · exact ⟨x, ht, covers?_refl x⟩
    · have ht' : ∃ y ∈ xs, y.covers? x = true ∧ x.covers? y = false := by
        by_contra hne
        apply ht
        refine List.mem_filter.2 ⟨hx, ?_⟩
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false, Bool.and_eq_true]
        intro y hy hyx
        cases hxy : x.covers? y
        · exact absurd ⟨y, hy, hyx.1, hxy⟩ hne
        · simp_all
      obtain ⟨y, hy, hyx, hxy⟩ := ht'
      have hlt : xs.countP (·.covers? y) < xs.countP (·.covers? x) :=
        countP_lt (fun z _ hz => covers?_trans hz hyx) ⟨x, hx, covers?_refl x, hxy⟩
      cases n with
      | zero => omega
      | succ n =>
        obtain ⟨t, htop, hty⟩ := top_cover xs n y hy (by omega)
        exact ⟨t, htop, covers?_trans hty hyx⟩

theorem fold_spec (l : List Span) : ∀ acc : List Span,
    let r := l.foldl (fun acc x => if acc.any fun y => y.covers? x then acc else acc ++ [x]) acc
    (∀ y ∈ acc, y ∈ r) ∧ (∀ t ∈ l, ∃ y ∈ r, y.covers? t = true) ∧ (∀ y ∈ r, y ∈ acc ∨ y ∈ l) ∧
      (acc.Pairwise (fun a b => a.covers? b = false) → r.Pairwise (fun a b => a.covers? b = false)) := by
  induction l with
  | nil => intro acc; simp
  | cons x l ih =>
    intro acc
    simp only [List.foldl_cons]
    split
    · rename_i hc
      obtain ⟨h1, h2, h3, h4⟩ := ih acc
      refine ⟨h1, ?_, fun y hy => (h3 y hy).elim .inl (fun h => .inr (List.mem_cons_of_mem x h)), h4⟩
      intro t ht
      rcases List.mem_cons.1 ht with rfl | ht
      · obtain ⟨y, hy, hyt⟩ := List.any_eq_true.1 hc
        exact ⟨y, h1 y hy, hyt⟩
      · exact h2 t ht
    · rename_i hc
      obtain ⟨h1, h2, h3, h4⟩ := ih (acc ++ [x])
      refine ⟨fun y hy => h1 y (List.mem_append_left _ hy), ?_, ?_, ?_⟩
      · intro t ht
        rcases List.mem_cons.1 ht with rfl | ht
        · exact ⟨t, h1 t (by simp), covers?_refl t⟩
        · exact h2 t ht
      · intro y hy
        rcases h3 y hy with h | h
        · rcases List.mem_append.1 h with h | h
          · exact .inl h
          · simp at h; subst h; exact .inr List.mem_cons_self
        · exact .inr (List.mem_cons_of_mem x h)
      · intro hp
        apply h4
        rw [List.pairwise_append]
        refine ⟨hp, by simp, fun a ha b hb => ?_⟩
        simp at hb; subst hb
        simp only [List.any_eq_true, not_exists, not_and, Bool.not_eq_true] at hc
        exact hc a ha

theorem maxima_sub {xs : List Span} {y : Span} (h : y ∈ maxima xs) : y ∈ xs := by
  obtain ⟨-, -, h3, -⟩ := fold_spec (topOf xs) []
  rcases h3 y h with h | h
  · simp at h
  · exact (List.mem_filter.1 h).1

theorem maxima_cover {xs : List Span} {x : Span} (hx : x ∈ xs) : ∃ y ∈ maxima xs, y.Covers x := by
  obtain ⟨t, ht, htx⟩ := top_cover xs _ x hx le_rfl
  obtain ⟨-, h2, -, -⟩ := fold_spec (topOf xs) []
  obtain ⟨y, hy, hyt⟩ := h2 t ht
  exact ⟨y, hy, covers?_sound (covers?_trans hyt htx)⟩

theorem maxima_pairwise (xs : List Span) :
    (maxima xs).Pairwise (fun a b => a.covers? b = false) :=
  (fold_spec (topOf xs) []).2.2.2 List.Pairwise.nil

theorem maxima_nil : maxima [] = [] := rfl

theorem fresh_nil (old : List Span) : fresh old [] = [] := rfl

theorem fresh_sub {old cands : List Span} {y : Span} (h : y ∈ fresh old cands) :
    y ∈ cands ∧ ∀ t ∈ old, t.covers? y = false := by
  have h' := List.mem_filter.1 (maxima_sub h)
  refine ⟨h'.1, fun t ht => ?_⟩
  have := h'.2
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false, Bool.not_eq_true] at this
  exact this t ht

/-- Every candidate is covered by an old answer or by a fresh one. -/
theorem fresh_cover {old cands : List Span} {c : Span} (hc : c ∈ cands) :
    ∃ y ∈ old ++ fresh old cands, y.Covers c := by
  by_cases ho : (old.any fun t => t.covers? c) = true
  · obtain ⟨t, ht, htc⟩ := List.any_eq_true.1 ho
    exact ⟨t, List.mem_append_left _ ht, covers?_sound htc⟩
  · obtain ⟨y, hy, hyc⟩ := maxima_cover (xs := cands.filter fun c => !old.any fun t => t.covers? c)
      (List.mem_filter.2 ⟨hc, by simpa using ho⟩)
    exact ⟨y, List.mem_append_right _ hy, hyc⟩

theorem fresh_pairwise (old cands : List Span) :
    (fresh old cands).Pairwise (fun a b => a.covers? b = false) := maxima_pairwise _

end Tier0

end R001

end RwLog
