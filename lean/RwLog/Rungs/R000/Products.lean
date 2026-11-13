/-
# Products of the normal form are never empty

Shape facts about rung zero's `joinSeq`, `mkAnd` and `norm` that do not depend
on what the products denote: how a join comes about, and that no product of a
normal form is the empty chain.
-/
import RwLog.Rungs.R000.Normalize

namespace RwLog

namespace R000

/-- A join either fuses the two spans that meet, or appends. -/
theorem joinSeq_cases {p q r : List Rel} (h : joinSeq p q = some r) :
    (∃ a b q' c, p.getLast? = some (.span a) ∧ q = .span b :: q' ∧ a.compose b = some c ∧
      r = p.dropLast ++ .span c :: q') ∨ r = p ++ q := by
  unfold joinSeq at h
  split at h
  · rename_i a b q' hl
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
    exact .inl ⟨a, b, q', c, hl, rfl, hc, rfl⟩
  · cases h
    exact .inr rfl

theorem joinSeq_ne_nil {p q r : List Rel} (h : joinSeq p q = some r) (hp : p ≠ []) : r ≠ [] := by
  rcases joinSeq_cases h with ⟨a, b, q', c, -, -, -, rfl⟩ | rfl
  · simp
  · simp [hp]

theorem mkAnd_ne_nil {p q r : List Rel} (h : mkAnd p q = some r) : r ≠ [] := by
  unfold mkAnd at h
  split at h
  · obtain ⟨c, -, rfl⟩ := Option.map_eq_some_iff.mp h
    simp
  · cases h
    simp

/-- No product of a normal form is the empty chain. -/
theorem norm_ne_nil : ∀ (e : Rel) (neg : Bool), ∀ p ∈ norm neg e, p ≠ [] := by
  intro e
  induction e with
  | zero => intro neg p hp; simp [norm] at hp
  | span s => intro neg p hp; simp only [norm, List.mem_singleton] at hp; simp [hp]
  | or a b iha ihb =>
    intro neg p hp
    simp only [norm, List.mem_append] at hp
    exact hp.elim (iha neg p) (ihb neg p)
  | and a b iha ihb =>
    intro neg r hr
    simp only [norm, List.mem_flatMap, List.mem_filterMap] at hr
    obtain ⟨p, -, q, -, hj⟩ := hr
    exact mkAnd_ne_nil hj
  | seq a b iha ihb =>
    intro neg r hr
    cases neg
    · simp only [norm, List.mem_flatMap, List.mem_filterMap] at hr
      obtain ⟨p, hp, q, -, hj⟩ := hr
      exact joinSeq_ne_nil hj (iha _ p hp)
    · simp only [norm, List.mem_flatMap, List.mem_filterMap] at hr
      obtain ⟨p, hp, q, -, hj⟩ := hr
      exact joinSeq_ne_nil hj (ihb _ p hp)
  | conv a iha => intro neg p hp; exact iha (!neg) p hp
  | call n => intro neg p hp; simp only [norm, List.mem_singleton] at hp; simp [hp]

end R000

end RwLog
