/-
# What the domain of sorts settles

* L09: no representative relates nothing (`Rep.live`), and an operation
  returns nothing exactly when its result relates no pair
  (`compose_eq_none_iff`, `meet_eq_none_iff`, `rep_eq_none_iff`): the test
  for a dead store is exact.
* L08: a representative mentions no variable outside its two sides, the
  sorts of each variable are among the declared ones (`Rep.no_hidden`), and
  two representatives that relate the same pairs are equal (`Rep.ext_rel`).
  So a store cannot grow on hidden variables: composing never keeps a
  variable that is in neither side of the result (`Rep.exists_comp` gives a
  representative for every composition that relates a pair).
-/
import RwLog.Sorts.Dom

namespace RwLog
namespace Sorts

variable {S : Sorts}

/-- L09. A representative relates some pair. -/
theorem Rep.live (ρ : Rep S) : (Answer.den S.interp ρ).Nonempty := ρ.rel_nonempty

/-- Composition returns nothing exactly when it relates no pair. -/
theorem compose_eq_none_iff (a b : Rep S) :
    (dom S).compose a b = none ↔ (a.1.rel S).comp (b.1.rel S) = ∅ := by
  constructor
  · exact (dom_lawful a.wf).compose_none a b
  · intro h
    cases hc : (dom S).compose a b with
    | none => rfl
    | some c =>
      have := (dom_lawful a.wf).compose_some a b c hc
      have hne := c.live
      rw [this] at hne
      exact absurd h hne.ne_empty

/-- Conjunction returns nothing exactly when it relates no pair. -/
theorem meet_eq_none_iff (a b : Rep S) :
    (dom S).meet a b = none ↔ a.1.rel S ∩ b.1.rel S = ∅ := by
  constructor
  · exact (dom_lawful a.wf).meet_none a b
  · intro h
    cases hc : (dom S).meet a b with
    | none => rfl
    | some c =>
      have := (dom_lawful a.wf).meet_some a b c hc
      have hne := c.live
      rw [this] at hne
      exact absurd h hne.ne_empty

/-- A first-order span has no representative exactly when it relates no
pair. -/
theorem rep_eq_none_iff (hS : S.WellFormed) (s : Span) (hs : s.firstOrder = true) :
    (dom S).rep s = none ↔ s.denAt S.interp = ∅ := by
  constructor
  · exact (dom_lawful hS).rep_none s hs
  · intro h
    cases hc : (dom S).rep s with
    | none => rfl
    | some c =>
      have := (dom_lawful hS).rep_some s c hc
      have hne := c.live
      rw [this] at hne
      exact absurd h hne.ne_empty

/-- L08. The variables of a representative are exactly those of its two
sides, the sorts of each are declared sorts, and every exclusion is over
those variables. -/
theorem Rep.no_hidden (ρ : Rep S) :
    (∀ v, v < ρ.1.c.length ↔ v ∈ ρ.l.vars ++ ρ.r.vars) ∧
    (∀ v, ρ.1.conj v ⊆ names S) ∧
    ∀ θ ∈ ρ.1.x, ∀ b ∈ θ, b.1 < ρ.1.c.length ∧ ∀ v ∈ b.2.vars, v < ρ.1.c.length := by
  refine ⟨fun v => ?_, fun v n hn => ?_, fun θ hθ b hb => ?_⟩
  · rw [← tpair_vars, ← ρ.t_eq]; exact (ρ.normal.len v).symm
  · by_cases hv : v < ρ.1.c.length
    · exact ((ρ.normal.up v hv n).1 hn).1
    · rw [Raw.Normal.conj_of_ge ρ.1 (Nat.le_of_not_lt hv)] at hn; simp at hn
  · have hn := ρ.normal.ex θ hθ
    exact ⟨hn.dom b hb, fun v hv => (hn.ran b hb v hv).1⟩

end Sorts
end RwLog
