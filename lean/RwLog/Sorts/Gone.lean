/-
# The terms a variable is excluded from

An exclusion whose equations hold exactly when one variable has one ground
value excludes that variable from that term (`unitOn`, `unitOn_iff`).
`gone x v` lists the terms the exclusions `x` exclude `v` from, and no
solution gives `v` one of them (`not_mem_gone`).

When the values left to a variable have one root, replacing the variable by
that root applied to new variables keeps what the store denotes
(`expStore_den`).
-/
import RwLog.Sorts.Roots
import RwLog.Sorts.Tight

namespace RwLog
namespace Sorts

/-- The pattern as a ground term, when it has no variable. -/
def ground? : Pat → Option GTerm
  | .var _ => none
  | .sym f => some (.sym f)
  | .app a b => (ground? a).bind fun a' => (ground? b).map (.app a')

theorem ground?_bind : ∀ {p : Pat} {g : GTerm}, ground? p = some g →
    ∀ σ : Nat → GTerm, p.bind σ = g
  | .var _, _, h, _ => by simp [ground?] at h
  | .sym f, _, h, _ => by simp only [ground?, Option.some.injEq] at h; subst h; rfl
  | .app a b, g, h, σ => by
    simp only [ground?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a', ha, b', hb, rfl⟩ := h
    simp only [Term.bind_app, ground?_bind ha σ, ground?_bind hb σ]

/-- The term the exclusion `E` excludes the variable `v` from, when that is
all it says. -/
def unitOn (v : Nat) (E : Eqns Nat) : Option GTerm :=
  match solve E with
  | none => none
  | some θ => if E.vars.all (fun w => decide (w = v ∨ θ w = .var w)) then ground? (θ v) else none

theorem unitOn_iff {v : Nat} {E : Eqns Nat} {g : GTerm} (h : unitOn v E = some g)
    (σ : Nat → GTerm) : Eqns.Unifies σ E ↔ σ v = g := by
  unfold unitOn at h
  split at h
  · cases h
  · rename_i θ hθ
    split at h
    · rename_i hall
      rw [List.all_eq_true] at hall
      obtain ⟨hu, hm⟩ := solve_some hθ
      constructor
      · intro hσ
        rw [← hm σ hσ v, ground?_bind h σ]
      · intro hv p hp
        have e : ∀ q : Pat, (∀ w ∈ q.vars, w ∈ E.vars) → q.bind σ = (q.bind θ).bind σ := by
          intro q hq
          rw [Term.bind_bind]
          apply Term.bind_congr
          intro w hw
          have := hall w (hq w hw)
          rw [decide_eq_true_eq] at this
          rcases this with rfl | hw'
          · rw [ground?_bind h σ, hv]
          · rw [hw']; rfl
        have hin : ∀ w, w ∈ p.1.vars ++ p.2.vars → w ∈ E.vars := fun w hw =>
          List.mem_flatMap.2 ⟨p, hp, hw⟩
        rw [e p.1 fun w hw => hin w (List.mem_append_left _ hw),
          e p.2 fun w hw => hin w (List.mem_append_right _ hw), hu p hp]
    · cases h

/-- The terms the exclusions exclude `v` from. -/
def gone (x : List (Eqns Nat)) (v : Nat) : List GTerm := x.filterMap (unitOn v)

theorem not_mem_gone {x : List (Eqns Nat)} {σ : Nat → GTerm}
    (h : ∀ E ∈ x, ¬ Eqns.Unifies σ E) (v : Nat) : σ v ∉ gone x v := by
  intro hm
  obtain ⟨E, hE, hu⟩ := List.mem_filterMap.1 hm
  exact h E hE ((unitOn_iff hu σ).2 rfl)

/-- A variable whose values have one root is replaced by that root applied to
new variables, and the store denotes what it did. -/
theorem expStore_den {S : Sorts} {s : Store} {N v : Nat} {f : Sym} {n : Nat} (hfin : s.Fin N)
    (hv : v < N) (h : sole S (s.c v) (gone s.x v) = some (f, n)) :
    (expStore S s N v f n).Den S = s.Den S := by
  have hacc : Accepts S (s.c v) f n := by
    unfold sole at h
    split at h
    · cases h
    · have : (f, n) ∈ survivors S (s.c v) (gone s.x v) := by
        rw [only_eq_some.1 h]; exact Finset.mem_singleton_self _
      simp only [survivors, Finset.mem_filter] at this
      exact this.2.1.1
  ext g
  constructor
  · rintro ⟨σ', hσ', rfl⟩
    obtain ⟨σ, hσ, e⟩ := expStore_bwd hfin hv hacc hσ'
    exact ⟨σ, hσ, e.symm⟩
  · rintro ⟨σ, hσ, rfl⟩
    obtain ⟨gs, hg, hlen⟩ := key_eq_mk (sole_sound h (hσ.1 v) (not_mem_gone hσ.2 v))
    obtain ⟨σ', hσ', e⟩ := expStore_fwd hfin hv hσ hg hlen
    exact ⟨σ', hσ', e.symm⟩

end Sorts
end RwLog
