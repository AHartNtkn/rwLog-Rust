/-
# Extending a solved exclusion by a binding

`ext k θ x p` is the solved exclusion `θ` with one more binding `x := p`,
substituted into the values of the others. It keeps the syntax of a normal
exclusion (`pre_ext`), and a substitution satisfies it exactly when it
satisfies `θ` and gives `x` the value of `p` (`unifies_ext`).
-/
import RwLog.Sorts.UniqueExcl
import RwLog.Sorts.FO

namespace RwLog
namespace Sorts

open Function

/-- A solved exclusion with one more binding `x := p`, substituted into the
values of the others. -/
def ext (k : Nat) (θ : Binds) (x : Nat) (p : Pat) : Binds :=
  (List.range k).filterMap fun v =>
    if v = x then some (x, p) else (θ.lookup v).map fun q => (v, q.bind (Term.single x p))

section ext

variable {k : Nat} {θ : Binds} {x : Nat} {p : Pat}

theorem mem_ext (hθ : Pre k θ) (hx : x < k) (hfree : ∀ b ∈ θ, b.1 ≠ x) {b : Nat × Pat} :
    b ∈ ext k θ x p ↔ b = (x, p) ∨ ∃ q, (b.1, q) ∈ θ ∧ b.2 = q.bind (Term.single x p) := by
  simp only [ext, List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨v, -, h⟩
    by_cases hv : v = x
    · simp only [hv, ite_true, Option.some.injEq] at h
      exact Or.inl h.symm
    · simp only [hv, ite_false, Option.map_eq_some_iff] at h
      obtain ⟨q, hq, rfl⟩ := h
      exact Or.inr ⟨q, mem_of_lookup hq, rfl⟩
  · rintro (rfl | ⟨q, hq, hb⟩)
    · exact ⟨x, hx, by simp⟩
    · refine ⟨b.1, hθ.dom (b.1, q) hq, ?_⟩
      have hne : b.1 ≠ x := hfree (b.1, q) hq
      have hl := lookup_of_sorted hθ.sorted _ hq
      simp only at hl
      simp only [hne, ite_false, hl, Option.map_some, Option.some.injEq]
      exact Prod.ext rfl hb.symm

theorem sorted_ext : (ext k θ x p).Pairwise fun a b => a.1 < b.1 := by
  refine List.Pairwise.filterMap _ ?_ List.pairwise_lt_range
  intro v w hvw b hb b' hb'
  have e : ∀ {u : Nat} {c : Nat × Pat},
      c ∈ (if u = x then some (x, p) else (θ.lookup u).map fun q => (u, q.bind (Term.single x p))) →
      c.1 = u := by
    intro u c hc
    by_cases hu : u = x
    · simp only [hu, ite_true, Option.mem_def, Option.some.injEq] at hc
      rw [← hc, hu]
    · simp only [hu, ite_false, Option.mem_def, Option.map_eq_some_iff] at hc
      obtain ⟨q, -, rfl⟩ := hc; rfl
  rw [e hb, e hb']; exact hvw

/-- Adding a binding keeps the exclusion solved. -/
theorem pre_ext (hθ : Pre k θ) (hx : x < k) (hfree : ∀ b ∈ θ, b.1 ≠ x)
    (hfo : p.firstOrder = true)
    (hvars : ∀ v ∈ p.vars, v < k ∧ v ≠ x ∧ ∀ b ∈ θ, b.1 ≠ v)
    (hlater : ∀ y, p = .var y → y < x) : Pre k (ext k θ x p) := by
  have hm := @mem_ext k θ x p hθ hx hfree
  have hkey : ∀ b ∈ ext k θ x p, b.1 = x ∨ ∃ b₀ ∈ θ, b₀.1 = b.1 := by
    intro b hb
    rcases hm.1 hb with rfl | ⟨q, hq, -⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨_, hq, rfl⟩
  have hfree' : ∀ v, v ≠ x → (∀ b ∈ θ, b.1 ≠ v) → ∀ b ∈ ext k θ x p, b.1 ≠ v := by
    intro v hvx hv b hb e
    rcases hkey b hb with h | ⟨b₀, hb₀, h⟩
    · exact hvx (e.symm.trans h)
    · exact hv b₀ hb₀ (h.trans e)
  refine ⟨sorted_ext, ?_, ?_, ?_, ?_⟩
  · intro b hb
    rcases hm.1 hb with rfl | ⟨q, hq, -⟩
    · exact hx
    · exact hθ.dom (b.1, q) hq
  · intro b hb
    rcases hm.1 hb with rfl | ⟨q, hq, hb2⟩
    · exact hfo
    · rw [hb2]
      refine Term.fo_bind (hθ.fo _ hq) fun v _ => ?_
      unfold Term.single; split
      · exact hfo
      · rfl
  · intro b hb v hv
    rcases hm.1 hb with rfl | ⟨q, hq, hb2⟩
    · exact ⟨(hvars v hv).1, hfree' v (hvars v hv).2.1 (hvars v hv).2.2⟩
    · rw [hb2] at hv
      rcases Term.vars_bind_single v hv with ⟨hvq, hvx⟩ | hvp
      · exact ⟨(hθ.ran _ hq v hvq).1, hfree' v hvx (hθ.ran _ hq v hvq).2⟩
      · exact ⟨(hvars v hvp).1, hfree' v (hvars v hvp).2.1 (hvars v hvp).2.2⟩
  · intro b hb y hy
    rcases hm.1 hb with rfl | ⟨q, hq, hb2⟩
    · exact hlater y hy
    · rw [hb2] at hy
      cases q with
      | var z =>
        have hz : z < b.1 := hθ.later _ hq z rfl
        by_cases hzx : z = x
        · subst hzx
          simp only [Term.bind_var, Term.single, ite_true] at hy
          have := hlater y hy
          omega
        · simp only [Term.bind_var, Term.single, hzx, ite_false, Term.var.injEq] at hy
          omega
      | sym f => simp at hy
      | app a c => simp at hy

/-- The extended exclusion asks for the old equations and the new one. -/
theorem unifies_ext (hθ : Pre k θ) (hx : x < k) (hfree : ∀ b ∈ θ, b.1 ≠ x) (σ : Nat → GTerm) :
    Eqns.Unifies σ (eqnsOf (ext k θ x p)) ↔
      Eqns.Unifies σ (eqnsOf θ) ∧ σ x = p.bind σ := by
  have hm := @mem_ext k θ x p hθ hx hfree
  constructor
  · intro hu
    have hxp : σ x = p.bind σ :=
      hu (Term.var x, p) (List.mem_map.2 ⟨(x, p), hm.2 (Or.inl rfl), rfl⟩)
    refine ⟨?_, hxp⟩
    intro e he
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 he
    have := hu (Term.var b.1, b.2.bind (Term.single x p))
      (List.mem_map.2 ⟨(b.1, b.2.bind (Term.single x p)), hm.2 (Or.inr ⟨b.2, hb, rfl⟩), rfl⟩)
    rw [bind_single_bind hxp] at this
    exact this
  · rintro ⟨hu, hxp⟩ e he
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 he
    rcases hm.1 hb with rfl | ⟨q, hq, hb2⟩
    · exact hxp
    · show σ b.1 = b.2.bind σ
      rw [hb2, bind_single_bind hxp]
      exact hu (Term.var b.1, q) (List.mem_map.2 ⟨(b.1, q), hq, rfl⟩)

end ext

end Sorts
end RwLog
