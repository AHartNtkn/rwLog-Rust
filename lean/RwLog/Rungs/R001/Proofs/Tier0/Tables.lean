/-
# Tier 0 proofs, part 11: the table invariants

From a goal with interface boundaries every table satisfies `TInv`: each
answer stands, up to the theory, for its goal's boundaries around one span the
goal's expression derives, and a complete table covers every such span. The
machine's own derivations (`GDerives`) are related to those spans by
`Lifting.toDerives` and `Lifting.toGDerives`, which need the boundaries to be
sub-identities and the answer to be live; dead answers are exempt in the
invariants themselves.
-/
import RwLog.Rungs.R001.Proofs.Tier0.Fair

namespace RwLog

namespace R001

namespace Tier0

open Lifting (LCov LEq Live PId bden W)

theorem goodG_of_interfaced {g : Goal} (h : g.Interfaced) : GoodG g := by
  obtain ⟨lb, e, rb⟩ := g
  constructor
  · cases lb with
    | none => trivial
    | some b => exact h b (by simp)
  · cases rb with
    | none => trivial
    | some b => exact h b (by simp)

theorem pid_of_goodBO {o : Option Span} (h : GoodBO o) : PId (bden o) :=
  Lifting.pid_bden fun b hb => by subst hb; exact h.1

/-- Equivalent boundaries relate the same pairs in every model, and the
second is a sub-identity when the first is. -/
theorem boundEq_leq {T : Theory} {a b : Option Span} (h : boundEq a b = true) :
    LEq T (bden a) (bden b) ∧ (PId (bden a) → PId (bden b)) := by
  cases a with
  | none => cases b with
    | none => exact ⟨LEq.refl _, id⟩
    | some _ => simp [boundEq] at h
  | some a => cases b with
    | none => simp [boundEq] at h
    | some b =>
      simp only [boundEq, Bool.and_eq_true] at h
      have hab := covers?_sound h.1
      have hba := covers?_sound h.2
      refine ⟨⟨lcov_of_covers hab, lcov_of_covers hba⟩, fun hp u v S hx => ?_⟩
      obtain ⟨⟨y1, y2, Y⟩, hy, e1, e2, -⟩ := hab _ hx
      simp only at e1 e2
      subst e1 e2
      exact hp _ _ _ hy

theorem tinv_tablesAt {P : Program} {g : Goal}
    (hwf : ∀ ρ ∈ P.theory, ρ.WellFormed) (hg : GoodG g) (n : Nat) :
    TInv P (Obligation.tablesAt P g n) := by
  unfold Obligation.tablesAt
  rcases stateAfter_cases (State.ofGoal P g) n with ⟨k, -, -, h⟩ | ⟨-, h⟩ <;> rw [h] <;>
    exact tinv_iter (st := State.ofGoal P g) hwf (tinv_ofGoal hg) _

theorem iter_eq_iterate (st : State) : ∀ k, iter st k = (fun st => (round st).1)^[k] st
  | 0 => rfl
  | k + 1 => by rw [Function.iterate_succ_apply', ← iter_eq_iterate st k]; rfl

/-- Every table of a run is some table after unconditional rounds. -/
theorem tablesAt_iter (P : Program) (g : Goal) (n : Nat) :
    ∃ k, Obligation.tablesAt P g n = (iter (State.ofGoal P g) k).tables := by
  unfold Obligation.tablesAt
  rcases stateAfter_cases (State.ofGoal P g) n with ⟨k, -, -, h⟩ | ⟨-, h⟩
  · exact ⟨k, by rw [h]⟩
  · exact ⟨n, by rw [h]⟩

end Tier0

open Tier0 Lifting

section

/-- Every answer of a table that is not dead is, up to the theory, an answer
the machine derives for the table's goal. -/
theorem table_sound : Obligation.table_sound := by
  intro P g hwf hg n t ht a ha
  have hI := tinv_tablesAt hwf (goodG_of_interfaced hg) n
  obtain ⟨s, hs, hr⟩ := hI.ref t ht a ha
  by_cases hd : a.Dead P.theory
  · exact .inl hd
  right
  have hl : Live P.theory (W t.goal.lb s.den t.goal.rb) := hr.1.1.live (not_dead_iff.1 hd)
  obtain ⟨c, hc, y, hy, h₁, h₂⟩ := toGDerives hwf hs t.goal.lb t.goal.rb hl
  have hgt := hI.good t ht
  have h₂' := h₂ (pid_of_goodBO hgt.1) (pid_of_goodBO hgt.2)
  exact ⟨y, lift_leaf hc hy, coversLive_iff.2 (hr.2.trans h₂'), coversLive_iff.2 (h₁.trans hr.1.1)⟩

/-- A complete table covers every answer the machine derives for its goal
that is not dead. -/
theorem completion_sound : Obligation.completion_sound := by
  intro P g hwf hg n t ht hd s hs
  have hI := tinv_tablesAt hwf (goodG_of_interfaced hg) n
  by_cases hdd : s.Dead P.theory
  · exact .inl hdd
  have hgt := hI.good t ht
  obtain ⟨s₀, hs₀, he⟩ :=
    toDerives hwf hs (pid_of_goodBO hgt.1) (pid_of_goodBO hgt.2) (not_dead_iff.1 hdd)
  rcases hI.comp t ht hd s₀ hs₀ with hdead | ⟨a, ha, hcov⟩
  · exact .inl (deadR_den.1 (hdead.of_dom he.2))
  · exact .inr ⟨a, ha, coversLive_iff.2 (hcov.trans he.2)⟩

/-- If rounds keep running, every answer the machine derives for a table's
goal that is not dead is eventually covered by that table. -/
theorem table_fair : Obligation.table_fair := by
  intro P g hwf hg n t ht s hs
  by_cases hdd : s.Dead P.theory
  · exact .inl hdd
  have hgG := goodG_of_interfaced hg
  set st := State.ofGoal P g
  obtain ⟨k, hk⟩ := tablesAt_iter P g n
  rw [hk] at ht
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 ht
  have hgt := (tinv_iter (st := st) hwf (tinv_ofGoal hgG) k).good _ ht
  obtain ⟨s₀, hs₀, he⟩ :=
    toDerives hwf hs (pid_of_goodBO hgt.1) (pid_of_goodBO hgt.2) (not_dead_iff.1 hdd)
  obtain ⟨w, hw⟩ := dw_of_derives hs₀
  obtain ⟨k₀, hk₀⟩ := fair (st := st) hwf (tinv_ofGoal hgG) _ k i hi w s₀ hw le_rfl
  have hkk : k ≤ max k₀ k := le_max_right _ _
  obtain ⟨hi', hdc⟩ := hk₀ (max k₀ k) (le_max_left _ _)
  obtain ⟨_, hext⟩ := iter_ext_le st hkk i hi
  rcases hdc with hdead | ⟨a, ha, hcov⟩
  · exact .inl (deadR_den.1 (hdead.of_dom he.2))
  · refine .inr ⟨max k₀ k, _, ?_, hext.1, a, ha, coversLive_iff.2 (hcov.trans he.2)⟩
    unfold Obligation.roundsAt
    rw [← iter_eq_iterate]
    exact List.getElem_mem hi'

/-- Goals that share a table derive the same answers up to the theory, apart
from dead ones. -/
theorem gderives_same : Obligation.gderives_same := by
  intro P g h hwf hg hs y hy
  by_cases hd : y.Dead P.theory
  · exact .inl hd
  right
  have hgG := goodG_of_interfaced hg
  obtain ⟨s₀, hs₀, he⟩ :=
    toDerives hwf hy (pid_of_goodBO hgG.1) (pid_of_goodBO hgG.2) (not_dead_iff.1 hd)
  simp only [Goal.same, Bool.and_eq_true, decide_eq_true_eq] at hs
  obtain ⟨⟨he', hl⟩, hr⟩ := hs
  obtain ⟨bl, pl⟩ := boundEq_leq (T := P.theory) hl
  obtain ⟨br, pr⟩ := boundEq_leq (T := P.theory) hr
  have hb : LEq P.theory (W g.lb s₀.den g.rb) (W h.lb s₀.den h.rb) :=
    bl.comp ((LEq.refl _).comp br)
  have hlive : Live P.theory (W h.lb s₀.den h.rb) := hb.2.live (he.2.live (not_dead_iff.1 hd))
  rw [he'] at hs₀
  obtain ⟨c, hc, y', hy', h₁, h₂⟩ := toGDerives hwf hs₀ h.lb h.rb hlive
  have h₂' := h₂ (pl (pid_of_goodBO hgG.1)) (pr (pid_of_goodBO hgG.2))
  exact ⟨y', lift_leaf hc hy', coversLive_iff.2 ((h₁.trans hb.2).trans he.2),
    coversLive_iff.2 ((he.1.trans hb.1).trans h₂')⟩

end

end R001

end RwLog
