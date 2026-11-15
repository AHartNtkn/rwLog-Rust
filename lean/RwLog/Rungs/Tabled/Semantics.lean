/-
# Which pairs the answers of a goal cover

A goal `⟨lb, node, rb⟩` of the tabled machine and a ground relation `G` its
node derives stand for the pairs of `lb ; G ; rb` (`pairsOf`). This file says
which of those pairs an answer made by a rule of the kernel covers, from the
laws of the constraint domain, and how the pairs of a chain or a meet are
made of the pairs of the two sides of a split.
-/
import RwLog.Rungs.Tabled.Candidates
import RwLog.Kernel.NormalFormSpans
import RwLog.Kernel.NormalFormSize
import RwLog.Kernel.DomainLaws
import RwLog.Kernel.Wrap
import RwLog.Rungs.Framework.Void

namespace RwLog

namespace Tabled

open Answer

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}

/-! ## Coverage, decided -/

section cover

variable (hL : D.Lawful P.sorts.interp)
include hL

variable (K : Kernel R Cost) (hK : K.Refines D)

/-- Every candidate is covered by an answer of the table or by one that
enters it. -/
theorem cov_fresh {old cands : List (Ans D P)} {X : PRel} (h : Cov cands X) :
    Cov (old ++ (fresh (K := DerivationKernel.over D K hK P) old cands).val) X := by
  obtain ⟨c, hc, hX⟩ := h
  rw [fresh_val]
  by_cases ho : (old.any fun t => covB D P t c) = true
  · obtain ⟨t, ht, htc⟩ := List.any_eq_true.1 ho
    exact ⟨t, List.mem_append_left _ ht, hX.trans ((covB_iff hL t c).1 htc)⟩
  · have hmem : c ∈ cands.filter fun c => !old.any fun t => covB D P t c := by
      rw [List.mem_filter]; exact ⟨hc, by simpa using ho⟩
    obtain ⟨z, hz, hzc⟩ := List.maximaBy_covers (covB_refl hL) (covB_trans hL) hmem
    exact ⟨z, List.mem_append_right _ hz, hX.trans ((covB_iff hL z c).1 hzc)⟩

omit hL in
/-- An answer that enters a table is a candidate that no answer of the table
covers. -/
theorem mem_fresh {old cands : List (Ans D P)} {a : Ans D P}
    (h : a ∈ (fresh (K := DerivationKernel.over D K hK P) old cands).val) :
    a ∈ cands ∧ ∀ t ∈ old, covB D P t a = false := by
  rw [fresh_val] at h
  have := List.mem_filter.1 (List.mem_maximaBy h)
  refine ⟨this.1, fun t ht => ?_⟩
  have h2 := this.2
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false] at h2
  simpa using h2 t ht

omit hL in
/-- The answers that enter a table in one round do not cover each other. -/
theorem fresh_pairwise (old cands : List (Ans D P)) :
    ((fresh (K := DerivationKernel.over D K hK P) old cands).val).Pairwise
      fun y x => covB D P y x = false ∧ covB D P x y = false := by
  rw [fresh_val]; exact List.maximaBy_pairwise _

end cover

end Tabled

end RwLog
