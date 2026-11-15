/-
# What the operations on goals return

The operations of `Rungs/Framework/Goals.lean` at the derivation kernel of a
program over a kernel that returns what a domain returns: the value of each.
A machine's own lemmas about its tables start from these.
-/
import RwLog.Rungs.Framework.Goals
import RwLog.Rungs.Framework.KernelAt
import RwLog.Rungs.Framework.Rules
import RwLog.Rungs.Framework.TraverseStd
import RwLog.Rungs.Framework.Cost
import RwLog.Lib.Maxima

namespace RwLog

namespace Goals

open Traverse

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}
  (K : Kernel R Cost) (hK : K.Refines D)

attribute [simp] over_toKernel over_view over_interval over_without over_body over_eqNode
  over_span over_leaf over_join over_meetA over_inj over_unfold

theorem sameBound_val (a b : Option R) :
    (sameBound (K := DerivationKernel.over D K hK P) a b).val = decide (a = b) := by
  at_cost K hK
  cases a <;> cases b <;> simp [sameBound, hK.eq]

theorem same_val (g h : GoalOf R Rel) :
    (same (K := DerivationKernel.over D K hK P) g h).val = decide (g = h) := by
  have hl := sameBound_val (P := P) K hK g.lb h.lb
  have hr := sameBound_val (P := P) K hK g.rb h.rb
  at_cost K hK
  obtain ⟨gl, gn, gr⟩ := g
  obtain ⟨hl', hn, hr'⟩ := h
  simp only [same, Cost.bind_val, over_eqNode, Charged.eqNode, Charged.op] at *
  by_cases e₁ : gn = hn <;> by_cases e₂ : gl = hl' <;> by_cases e₃ : gr = hr' <;>
    simp_all

/-- The position of the table of a goal is that of the first table with that
goal. -/
theorem indexFrom_val {T : Type} (goal : T → GoalOf R Rel) (g : GoalOf R Rel) :
    ∀ (ts : List T) (i : Nat),
    (indexFrom (K := DerivationKernel.over D K hK P) goal g i ts).val =
      (ts.findIdx? fun t => decide (goal t = g)).map (· + i) := by
  have hs := fun t : T => same_val (P := P) K hK (goal t) g
  at_cost K hK
  intro ts
  induction ts with
  | nil => intro i; rfl
  | cons t ts ih =>
    intro i
    simp only [indexFrom, Cost.bind_val, hs, List.findIdx?_cons]
    by_cases h : goal t = g
    · simp [h]
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, ih, Option.map_map]
      congr 1; funext j; simp only [Function.comp]; omega

/-! ## Answers of one table -/

/-- Does the first answer cover the second, by the test of the domain? -/
def covB (D : Domain R) (P : Program) (y x : Ans D P) : Bool := D.covers y.span x.span

section cover

open Answer

variable {K hK} (hL : D.Lawful P.sorts.interp)
include hL

omit [DecidableEq R] in
theorem covB_iff (y x : Ans D P) :
    covB D P y x = true ↔ den P.sorts.interp x.span ⊆ den P.sorts.interp y.span :=
  hL.covers_iff _ _

omit [DecidableEq R] in
theorem covB_refl (a : Ans D P) : covB D P a a = true := (covB_iff hL a a).2 subset_rfl

omit [DecidableEq R] in
theorem covB_trans (a b c : Ans D P) (h₁ : covB D P a b = true) (h₂ : covB D P b c = true) :
    covB D P a c = true :=
  (covB_iff hL a c).2 (((covB_iff hL b c).1 h₂).trans ((covB_iff hL a b).1 h₁))

end cover

theorem coversA_val (y x : Ans D P) :
    (coversA (K := DerivationKernel.over D K hK P) y x).val = covB D P y x := by
  at_cost K hK
  simp only [coversA, over_span, hK.covers, covB]

theorem maxima_val (xs : List (Ans D P)) :
    (maxima (K := DerivationKernel.over D K hK P) xs).val = xs.maximaBy (covB D P) := by
  have hc := coversA_val (P := P) K hK
  at_cost K hK
  simp only [maxima, Cost.bind_val, filterL_std, Cost.filterL_val, anyL_std, Cost.anyL_val,
    foldL_std, Cost.foldL_val, Cost.pure_val, hc, List.maximaBy, List.thin, List.tops]
  congr 2
  · funext x
    congr 2
    funext y
    cases h : covB D P y x <;> simp [hc]

theorem fresh_val (old cands : List (Ans D P)) :
    (fresh (K := DerivationKernel.over D K hK P) old cands).val =
      (cands.filter fun c => !old.any fun t => covB D P t c).maximaBy (covB D P) := by
  have hc := coversA_val (P := P) K hK
  have hm := maxima_val (P := P) K hK
  at_cost K hK
  simp only [fresh, Cost.bind_val, filterL_std, Cost.filterL_val, anyL_std, Cost.anyL_val,
    Cost.pure_val, hc, hm]

/-! ## The rule of a split -/

/-- The node the rules `join` and `meetA` give their answer. -/
def comb : Kind → Rel → Rel → Rel
  | .seq, x, y => mkSeq (seqParts x ++ seqParts y)
  | .and, x, y => mkAnd (sortedParts (andParts x ++ andParts y))

/-- What the rule of a split returns: when it returns an answer, the span
and the goal of that answer. -/
theorem both_some {k : Kind} {x y c : Ans D P} :
    (both (K := DerivationKernel.over D K hK P) k x y).val = some c ↔
      match k with
      | .seq => JoinOk D x.span x.goal.rb y.goal.lb y.span ∧
          D.compose x.span y.span = some c.span ∧
          c.goal = ⟨x.goal.lb, comb .seq x.goal.node y.goal.node, y.goal.rb⟩
      | .and => MeetOk D x.span x.goal.lb x.goal.rb y.goal.lb y.goal.rb ∧
          D.meet x.span y.span = some c.span ∧
          c.goal = ⟨x.goal.lb, comb .and x.goal.node y.goal.node, x.goal.rb⟩ := by
  cases k
  · exact Ans.join_val K hK
  · exact Ans.meetA_val K hK

end Goals

end RwLog
