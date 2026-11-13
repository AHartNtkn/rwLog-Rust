/-
# What the table operations of the tabled machine return

The tabled machine (`Rungs/Tabled/Machine.lean`) at the derivation kernel of
a program over a kernel that returns what a domain returns: the value of each
operation on goals and tables.
-/
import RwLog.Rungs.Tabled.Machine
import RwLog.Rungs.Framework.KernelAt
import RwLog.Rungs.Framework.TraverseStd
import RwLog.Rungs.Framework.Cost
import RwLog.Kernel.NormalFormDepth
import RwLog.Lib.Maxima

namespace RwLog

namespace Tabled

open Traverse

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}
  (K : Kernel R Cost) (hK : K.Refines D)

/-! ## The derivation kernel, operation by operation -/

section over

variable (P)

@[simp] theorem over_toKernel : (DerivationKernel.over D K hK P).toKernel = K := rfl

@[simp] theorem over_view (n : Rel) :
    (DerivationKernel.over D K hK P).view n = Charged.viewNode n := rfl

@[simp] theorem over_interval (n : Rel) (i j : Nat) :
    (DerivationKernel.over D K hK P).interval n i j = Charged.interval n i j := rfl

@[simp] theorem over_without (n : Rel) (i : Nat) :
    (DerivationKernel.over D K hK P).without n i = Charged.without n i := rfl

@[simp] theorem over_body (n : Rel) :
    (DerivationKernel.over D K hK P).body n = Charged.body P n := rfl

@[simp] theorem over_eqNode (m n : Rel) :
    (DerivationKernel.over D K hK P).eqNode m n = Charged.eqNode m n := rfl

@[simp] theorem over_span (a : Ans D P) : (DerivationKernel.over D K hK P).span a = a.span := rfl

@[simp] theorem over_leaf (lb : Option R) (n : Rel) (rb : Option R) :
    (DerivationKernel.over D K hK P).leaf lb n rb = Ans.leaf D P K hK lb n rb := rfl

@[simp] theorem over_join (a b : Ans D P) :
    (DerivationKernel.over D K hK P).join a b = Ans.join D P K hK a b := rfl

@[simp] theorem over_meetA (a b : Ans D P) :
    (DerivationKernel.over D K hK P).meetA a b = Ans.meetA D P K hK a b := rfl

@[simp] theorem over_inj (a : Ans D P) (u : Rel) (i : Nat) :
    (DerivationKernel.over D K hK P).inj a u i = Ans.inj D P a u i := rfl

@[simp] theorem over_unfold (a : Ans D P) (c : Rel) :
    (DerivationKernel.over D K hK P).unfold a c = Ans.unfold D P a c := rfl

end over

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

/-! ## Tables -/

/-- The table of a goal: the first one with that goal. -/
def lookup (ts : List (TableOf R Rel (Ans D P))) (g : GoalOf R Rel) :
    Option (TableOf R Rel (Ans D P)) :=
  ts.find? fun t => decide (t.goal = g)

theorem findTable_val (ts : List (TableOf R Rel (Ans D P))) (g : GoalOf R Rel) :
    (findTable (K := DerivationKernel.over D K hK P) ts g).val = lookup ts g := by
  have hs := fun t : TableOf R Rel (Ans D P) => same_val (P := P) K hK t.goal g
  at_cost K hK
  simp only [findTable, findL_std, Cost.findL_val, hs, lookup]

theorem indexFrom_val (g : GoalOf R Rel) : ∀ (ts : List (TableOf R Rel (Ans D P))) (i : Nat),
    (indexFrom (K := DerivationKernel.over D K hK P) g i ts).val =
      (ts.findIdx? fun t => decide (t.goal = g)).map (· + i) := by
  have hs := fun t : TableOf R Rel (Ans D P) => same_val (P := P) K hK t.goal g
  at_cost K hK
  intro ts
  induction ts with
  | nil => intro i; rfl
  | cons t ts ih =>
    intro i
    simp only [indexFrom, Cost.bind_val, hs, List.findIdx?_cons]
    by_cases h : t.goal = g
    · simp [h]
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, ih, Option.map_map]
      congr 1; funext j; simp only [Function.comp]; omega

theorem indexOf_val (ts : List (TableOf R Rel (Ans D P))) (g : GoalOf R Rel) :
    (indexOf (K := DerivationKernel.over D K hK P) ts g).val =
      ts.findIdx? fun t => decide (t.goal = g) := by
  unfold indexOf; rw [indexFrom_val]; simp

theorem answersOf_val (ts : List (TableOf R Rel (Ans D P))) (g : GoalOf R Rel) :
    (answersOf (K := DerivationKernel.over D K hK P) ts g).val =
      match lookup ts g with
      | some t => t.answers
      | none => [] := by
  have hf := findTable_val (P := P) K hK ts g
  at_cost K hK
  simp only [answersOf, Cost.bind_val, hf, Cost.pure_val]
  cases lookup ts g <;> rfl

theorem doneOf_val (ts : List (TableOf R Rel (Ans D P))) (g : GoalOf R Rel) :
    (doneOf (K := DerivationKernel.over D K hK P) ts g).val =
      match lookup ts g with
      | some t => t.done
      | none => false := by
  have hf := findTable_val (P := P) K hK ts g
  at_cost K hK
  simp only [doneOf, Cost.bind_val, hf, Cost.pure_val]
  cases lookup ts g <;> rfl

/-! ## Answers of one table -/

/-- Does the first answer cover the second, by the test of the domain? -/
def covB (D : Domain R) (P : Program) (y x : Ans D P) : Bool := D.covers y.span x.span

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

end Tabled

end RwLog
