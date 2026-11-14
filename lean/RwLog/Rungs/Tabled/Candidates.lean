/-
# What a goal of the tabled machine computes in a round

The candidates and the strategies of a goal (`Tabled.produce`), read at the
derivation kernel of a program over a kernel that returns what a domain
returns: which answers are candidates, by the kind of the goal's node, and
which goals each strategy depends on.
-/
import RwLog.Rungs.Tabled.Tables
import RwLog.Rungs.Framework.Rules

namespace RwLog

namespace Tabled

open Traverse

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}
  (K : Kernel R Cost) (hK : K.Refines D)

/-- The answers the goal has in the tables. -/
def ansOf (ts : List (TableOf R Rel (Ans D P))) (g : GoalOf R Rel) : List (Ans D P) :=
  match lookup ts g with
  | some t => t.answers
  | none => []

/-- The goal has a table and it is complete. -/
def isDone (ts : List (TableOf R Rel (Ans D P))) (g : GoalOf R Rel) : Bool :=
  match lookup ts g with
  | some t => t.done
  | none => false

theorem answersOf_eq (ts : List (TableOf R Rel (Ans D P))) (g : GoalOf R Rel) :
    (answersOf (K := DerivationKernel.over D K hK P) ts g).val = ansOf ts g :=
  answersOf_val K hK ts g

theorem doneOf_eq (ts : List (TableOf R Rel (Ans D P))) (g : GoalOf R Rel) :
    (doneOf (K := DerivationKernel.over D K hK P) ts g).val = isDone ts g :=
  doneOf_val K hK ts g

/-! ## Splits -/

/-- The goal pushed to the right side of a split for an answer of the left
side. -/
def pushLG (D : Domain R) (g r : GoalOf R Rel) : Kind → Ans D P → GoalOf R Rel
  | .seq, x => ⟨D.rightBound x.span, r.node, g.rb⟩
  | .and, x => ⟨D.leftBound x.span, r.node, D.rightBound x.span⟩

/-- The goal pushed to the left side of a split for an answer of the right
side. -/
def pushRG (D : Domain R) (g l : GoalOf R Rel) : Kind → Ans D P → GoalOf R Rel
  | .seq, y => ⟨g.lb, l.node, D.leftBound y.span⟩
  | .and, y => ⟨D.leftBound y.span, l.node, D.rightBound y.span⟩

theorem pushL_val (g r : GoalOf R Rel) (k : Kind) (x : Ans D P) :
    (pushL (K := DerivationKernel.over D K hK P) g r k x).val = pushLG D g r k x := by
  at_cost K hK
  cases k <;> simp [pushL, pushLG, hK.rightBound, hK.leftBound]

theorem pushR_val (g l : GoalOf R Rel) (k : Kind) (y : Ans D P) :
    (pushR (K := DerivationKernel.over D K hK P) g l k y).val = pushRG D g l k y := by
  at_cost K hK
  cases k <;> simp [pushR, pushRG, hK.rightBound, hK.leftBound]

/-- What `both` returns. -/
def bothV (k : Kind) (x y : Ans D P) : Option (Ans D P) :=
  match k with
  | .seq => (Ans.join D P K hK x y).val
  | .and => (Ans.meetA D P K hK x y).val

/-- What `fromR` returns. -/
def fromRV (k : Kind) (y x : Ans D P) : Option (Ans D P) :=
  match k with
  | .seq => (Ans.join D P K hK x y).val
  | .and => (Ans.meetA D P K hK y x).val

theorem both_val (k : Kind) (x y : Ans D P) :
    (both (K := DerivationKernel.over D K hK P) k x y).val = bothV K hK k x y := by
  cases k <;> rfl

theorem fromR_val (k : Kind) (y x : Ans D P) :
    (fromR (K := DerivationKernel.over D K hK P) k y x).val = fromRV K hK k y x := by
  cases k <;> rfl

theorem pushes_val (f : Ans D P → Cost (GoalOf R Rel)) (xs : List (Ans D P)) :
    (pushes (K := DerivationKernel.over D K hK P) f xs).val = xs.map fun x => (x, (f x).val) := by
  at_cost K hK
  simp only [pushes, mapL_std, Cost.mapL_val, Cost.bind_val, Cost.pure_val]

/-- The candidates of a split. -/
theorem mem_way (ts : List (TableOf R Rel (Ans D P))) (g : GoalOf R Rel)
    (w : Kind × GoalOf R Rel × GoalOf R Rel) (c : Ans D P) :
    c ∈ (way (K := DerivationKernel.over D K hK P) ts g w).val.1 ↔
      (∃ x ∈ ansOf ts w.2.1, ∃ y ∈ ansOf ts w.2.2, bothV K hK w.1 x y = some c) ∨
      (isDone ts w.2.1 = true ∧ ∃ x ∈ (ansOf ts w.2.1).maximaBy (covB D P),
        ∃ y ∈ ansOf ts (pushLG D g w.2.2 w.1 x), bothV K hK w.1 x y = some c) ∨
      (isDone ts w.2.2 = true ∧ ∃ y ∈ (ansOf ts w.2.2).maximaBy (covB D P),
        ∃ x ∈ ansOf ts (pushRG D g w.2.1 w.1 y), fromRV K hK w.1 y x = some c) := by
  have e₁ := answersOf_eq (P := P) K hK ts
  have e₂ := doneOf_eq (P := P) K hK ts
  have e₃ := maxima_val (P := P) K hK
  have e₄ := both_val (P := P) K hK
  have e₅ := fromR_val (P := P) K hK
  have e₆ := pushL_val (P := P) K hK
  have e₇ := pushR_val (P := P) K hK
  have e₈ := pushes_val (P := P) K hK
  at_cost K hK
  simp only [way, Cost.bind_val, e₁, e₂]
  cases hd₁ : isDone ts w.2.1 <;> cases hd₂ : isDone ts w.2.2 <;>
    simp [e₁, e₂, hd₂, e₃, e₄, e₅, e₆, e₇, e₈, flatMapL_std, filterMapL_std]

/-- The strategies of a split. -/
theorem way_strats (ts : List (TableOf R Rel (Ans D P))) (g : GoalOf R Rel)
    (w : Kind × GoalOf R Rel × GoalOf R Rel) :
    (way (K := DerivationKernel.over D K hK P) ts g w).val.2 =
      [[w.2.1, w.2.2]] ++
        (if isDone ts w.2.1 then
          [w.2.1 :: ((ansOf ts w.2.1).maximaBy (covB D P)).map (pushLG D g w.2.2 w.1)] else []) ++
        (if isDone ts w.2.2 then
          [w.2.2 :: ((ansOf ts w.2.2).maximaBy (covB D P)).map (pushRG D g w.2.1 w.1)] else []) := by
  have e₁ := answersOf_eq (P := P) K hK ts
  have e₂ := doneOf_eq (P := P) K hK ts
  have e₃ := maxima_val (P := P) K hK
  have e₆ := pushL_val (P := P) K hK
  have e₇ := pushR_val (P := P) K hK
  have e₈ := pushes_val (P := P) K hK
  at_cost K hK
  simp only [way, Cost.bind_val, e₁, e₂]
  cases hd₁ : isDone ts w.2.1 <;> cases hd₂ : isDone ts w.2.2 <;>
    simp [e₂, hd₂, e₃, e₈, e₆, e₇, Function.comp_def]

/-- The splits of a chain. -/
theorem mem_splitsOf_chain (g : GoalOf R Rel) (xs : List Rel)
    (w : Kind × GoalOf R Rel × GoalOf R Rel) :
    w ∈ (splitsOf (K := DerivationKernel.over D K hK P) g (.chain xs)).val ↔
      ∃ i ∈ seqSplits xs.length, ∃ l r, g.node.interval 0 i = some l ∧
        g.node.interval i xs.length = some r ∧ w = (.seq, ⟨g.lb, l, none⟩, ⟨none, r, g.rb⟩) := by
  at_cost K hK
  simp only [splitsOf, filterMapL_std, Cost.filterMapL_val, Cost.bind_val, Cost.pure_val,
    over_interval, Charged.interval, Charged.op, List.mem_filterMap]
  constructor
  · rintro ⟨i, hi, h⟩
    cases hl : g.node.interval 0 i <;> cases hr : g.node.interval i xs.length <;>
      simp only [hl, hr] at h <;> try cases h
    exact ⟨i, hi, _, _, hl, hr, rfl⟩
  · rintro ⟨i, hi, l, r, hl, hr, rfl⟩
    exact ⟨i, hi, by simp only [hl, hr]⟩

/-- The splits of a meet. -/
theorem mem_splitsOf_meet (g : GoalOf R Rel) (xs : List Rel)
    (w : Kind × GoalOf R Rel × GoalOf R Rel) :
    w ∈ (splitsOf (K := DerivationKernel.over D K hK P) g (.meet xs)).val ↔
      ∃ i ∈ andSplits xs.length, ∃ l r, xs[i]? = some l ∧ g.node.without i = some r ∧
        w = (.and, ⟨g.lb, l, g.rb⟩, ⟨g.lb, r, g.rb⟩) := by
  at_cost K hK
  simp only [splitsOf, filterMapL_std, Cost.filterMapL_val, Cost.bind_val, Cost.pure_val,
    over_without, Charged.without, Charged.op, List.mem_filterMap]
  constructor
  · rintro ⟨i, hi, h⟩
    cases hl : xs[i]? <;> cases hr : g.node.without i <;>
      simp only [hl, hr] at h <;> try cases h
    exact ⟨i, hi, _, _, hl, hr, rfl⟩
  · rintro ⟨i, hi, l, r, hl, hr, rfl⟩
    exact ⟨i, hi, by simp only [hl, hr]⟩

/-! ## Candidates and strategies, by the kind of the node -/

section produce

variable (ts : List (TableOf R Rel (Ans D P))) (g : GoalOf R Rel)

theorem produceTables_span (h : g.node.view.forget = .span ()) :
    (produceTables (K := DerivationKernel.over D K hK P) ts g).val =
      ((Ans.leaf D P K hK g.lb g.node g.rb).val.toList, [[]]) := by
  at_cost K hK
  simp only [produceTables, Cost.bind_val, over_view, Charged.viewNode, Charged.op, h,
    Cost.pure_val, over_leaf]

theorem produceTables_call {n : Name} {f : Bool} {b : Rel} (h : g.node.view.forget = .call n f)
    (hb : Charged.bodyOf P g.node = some b) :
    (produceTables (K := DerivationKernel.over D K hK P) ts g).val =
      ((ansOf ts ⟨g.lb, b, g.rb⟩).filterMap fun x => (Ans.unfold D P x g.node).val,
        [[⟨g.lb, b, g.rb⟩]]) := by
  have e₁ := answersOf_eq (P := P) K hK ts
  at_cost K hK
  simp only [produceTables, Cost.bind_val, over_view, Charged.viewNode, Charged.op, h,
    Cost.pure_val, over_body, Charged.body, hb, e₁, filterMapL_std, Cost.filterMapL_val,
    over_unfold]

theorem produceTables_union {xs : List Rel} (h : g.node.view.forget = .union xs) :
    (produceTables (K := DerivationKernel.over D K hK P) ts g).val =
      (((xs.map fun x => (⟨g.lb, x, g.rb⟩ : GoalOf R Rel)).zipIdx).flatMap fun p =>
          (ansOf ts p.1).filterMap fun a => (Ans.inj D P a g.node p.2).val,
        [xs.map fun x => ⟨g.lb, x, g.rb⟩]) := by
  have e₁ := answersOf_eq (P := P) K hK ts
  at_cost K hK
  simp only [produceTables, Cost.bind_val, over_view, Charged.viewNode, Charged.op, h,
    Cost.pure_val, e₁, filterMapL_std, Cost.filterMapL_val, flatMapL_std, Cost.flatMapL_val,
    over_inj]

theorem produceTables_chain {xs : List Rel} (h : g.node.view.forget = .chain xs) :
    (produceTables (K := DerivationKernel.over D K hK P) ts g).val =
      (((splitsOf (K := DerivationKernel.over D K hK P) g (.chain xs)).val.map fun w =>
          (way (K := DerivationKernel.over D K hK P) ts g w).val).flatMap Prod.fst,
        ((splitsOf (K := DerivationKernel.over D K hK P) g (.chain xs)).val.map fun w =>
          (way (K := DerivationKernel.over D K hK P) ts g w).val).flatMap Prod.snd) := by
  at_cost K hK
  simp only [produceTables, Cost.bind_val, over_view, Charged.viewNode, Charged.op, h,
    Cost.pure_val, mapL_std, Cost.mapL_val]

theorem produceTables_meet {xs : List Rel} (h : g.node.view.forget = .meet xs) :
    (produceTables (K := DerivationKernel.over D K hK P) ts g).val =
      (((splitsOf (K := DerivationKernel.over D K hK P) g (.meet xs)).val.map fun w =>
          (way (K := DerivationKernel.over D K hK P) ts g w).val).flatMap Prod.fst,
        ((splitsOf (K := DerivationKernel.over D K hK P) g (.meet xs)).val.map fun w =>
          (way (K := DerivationKernel.over D K hK P) ts g w).val).flatMap Prod.snd) := by
  at_cost K hK
  simp only [produceTables, Cost.bind_val, over_view, Charged.viewNode, Charged.op, h,
    Cost.pure_val, mapL_std, Cost.mapL_val]

theorem produce_val (u : Bool × List (Ans D P)) :
    (produce (K := DerivationKernel.over D K hK P) ts g u).val =
      (u.2 ++ (produceTables (K := DerivationKernel.over D K hK P) ts g).val.1,
        (if u.1 then [[]] else []) ++
          (produceTables (K := DerivationKernel.over D K hK P) ts g).val.2) := by
  at_cost K hK
  simp only [produce, Cost.bind_val, Cost.pure_val]

end produce

end Tabled

end RwLog
