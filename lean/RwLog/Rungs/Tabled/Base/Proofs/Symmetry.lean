/-
# Rung R001: order and direction (the Symmetry group)

* `conv_trace`: running `conv q` is running `q` with every answer swapped,
  step for step and exactly. The two initial states have the same tables and
  differ only in `rootFlip`, and a round never reads `rootFlip` except to
  orient the root's new answers.
-/
import RwLog.Rungs.Tabled.Base.Proofs.Base
import RwLog.Kernel.Order

namespace RwLog

namespace R001

namespace Symmetry

/-! ## `conv_trace` -/

/-- Flipping the root's orientation leaves the tables alone. -/
theorem round_flip (st : State) :
    round ⟨st.P, st.tables, !st.rootFlip, st.depth⟩ =
      (⟨st.P, (round st).1.tables, !st.rootFlip, st.depth + 1⟩, (round st).2.map Span.swap) := by
  simp only [round, orient_not]

theorem step_flip (st : State) :
    step ⟨st.P, st.tables, !st.rootFlip, st.depth⟩ =
      match step st with
      | .emit as st' => .emit (as.map Span.swap) ⟨st'.P, st'.tables, !st'.rootFlip, st'.depth⟩
      | .done => .done := by
  unfold step
  by_cases h : st.finished = true
  · have h' : StateOf.finished ⟨st.P, st.tables, !st.rootFlip, st.depth⟩ = true := h
    simp [h, h']
  · have h' : ¬ StateOf.finished ⟨st.P, st.tables, !st.rootFlip, st.depth⟩ = true := h
    simp only [h, h', round_flip]
    simp [round]

/-- The state with the root's orientation flipped. -/
def _root_.RwLog.R001.StateOf.flip (st : State) : State := ⟨st.P, st.tables, !st.rootFlip, st.depth⟩

theorem trace_succ (st : runtime.State) (n : Nat) :
    runtime.trace st (n + 1) =
      match runtime.step st with
      | .emit as s' => as :: runtime.trace s' n
      | .done => [] := by
  conv => lhs; unfold Runtime.trace
  cases runtime.step st <;> rfl

theorem trace_flip (st : State) (n : Nat) :
    runtime.trace (st.flip : runtime.State) n =
      (runtime.trace (st : runtime.State) n).map (·.map Span.swap) := by
  induction n generalizing st with
  | zero => rfl
  | succ n ih =>
    refine (trace_succ (st.flip : runtime.State) n).trans ?_
    refine Eq.trans ?_ (congrArg _ (trace_succ (st : runtime.State) n)).symm
    show (match step st.flip with
      | .emit as s' => as :: runtime.trace s' n
      | .done => []) = (match step st with
      | .emit as s' => as :: runtime.trace s' n
      | .done => []).map _
    rw [StateOf.flip, step_flip]
    cases step st with
    | emit as st' => simp only [List.map_cons]; rw [← ih st']; rfl
    | done => rfl

theorem _root_.RwLog.R001.conv_trace : Obligation.conv_trace := by
  intro P q n
  have h : runtime.init P (.conv q) = StateOf.flip (runtime.init P q) := by
    show StateOf.ofGoal P ⟨none, .conv q, none⟩ = _
    simp only [StateOf.ofGoal, GoalOf.norm, canon]
    rw [GoalOf.stripConv]
    rfl
  rw [h]
  exact trace_flip (runtime.init P q) n

/-! ## The canonical form forgets the order and grouping of `|`

`relCmp` is a linear order and a sorted list of branches is determined by its
members: `Kernel/Order.lean`. -/

section Canon

/-- Not a `|`. -/
def NotOr (e : Rel) : Prop := ∀ a b, e ≠ .or a b

theorem notOr_of_mem_orBranches : ∀ {e x : Rel}, x ∈ orBranches e → NotOr x
  | .or a b, x, h => by
    rw [orBranches, List.mem_append] at h
    exact h.elim notOr_of_mem_orBranches notOr_of_mem_orBranches
  | .zero, x, h | .span _, x, h | .and _ _, x, h | .seq _ _, x, h | .conv _, x, h | .call _, x, h => by
    simp only [orBranches, List.mem_singleton] at h; subst h; intro a b h; cases h

theorem orBranches_notOr {e : Rel} (h : NotOr e) : orBranches e = [e] := by
  cases e with
  | or a b => exact absurd rfl (h a b)
  | _ => rfl

theorem mem_orBranches_mkOr : ∀ {L : List Rel}, (∀ x ∈ L, NotOr x) →
    ∀ z, z ≠ .zero → (z ∈ orBranches (mkOr L) ↔ z ∈ L)
  | [], _, z, hz => by simp [mkOr, orBranches, hz]
  | [e], hL, z, _ => by
    rw [mkOr, orBranches_notOr (hL e (by simp))]
  | e :: e' :: es, hL, z, hz => by
    rw [show mkOr (e :: e' :: es) = .or e (mkOr (e' :: es)) from rfl, orBranches,
      orBranches_notOr (hL e (by simp)), List.mem_append,
      mem_orBranches_mkOr (fun x hx => hL x (List.mem_cons_of_mem _ hx)) z hz]
    simp

/-- The non-`0` branches of a canonical `|`. -/
theorem mem_orBranches_canon_or {a b : Rel} {z : Rel} (hz : z ≠ .zero) :
    z ∈ orBranches (canon (.or a b)) ↔ z ∈ orBranches (canon a) ∨ z ∈ orBranches (canon b) := by
  rw [canon, mem_orBranches_mkOr (fun x hx => ?_) z hz, mem_sortedBranches, List.mem_append]
  · simp [hz]
  · rw [mem_sortedBranches, List.mem_append] at hx
    exact hx.1.elim notOr_of_mem_orBranches notOr_of_mem_orBranches

theorem canon_or_comm (a b : Rel) : canon (.or a b) = canon (.or b a) := by
  simp only [canon]
  congr 1
  exact sortedBranches_eq fun z _ => by simp only [List.mem_append]; exact or_comm

theorem canon_or_assoc (a b c : Rel) : canon (.or (.or a b) c) = canon (.or a (.or b c)) := by
  conv => lhs; rw [canon]
  conv => rhs; rw [canon]
  congr 1
  refine sortedBranches_eq fun z hz => ?_
  simp only [List.mem_append, mem_orBranches_canon_or hz]
  exact or_assoc

end Canon

theorem _root_.RwLog.R001.or_comm_trace : Obligation.or_comm_trace := by
  intro P a b n
  show runtime.trace (StateOf.ofGoal P ⟨none, .or a b, none⟩) n =
    runtime.trace (StateOf.ofGoal P ⟨none, .or b a, none⟩) n
  simp only [StateOf.ofGoal, GoalOf.norm, canon_or_comm a b]

theorem _root_.RwLog.R001.or_assoc : Obligation.or_assoc := by
  intro P a b c n
  show runtime.trace (StateOf.ofGoal P ⟨none, .or (.or a b) c, none⟩) n =
    runtime.trace (StateOf.ofGoal P ⟨none, .or a (.or b c), none⟩) n
  simp only [StateOf.ofGoal, GoalOf.norm, canon_or_assoc a b c]

end Symmetry

end R001

end RwLog
