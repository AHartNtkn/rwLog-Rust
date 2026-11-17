/-
# The diving engine on a root that is its own converse

A reading of a node makes an answer of the goal of that node between no
boundaries (`rd_goal`). So the answer a step emits is an answer of the root
goal, and on a root that is its own converse so is its converse, which the
step emits with it: every step shows nothing, or an answer and its converse.
The machine of the diving engine therefore shows its own converse on such a
root (`dive_selfConverse`).
-/
import RwLog.Rungs.Dive.FanRun
import RwLog.Rungs.Framework.BesideConverse

namespace RwLog

namespace Dive

open Beside

section Reading

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}
  (K : Kernel R Cost) (hK : K.Refines D)

theorem ml_nil (ev : Nat → Rel → Cost (Option (Ans D P) × Nat)) (a : Ans D P) (k : Nat) :
    ml K hK ev a k [] = pure (some a, k) := by
  at_cost K hK
  rfl

theorem ml_cons (ev : Nat → Rel → Cost (Option (Ans D P) × Nat)) (a : Ans D P) (k : Nat)
    (x : Rel) (xs : List Rel) :
    ml K hK ev a k (x :: xs) = (do
      let r ← ev k x
      match r.1 with
      | none => pure (none, r.2)
      | some b =>
        match ← Ans.meetA D P K hK a b with
        | none => pure (none, r.2)
        | some c => ml K hK ev c r.2 xs) := by
  at_cost K hK
  conv_lhs => unfold ml meetL
  congr! 2 with r
  cases r.1 with
  | none => rfl
  | some b =>
    simp only
    congr! 2 with z
    cases z with
    | none => rfl
    | some c => rfl

/-- Joining answers between no boundaries makes an answer between no
boundaries. -/
theorem jl_bounds (ev : Nat → Rel → Cost (Option (Ans D P) × Nat))
    (hev : ∀ k x b k', (ev k x).val = (some b, k') → b.goal.lb = none ∧ b.goal.rb = none) :
    ∀ (xs : List Rel) (a : Ans D P) (k : Nat) (z : Ans D P) (k' : Nat), a.goal.lb = none →
      a.goal.rb = none → (jl K hK ev a k xs).val = (some z, k') →
      z.goal.lb = none ∧ z.goal.rb = none
  | [], a, k, z, k', hl, hr, h => by
    rw [jl_nil] at h
    obtain ⟨rfl, -⟩ : a = z ∧ k = k' := by simpa using h
    exact ⟨hl, hr⟩
  | x :: xs, a, k, z, k', hl, hr, h => by
    rw [jl_cons] at h
    simp only [Cost.bind_val] at h
    rcases hx : (ev k x).val with ⟨_ | b, k1⟩
    · rw [hx] at h
      simp at h
    · rw [hx] at h
      simp only [Cost.bind_val] at h
      cases hj : (Ans.join D P K hK a b).val with
      | none =>
        rw [hj] at h
        simp at h
      | some c =>
        rw [hj] at h
        obtain ⟨-, -, hc⟩ := (Ans.join_val K hK).1 hj
        obtain ⟨-, hb⟩ := hev k x b k1 hx
        exact jl_bounds ev hev xs c k1 z k' (by rw [hc]; exact hl) (by rw [hc]; exact hb) h

/-- Meeting answers onto an answer between no boundaries makes an answer
between no boundaries. -/
theorem ml_bounds (ev : Nat → Rel → Cost (Option (Ans D P) × Nat)) :
    ∀ (xs : List Rel) (a : Ans D P) (k : Nat) (z : Ans D P) (k' : Nat), a.goal.lb = none →
      a.goal.rb = none → (ml K hK ev a k xs).val = (some z, k') →
      z.goal.lb = none ∧ z.goal.rb = none
  | [], a, k, z, k', hl, hr, h => by
    rw [ml_nil] at h
    obtain ⟨rfl, -⟩ : a = z ∧ k = k' := by simpa using h
    exact ⟨hl, hr⟩
  | x :: xs, a, k, z, k', hl, hr, h => by
    rw [ml_cons] at h
    simp only [Cost.bind_val] at h
    rcases hx : (ev k x).val with ⟨_ | b, k1⟩
    · rw [hx] at h
      simp at h
    · rw [hx] at h
      simp only [Cost.bind_val] at h
      cases hj : (Ans.meetA D P K hK a b).val with
      | none =>
        rw [hj] at h
        simp at h
      | some c =>
        rw [hj] at h
        obtain ⟨-, -, hc⟩ := (Ans.meetA_val K hK).1 hj
        exact ml_bounds ev xs c k1 z k' (by rw [hc]; exact hl) (by rw [hc]; exact hr) h

/-- **A reading of a node makes an answer of the goal of that node between
no boundaries.** -/
theorem rd_goal : ∀ (d k : Nat) (n : Rel) (a : Ans D P) (k' : Nat),
    (rd (P := P) K hK d k n).val = (some a, k') → a.goal = ⟨none, n, none⟩
  | 0, k, n, a, k', h => by
    rw [rd_zero] at h
    simp at h
  | d + 1, k, n, a, k', h => by
    have ih : ∀ k x b k', (rd (P := P) K hK d k x).val = (some b, k') →
        b.goal.lb = none ∧ b.goal.rb = none := fun k x b k' hb => by
      rw [rd_goal d k x b k' hb]; exact ⟨rfl, rfl⟩
    rw [rd_succ] at h
    simp only [Cost.bind_val, Charged.viewNode, Charged.op_val] at h
    cases hv : n.view with
    | span s =>
      rw [hv] at h
      simp only [NodeView.forget, Cost.bind_val, Cost.pure_val, Prod.mk.injEq] at h
      obtain ⟨s', rfl, -, -, -, hg⟩ := (Ans.leaf_val K hK).1 h.1
      exact hg
    | call nm f =>
      rw [hv] at h
      simp only [NodeView.forget, Charged.body, Cost.bind_val, Charged.op_val] at h
      cases hb : Charged.bodyOf P n with
      | none =>
        rw [hb] at h
        simp at h
      | some b =>
        rw [hb] at h
        simp only [Cost.bind_val] at h
        rcases hr : (rd (P := P) K hK d k b).val with ⟨_ | a0, k1⟩
        · rw [hr] at h
          simp at h
        · rw [hr] at h
          simp only [Cost.bind_val, Cost.pure_val, Prod.mk.injEq] at h
          obtain ⟨-, -, hg⟩ := Ans.unfold_val.1 h.1
          obtain ⟨h1, h2⟩ := ih k b a0 k1 hr
          rw [hg, h1, h2]
    | union xs =>
      rw [hv] at h
      simp only [NodeView.forget] at h
      cases hx : xs[k % xs.length]? with
      | none =>
        rw [hx] at h
        simp at h
      | some x =>
        rw [hx] at h
        simp only [Cost.bind_val] at h
        rcases hr : (rd (P := P) K hK d (k / xs.length) x).val with ⟨_ | a0, k1⟩
        · rw [hr] at h
          simp at h
        · rw [hr] at h
          simp only [Cost.bind_val, Cost.pure_val, Prod.mk.injEq] at h
          obtain ⟨-, -, hg⟩ := Ans.inj_val.1 h.1
          obtain ⟨h1, h2⟩ := ih _ x a0 k1 hr
          rw [hg, h1, h2]
    | chain xs =>
      rw [hv] at h
      simp only [NodeView.forget] at h
      cases xs with
      | nil => simp at h
      | cons x rest =>
        simp only [Cost.bind_val] at h
        rcases hr : (rd (P := P) K hK d k x).val with ⟨_ | a0, k1⟩
        · rw [hr] at h
          simp at h
        · rw [hr] at h
          simp only [Cost.bind_val] at h
          rcases hj : (jl K hK (rd K hK d) a0 k1 rest).val with ⟨_ | c, k2⟩
          · rw [hj] at h
            simp at h
          · rw [hj] at h
            simp only [Cost.bind_val, Cost.pure_val, Prod.mk.injEq] at h
            obtain ⟨-, -, hg⟩ := Ans.inj_val.1 h.1
            obtain ⟨h1, h2⟩ := ih k x a0 k1 hr
            obtain ⟨h3, h4⟩ := jl_bounds K hK _ ih rest a0 k1 c k2 h1 h2 hj
            rw [hg, h3, h4]
    | meet xs =>
      rw [hv] at h
      simp only [NodeView.forget] at h
      cases xs with
      | nil => simp at h
      | cons x rest =>
        simp only [Cost.bind_val] at h
        rcases hr : (rd (P := P) K hK d k x).val with ⟨_ | a0, k1⟩
        · rw [hr] at h
          simp at h
        · rw [hr] at h
          simp only [Cost.bind_val] at h
          rcases hj : (ml K hK (rd K hK d) a0 k1 rest).val with ⟨_ | c, k2⟩
          · rw [hj] at h
            simp at h
          · rw [hj] at h
            simp only [Cost.bind_val, Cost.pure_val, Prod.mk.injEq] at h
            obtain ⟨-, -, hg⟩ := Ans.inj_val.1 h.1
            obtain ⟨h1, h2⟩ := ih k x a0 k1 hr
            obtain ⟨h3, h4⟩ := ml_bounds K hK _ rest a0 k1 c k2 h1 h2 hj
            rw [hg, h3, h4]

theorem State.next_root (s : State Rel) : s.next.root = s.root := by
  unfold State.next
  split <;> rfl

/-- A step shows nothing, or the answer of its reading and its converse. -/
theorem st_shows (s : State Rel) :
    (st (P := P) K hK s).val = .emit [] s.next ∨
      ∃ a : Ans D P, a.goal = ⟨none, s.root, none⟩ ∧
        (st (P := P) K hK s).val = .emit [a, (Ans.swapA D P a).val] s.next := by
  rw [st_eq, Cost.bind_val]
  rcases hw : (Cost.within (2 ^ s.level) (rd (P := P) K hK (2 ^ s.level) s.number s.root)).val
    with _ | ⟨_ | a, k'⟩
  · left
    at_cost K hK
    rfl
  · left
    at_cost K hK
    rfl
  · right
    refine ⟨a, ?_, ?_⟩
    · unfold Cost.within at hw
      split at hw
      · exact rd_goal K hK _ _ _ a k' (Option.some.inj hw)
      · cases hw
    · rw [fin_some]
      rfl

end Reading

/-! ## The machine -/

variable {R : Sorts → Type} [∀ S, Answer (R S)] [∀ S, DecidableEq (R S)]
  (dom : ∀ S, Domain (R S)) (K : ∀ S, Kernel (R S) Cost) (hK : ∀ S, (K S).Refines (dom S))
  (cells : ∀ S, R S → Nat)

open Engine in
/-- From a state that holds the root, a root that is its own converse, every
step of the machine shows nothing, or an answer and its converse. -/
theorem dive_showsSelf (M : Interp) : ∀ (n : Nat) (s : dive.StateAt dom), s.st.root = s.root →
    s.root.normConv = s.root →
    TraceEquiv M ((dive.costedAt dom K hK cells).runtime.trace s n)
      (((dive.costedAt dom K hK cells).runtime.trace s n).map Shown.swap)
  | 0, _, _, _ => List.Forall₂.nil
  | n + 1, s, hr, hc => by
    have hv := machine_step dive dom K hK cells s
    have hst : dive.stepAt dom K hK s.P s.st = st (K s.P.sorts) (hK s.P.sorts) s.st := rfl
    have ih := dive_showsSelf M n ⟨s.P, s.root, s.st.next⟩ ((State.next_root s.st).trans hr) hc
    rcases st_shows (P := s.P) (K s.P.sorts) (hK s.P.sorts) s.st with h | ⟨a, hg, h⟩
    · have hs : (dive.costedAt dom K hK cells).runtime.step s =
          .emit (shownAt dom s.P s.root []) ⟨s.P, s.root, s.st.next⟩ := by
        rw [hst, h] at hv
        exact hv
      rw [Runtime.trace_succ_emit _ hs]
      exact List.Forall₂.cons (StepEquiv.refl _) ih
    · have hs : (dive.costedAt dom K hK cells).runtime.step s =
          .emit (shownAt dom s.P s.root [a, (Ans.swapA (dom s.P.sorts) s.P a).val])
            ⟨s.P, s.root, s.st.next⟩ := by
        rw [hst, h] at hv
        exact hv
      rw [Runtime.trace_succ_emit _ hs]
      refine List.Forall₂.cons ?_ ih
      have hg' : (Ans.swapA (dom s.P.sorts) s.P a).val.goal = ⟨none, s.root, none⟩ := by
        show (⟨a.goal.rb, a.goal.node.normConv, a.goal.lb⟩ : Goal (R s.P.sorts)) = _
        rw [hg, hr, hc]
      have e : shownAt dom s.P s.root [a, (Ans.swapA (dom s.P.sorts) s.P a).val] =
          [(⟨s.P.sorts, a.span⟩ : (S : Sorts) × R S)] ++
            [Answer.swap (⟨s.P.sorts, a.span⟩ : (S : Sorts) × R S)] := by
        simp only [shownAt, List.filterMap_cons, List.filterMap_nil, Ans.rootSpan, hg, hg', hr,
          ↓reduceIte, List.map_cons, List.map_nil]
        rfl
      rw [e]
      exact (StepEquiv.of_perm List.perm_append_comm).trans
        ((StepEquiv.refl _).append (StepEquiv.swap_swap M [_]).symm)

/-- **On a root that is its own converse the machine of the diving engine
shows its own converse.** -/
theorem dive_selfConverse : (dive.costedAt dom K hK cells).SelfConverse := by
  intro P root _ _ hN _ hself n
  rw [dive_start]
  refine dive_showsSelf dom K hK cells _ n _ rfl ?_
  show root.norm.normConv = root.norm
  rw [hN.norm_eq, hself]

end Dive

end RwLog
