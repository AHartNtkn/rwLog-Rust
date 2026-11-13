/-
# Chains of spans

`Span.chain` (in `Trusted/Cost.lean`) composes a list of spans from the left.
Its ground meaning is the composition of the members' relations, so whether a
chain composes depends only on that relation: it is unchanged when two
adjacent members are fused, and a pair with no match kills the whole chain.
-/
import RwLog.Trusted.Cost
import RwLog.SpanLayer.Algebra

namespace RwLog

namespace GRel

/-- The composition of a list of relations, left to right. -/
def chain : List GRel → GRel
  | [] => id
  | R :: Rs => R.comp (chain Rs)

@[simp] theorem chain_nil : chain [] = id := rfl

@[simp] theorem chain_cons (R : GRel) (Rs : List GRel) : chain (R :: Rs) = R.comp (chain Rs) := rfl

theorem chain_append (xs ys : List GRel) : chain (xs ++ ys) = (chain xs).comp (chain ys) := by
  induction xs with
  | nil => exact (id_comp _).symm
  | cons R xs ih => simp only [List.cons_append, chain_cons, ih, comp_assoc]

end GRel

namespace Span

theorem denO_nonempty_iff (o : Option Span) : (denO o).Nonempty ↔ o.isSome := by
  cases o with
  | none => simp [denO]
  | some s => simp [denO, den_nonempty]

theorem denO_foldl_compose (ts : List Span) : ∀ o : Option Span,
    denO (ts.foldl (fun acc t => acc.bind (·.compose t)) o) =
      (denO o).comp (GRel.chain (ts.map den)) := by
  induction ts with
  | nil => intro o; simp only [List.foldl_nil, List.map_nil, GRel.chain_nil, GRel.comp_id]
  | cons t ts ih =>
    intro o
    rw [List.foldl_cons, ih, List.map_cons, GRel.chain_cons, ← GRel.comp_assoc]
    congr 1
    cases o with
    | none => exact (empty_comp _).symm
    | some s => exact compose_den s t

/-- A chain denotes the composition of its members. -/
theorem denO_chain : ∀ xs : List Span, denO (chain xs) = GRel.chain (xs.map den)
  | [] => den_idSpan
  | s :: rest => denO_foldl_compose rest (some s)

/-- A chain composes exactly when the composed ground relation is nonempty. -/
theorem chain_isSome_iff (xs : List Span) :
    (chain xs).isSome ↔ (GRel.chain (xs.map den)).Nonempty := by
  rw [← denO_chain, denO_nonempty_iff]

/-- Fusing two adjacent members does not change what a chain denotes. -/
theorem denO_chain_fuse {a b c : Span} (h : a.compose b = some c) (xs ys : List Span) :
    denO (chain (xs ++ a :: b :: ys)) = denO (chain (xs ++ c :: ys)) := by
  simp only [denO_chain, List.map_append, List.map_cons, GRel.chain_append, GRel.chain_cons,
    compose_some h, GRel.comp_assoc]

/-- A chain composes exactly when it does with two adjacent members fused. -/
theorem chain_isSome_fuse {a b c : Span} (h : a.compose b = some c) (xs ys : List Span) :
    (chain (xs ++ a :: b :: ys)).isSome = (chain (xs ++ c :: ys)).isSome :=
  Bool.eq_iff_iff.2 (by rw [← denO_nonempty_iff, ← denO_nonempty_iff, denO_chain_fuse h])

/-- Two adjacent members with no match kill the chain. -/
theorem chain_eq_none_of_compose {a b : Span} (h : a.compose b = none) (xs ys : List Span) :
    chain (xs ++ a :: b :: ys) = none := by
  cases hc : chain (xs ++ a :: b :: ys) with
  | none => rfl
  | some s =>
    have hne : (denO (chain (xs ++ a :: b :: ys))).Nonempty :=
      (denO_nonempty_iff _).2 (by rw [hc]; rfl)
    rw [denO_chain, List.map_append, List.map_cons, List.map_cons, GRel.chain_append,
      GRel.chain_cons, GRel.chain_cons, ← GRel.comp_assoc a.den, compose_none h,
      empty_comp, comp_empty] at hne
    exact absurd hne Set.not_nonempty_empty

end Span

end RwLog
