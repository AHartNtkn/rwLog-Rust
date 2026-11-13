/-
# The trace laws of the hedge

`Hedge.step_sim` for the two ways a query is written the other way round.

* `convTrace_of`: if the runs of `A` on `q` and on `conv q` cost the same step
  for step and emit the same answers swapped, and likewise the runs of `B`,
  then so do the runs of the hedge: its trace on `conv q` is its trace on `q`
  with every answer swapped.
* `dualTrace_of`: if the runs of `A` on a query and on its mirror image cost
  the same step for step and emit the same answers swapped, up to order and
  equivalence, and the runs of `B` cost the same and emit the same answers
  swapped, up to order, then the trace of the hedge on the mirror image is
  the mirror image of its trace, up to order and equivalence.

`B`'s answers must correspond exactly, not up to equivalence, because the
hedge keeps those that carry no constraints, and equivalent spans need not
both be written without constraints.
-/
import RwLog.Rungs.Hedge.Laws
import RwLog.Rungs.Tabled.Base.Proofs.SymmetryLists

namespace RwLog

open Cost R001.Symmetry

namespace Hedge

theorem plains_map_swap (bs : List Span) : plains (bs.map Span.swap) = (plains bs).map Span.swap := by
  simp only [plains, List.filter_map, Function.comp_def, plain_swap]

theorem filterL_plain_ticks (bs : List Span) :
    (filterL plain bs).ticks = (bs.map fun x => (plain x).ticks).sum :=
  filterL_ticks plain bs

theorem dropped_map_swap (as sb : List Span) :
    ((as.map Span.swap).filter fun x => !(sb.map Span.swap).any fun t => t.covers? x) =
      (as.filter fun x => !sb.any fun t => t.covers? x).map Span.swap := by
  simp only [List.filter_map, List.any_map, Function.comp_def, covers?_swap]

/-- The answers of the run on `conv q` are those of the run on `q`, swapped. -/
def convRels : Rels where
  EA xs ys := ys = xs.map Span.swap
  EB xs ys := ys = xs.map Span.swap
  E xs ys := ys = xs.map Span.swap
  S xs ys := ys = xs.map Span.swap
  SB xs ys := ys = xs.map Span.swap
  plainTicks := by
    rintro bs _ rfl
    simp only [filterL_plain_ticks, List.map_map, Function.comp_def, plain_swap]
  plains := by
    rintro bs _ rfl
    exact plains_map_swap bs
  outA := by
    rintro as _ sb _ rfl rfl
    exact dropped_map_swap as sb
  outB := by
    rintro ps _ s _ rfl rfl
    exact fresh_map_swap s ps
  appS := by
    rintro s _ o _ rfl rfl
    simp
  appSB := by
    rintro s _ o _ rfl rfl
    simp
  nil := rfl

theorem stepEquiv_filter {xs ys : List Span} (h : StepEquiv xs ys) (p q : Span → Bool)
    (hpq : ∀ x y, x.Equiv y → p x = q y) : StepEquiv (xs.filter p) (ys.filter q) := by
  obtain ⟨ys', hperm, hf⟩ := h
  refine ⟨ys'.filter q, hperm.filter q, ?_⟩
  clear hperm
  induction hf with
  | nil => exact .nil
  | @cons x y xs ys' hxy _ ih =>
    simp only [List.filter_cons, hpq x y hxy]
    split
    · exact .cons hxy ih
    · exact ih

/-- The answers of the run on the mirror image are those of the run, swapped,
up to order and equivalence; those of `B` up to order only. -/
def dualRels : Rels where
  EA xs ys := StepEquiv ys (xs.map Span.swap)
  EB xs ys := ys.Perm (xs.map Span.swap)
  E xs ys := StepEquiv ys (xs.map Span.swap)
  S xs ys := ClassEq ys (xs.map Span.swap)
  SB xs ys := ClassEq ys (xs.map Span.swap)
  plainTicks := by
    intro bs bs' h
    simp only [filterL_plain_ticks]
    rw [(h.map fun x => (plain x).ticks).sum_eq]
    simp only [List.map_map, Function.comp_def, plain_swap]
  plains := by
    intro bs bs' h
    rw [← plains_map_swap]
    exact h.filter _
  outA := by
    intro as as' sb sb' h hs
    rw [← dropped_map_swap]
    refine stepEquiv_filter h _ _ fun x y e => ?_
    congr 1
    apply Bool.eq_iff_iff.2
    simp only [List.any_eq_true]
    constructor
    · rintro ⟨t, ht, hc⟩
      obtain ⟨t', ht', e'⟩ := hs.1 t ht
      exact ⟨t', ht', by rw [← covers?_congr e' e]; exact hc⟩
    · rintro ⟨t, ht, hc⟩
      obtain ⟨t', ht', e'⟩ := hs.2 t ht
      exact ⟨t', ht', by rw [covers?_congr e' e]; exact hc⟩
  outB := by
    intro ps ps' s s' h hs
    rw [← fresh_map_swap]
    exact fresh_stepEquiv hs (ClassEq.of_stepEquiv (StepEquiv.of_perm h))
  appS := by
    intro s s' o o' h h'
    rw [List.map_append]
    exact h.append (ClassEq.of_stepEquiv h')
  appSB := by
    intro s s' o o' h h'
    rw [List.map_append]
    exact h.append (ClassEq.of_stepEquiv h')
  nil := StepEquiv.refl _

variable {A B : CostedRuntime} {SimA : A.State → A.State → Prop} {SimB : B.State → B.State → Prop}

theorem forall₂_eq_map {t t' : List (List Span)}
    (h : List.Forall₂ (fun xs ys => ys = xs.map Span.swap) t t') :
    t' = t.map (·.map Span.swap) := by
  induction h with
  | nil => rfl
  | cons h _ ih => rw [List.map_cons, ← ih, h]

theorem forall₂_stepEquiv_map {t t' : List (List Span)}
    (h : List.Forall₂ (fun xs ys => StepEquiv ys (xs.map Span.swap)) t t') :
    TraceEquiv t' (t.map (·.map Span.swap)) := by
  induction h with
  | nil => exact .nil
  | cons h _ ih => exact .cons h ih

/-- The hedge's trace on a converse is its trace swapped, when that holds of
both machines step for step, at the same cost. -/
theorem convTrace_of
    (hA : ∀ a a', SimA a a' → CRel convRels.EA SimA (A.step a) (A.step a'))
    (hB : ∀ b b', SimB b b' → CRel convRels.EB SimB (B.step b) (B.step b'))
    {P : Program} {q : Rel} (hA0 : SimA (A.start P q) (A.start P (.conv q)))
    (hB0 : SimB (B.start P q) (B.start P (.conv q))) (n : Nat) :
    (machine A B).runtime.trace ((machine A B).runtime.init P (.conv q)) n =
      ((machine A B).runtime.trace ((machine A B).runtime.init P q) n).map (·.map Span.swap) :=
  forall₂_eq_map (trace_sim (r := convRels) hA hB
    (st := (machine A B).start P q) (st' := (machine A B).start P (.conv q))
    ⟨hA0, hB0, rfl, rfl, rfl, rfl, rfl⟩ n)

/-- The hedge's trace on the mirror image is the mirror image of its trace,
when that holds of both machines step for step, at the same cost. -/
theorem dualTrace_of
    (hA : ∀ a a', SimA a a' → CRel dualRels.EA SimA (A.step a) (A.step a'))
    (hB : ∀ b b', SimB b b' → CRel dualRels.EB SimB (B.step b) (B.step b'))
    {P : Program} {q : Rel} (hA0 : SimA (A.start P q) (A.start P.dual q.dual))
    (hB0 : SimB (B.start P q) (B.start P.dual q.dual)) (n : Nat) :
    TraceEquiv ((machine A B).runtime.trace ((machine A B).runtime.init P.dual q.dual) n)
      (((machine A B).runtime.trace ((machine A B).runtime.init P q) n).map (·.map Span.swap)) :=
  forall₂_stepEquiv_map (trace_sim (r := dualRels) hA hB
    (st := (machine A B).start P q) (st' := (machine A B).start P.dual q.dual)
    ⟨hA0, hB0, rfl, rfl, rfl, ClassEq.refl _, ClassEq.refl _⟩ n)

end Hedge

end RwLog
