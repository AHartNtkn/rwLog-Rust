/-
# Comparing runs step for step

* `StepEquiv`: two answer lists of one step agree up to order and equivalent
  answers. `TraceEquiv`: two traces agree step for step, up to `StepEquiv`.
  A step emits a set of answers and a machine may keep any representative of
  a class of equivalent answers, so this is what "the same run" means.
* Lockstep simulation (`Runtime.trace_of_sim`, `Runtime.halts_iff_of_sim`): if
  a relation between the states of two runtimes is preserved by a step, with
  related emissions, the traces are related step for step and the runs halt
  together. This is how a rung shows it runs like another one (an earlier
  rung, the same rung on a mirrored or reordered query).
-/
import RwLog.Rungs.Framework.Runtime
import RwLog.Trusted.Properties
import RwLog.Kernel.Covers

namespace RwLog

theorem StepEquiv.refl (xs : List Span) : StepEquiv xs xs :=
  ⟨xs, List.Perm.refl _, List.forall₂_same.2 fun x _ => Span.Equiv.refl x⟩

theorem StepEquiv.of_perm {xs ys : List Span} (h : xs.Perm ys) : StepEquiv xs ys :=
  ⟨xs, h, List.forall₂_same.2 fun x _ => Span.Equiv.refl x⟩

theorem StepEquiv.of_forall₂ {xs ys : List Span} (h : List.Forall₂ Span.Equiv xs ys) :
    StepEquiv xs ys :=
  ⟨ys, List.Perm.refl _, h⟩

theorem StepEquiv.symm {xs ys : List Span} (h : StepEquiv xs ys) : StepEquiv ys xs := by
  obtain ⟨ys', hp, hf⟩ := h
  obtain ⟨m, hm, hmp⟩ := List.perm_comp_forall₂ hp.symm (hf.flip)
  exact ⟨m, hmp, hm.imp fun _ _ h => Span.Equiv.symm h⟩

theorem forall₂_equiv_trans : ∀ {xs ys zs : List Span}, List.Forall₂ Span.Equiv xs ys →
    List.Forall₂ Span.Equiv ys zs → List.Forall₂ Span.Equiv xs zs
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h hs, .cons h' hs' => .cons (Span.Equiv.trans h h') (forall₂_equiv_trans hs hs')

theorem forall₂_mem_left {α β : Type} {R : α → β → Prop} : ∀ {xs : List α} {ys : List β},
    List.Forall₂ R xs ys → ∀ {x}, x ∈ xs → ∃ y ∈ ys, R x y
  | _, _, .nil, _, hx => by cases hx
  | _, _, .cons (b := b) h hs, x, hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨b, List.mem_cons_self .., h⟩
    · obtain ⟨y, hy, r⟩ := forall₂_mem_left hs hx
      exact ⟨y, List.mem_cons_of_mem _ hy, r⟩

theorem StepEquiv.trans {xs ys zs : List Span} (h₁ : StepEquiv xs ys) (h₂ : StepEquiv ys zs) :
    StepEquiv xs zs := by
  obtain ⟨ys', hp, hf⟩ := h₁
  obtain ⟨zs', hq, hg⟩ := h₂
  obtain ⟨m, hm, hmp⟩ := List.perm_comp_forall₂ hp hg
  refine ⟨m, hmp.trans hq, ?_⟩
  exact forall₂_equiv_trans hf hm

theorem StepEquiv.append {xs ys xs' ys' : List Span} (h : StepEquiv xs ys) (h' : StepEquiv xs' ys') :
    StepEquiv (xs ++ xs') (ys ++ ys') := by
  obtain ⟨u, hp, hf⟩ := h
  obtain ⟨u', hp', hf'⟩ := h'
  exact ⟨u ++ u', hp.append hp', List.rel_append hf hf'⟩

theorem map_swap_swap (xs : List Span) : (xs.map Span.swap).map Span.swap = xs := by
  rw [List.map_map]
  have : (Span.swap ∘ Span.swap) = id := funext fun s => s.swap_swap
  rw [this, List.map_id]

theorem StepEquiv.map_swap {xs ys : List Span} (h : StepEquiv xs ys) :
    StepEquiv (xs.map Span.swap) (ys.map Span.swap) := by
  obtain ⟨u, hp, hf⟩ := h
  refine ⟨u.map Span.swap, hp.map _, ?_⟩
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact hf.imp fun _ _ h => Span.Equiv.swap h

theorem StepEquiv.length {xs ys : List Span} (h : StepEquiv xs ys) : xs.length = ys.length := by
  obtain ⟨u, hp, hf⟩ := h
  rw [hf.length_eq, hp.length_eq]

theorem StepEquiv.mem {xs ys : List Span} (h : StepEquiv xs ys) {x : Span} (hx : x ∈ xs) :
    ∃ y ∈ ys, x.Equiv y := by
  obtain ⟨u, hp, hf⟩ := h
  obtain ⟨y, hy, hxy⟩ := forall₂_mem_left hf hx
  exact ⟨y, hp.subset hy, hxy⟩

/-- `flatMap` over related lists with related images. -/
theorem StepEquiv.flatMap {α : Type} {xs ys : List α} (R : α → α → Prop)
    (hxy : ∃ ys', ys'.Perm ys ∧ List.Forall₂ R xs ys')
    {f g : α → List Span} (hfg : ∀ x y, R x y → StepEquiv (f x) (g y)) :
    StepEquiv (xs.flatMap f) (ys.flatMap g) := by
  obtain ⟨ys', hp, hf⟩ := hxy
  refine StepEquiv.trans ?_ (StepEquiv.of_perm (hp.flatMap_right g))
  clear hp
  induction hf with
  | nil => exact StepEquiv.refl _
  | cons h _ ih => simp only [List.flatMap_cons]; exact (hfg _ _ h).append ih

theorem TraceEquiv.refl (t : List (List Span)) : TraceEquiv t t :=
  List.forall₂_same.2 fun xs _ => StepEquiv.refl xs

theorem TraceEquiv.symm {t t' : List (List Span)} (h : TraceEquiv t t') : TraceEquiv t' t :=
  (List.Forall₂.flip h).imp fun _ _ h => StepEquiv.symm h

theorem TraceEquiv.trans : ∀ {t t' t'' : List (List Span)}, TraceEquiv t t' → TraceEquiv t' t'' →
    TraceEquiv t t''
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h hs, .cons h' hs' => .cons (h.trans h') (TraceEquiv.trans hs hs')

/-- Traces that agree step for step emit the same answers overall, up to
order and equivalence. -/
theorem TraceEquiv.flatten : ∀ {t t' : List (List Span)}, TraceEquiv t t' →
    StepEquiv t.flatten t'.flatten
  | _, _, .nil => StepEquiv.refl _
  | _, _, .cons h hs => by
    simp only [List.flatten_cons]; exact h.append (TraceEquiv.flatten hs)

/-! ## Lockstep simulation -/

/-- Two steps correspond: both emit, with related answers and related next
states, or both are done. -/
def Step.Rel {S S' : Type} (E : List Span → List Span → Prop) (Sim : S → S' → Prop) :
    Step S → Step S' → Prop
  | .emit as t, .emit as' t' => E as as' ∧ Sim t t'
  | .done, .done => True
  | _, _ => False

namespace Runtime

variable {R R' : Runtime} {E : List Span → List Span → Prop} {Sim : R.State → R'.State → Prop}

/-- A relation on states preserved by a step relates the traces step for
step. -/
theorem trace_of_sim (hstep : ∀ s s', Sim s s' → Step.Rel E Sim (R.step s) (R'.step s')) :
    ∀ (n : Nat) (s : R.State) (s' : R'.State), Sim s s' →
      List.Forall₂ E (R.trace s n) (R'.trace s' n)
  | 0, _, _, _ => .nil
  | n + 1, s, s', h => by
    have hs := hstep s s' h
    cases h₁ : R.step s with
    | done =>
      cases h₂ : R'.step s' with
      | done => rw [R.trace_succ_done h₁, R'.trace_succ_done h₂]; exact .nil
      | emit as' t' => rw [h₁, h₂] at hs; exact hs.elim
    | emit as t =>
      cases h₂ : R'.step s' with
      | done => rw [h₁, h₂] at hs; exact hs.elim
      | emit as' t' =>
        rw [h₁, h₂] at hs
        rw [R.trace_succ_emit h₁, R'.trace_succ_emit h₂]
        exact .cons hs.1 (trace_of_sim hstep n t t' hs.2)

/-- Runs related by a lockstep simulation halt together. -/
theorem halts_iff_of_sim (hstep : ∀ s s', Sim s s' → Step.Rel E Sim (R.step s) (R'.step s'))
    (n : Nat) {s : R.State} {s' : R'.State} (h : Sim s s') : R.Halts s n ↔ R'.Halts s' n := by
  rw [R.halts_iff_trace_length, R'.halts_iff_trace_length, (trace_of_sim hstep n s s' h).length_eq]

/-- With `StepEquiv` as the relation on emissions, what the two runs have
emitted after `n` steps agrees up to order and equivalence. -/
theorem emitted_of_sim {Sim : R.State → R'.State → Prop}
    (hstep : ∀ s s', Sim s s' → Step.Rel StepEquiv Sim (R.step s) (R'.step s'))
    (n : Nat) {s : R.State} {s' : R'.State} (h : Sim s s') :
    StepEquiv (R.emitted s n) (R'.emitted s' n) := by
  rw [R.emitted_eq_flatten_trace, R'.emitted_eq_flatten_trace]
  exact TraceEquiv.flatten (trace_of_sim hstep n s s' h)

end Runtime

end RwLog
