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
import RwLog.Rungs.Framework.Answer
import RwLog.Trusted.Properties

namespace RwLog

section
variable {A B C : Type} [Answer A] [Answer B] [Answer C] {M : Interp}

theorem StepEquiv.refl (xs : List A) : (StepEquiv M) xs xs :=
  ⟨xs, List.Perm.refl _, List.forall₂_same.2 fun x _ => Answer.Equiv.refl x⟩

theorem StepEquiv.of_perm {xs ys : List A} (h : xs.Perm ys) : (StepEquiv M) xs ys :=
  ⟨xs, h, List.forall₂_same.2 fun x _ => Answer.Equiv.refl x⟩

theorem StepEquiv.of_forall₂ {xs : List A} {ys : List B} (h : List.Forall₂ (Answer.Equiv M) xs ys) :
    (StepEquiv M) xs ys :=
  ⟨ys, List.Perm.refl _, h⟩

theorem StepEquiv.symm {xs : List A} {ys : List B} (h : (StepEquiv M) xs ys) : (StepEquiv M) ys xs := by
  obtain ⟨ys', hp, hf⟩ := h
  obtain ⟨m, hm, hmp⟩ := List.perm_comp_forall₂ hp.symm (hf.flip)
  exact ⟨m, hmp, hm.imp fun _ _ h => Answer.Equiv.symm h⟩

theorem forall₂_equiv_trans : ∀ {xs : List A} {ys : List B} {zs : List C},
    List.Forall₂ (Answer.Equiv M) xs ys → List.Forall₂ (Answer.Equiv M) ys zs →
    List.Forall₂ (Answer.Equiv M) xs zs
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h hs, .cons h' hs' =>
    .cons (Answer.Equiv.trans h h') (forall₂_equiv_trans hs hs')

theorem forall₂_mem_left {α β : Type} {R : α → β → Prop} : ∀ {xs : List α} {ys : List β},
    List.Forall₂ R xs ys → ∀ {x}, x ∈ xs → ∃ y ∈ ys, R x y
  | _, _, .nil, _, hx => by cases hx
  | _, _, .cons (b := b) h hs, x, hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨b, List.mem_cons_self .., h⟩
    · obtain ⟨y, hy, r⟩ := forall₂_mem_left hs hx
      exact ⟨y, List.mem_cons_of_mem _ hy, r⟩

theorem StepEquiv.trans {xs : List A} {ys : List B} {zs : List C} (h₁ : (StepEquiv M) xs ys)
    (h₂ : (StepEquiv M) ys zs) : (StepEquiv M) xs zs := by
  obtain ⟨ys', hp, hf⟩ := h₁
  obtain ⟨zs', hq, hg⟩ := h₂
  obtain ⟨m, hm, hmp⟩ := List.perm_comp_forall₂ hp hg
  refine ⟨m, hmp.trans hq, ?_⟩
  exact forall₂_equiv_trans hf hm

theorem StepEquiv.append {xs xs' : List A} {ys ys' : List B} (h : (StepEquiv M) xs ys)
    (h' : (StepEquiv M) xs' ys') : (StepEquiv M) (xs ++ xs') (ys ++ ys') := by
  obtain ⟨u, hp, hf⟩ := h
  obtain ⟨u', hp', hf'⟩ := h'
  exact ⟨u ++ u', hp.append hp', List.rel_append hf hf'⟩

theorem map_swap_swap (xs : List Span) : (xs.map Span.swap).map Span.swap = xs := by
  rw [List.map_map]
  have : (Span.swap ∘ Span.swap) = id := funext fun s => s.swap_swap
  rw [this, List.map_id]

theorem StepEquiv.map_swap {xs : List A} {ys : List B} (h : (StepEquiv M) xs ys) :
    (StepEquiv M) (xs.map Answer.swap) (ys.map Answer.swap) := by
  obtain ⟨u, hp, hf⟩ := h
  refine ⟨u.map Answer.swap, hp.map _, ?_⟩
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact hf.imp fun _ _ h => Answer.Equiv.swap h

theorem StepEquiv.length {xs : List A} {ys : List B} (h : (StepEquiv M) xs ys) :
    xs.length = ys.length := by
  obtain ⟨u, hp, hf⟩ := h
  rw [hf.length_eq, hp.length_eq]

theorem StepEquiv.mem {xs : List A} {ys : List B} (h : (StepEquiv M) xs ys) {x : A} (hx : x ∈ xs) :
    ∃ y ∈ ys, (Answer.Equiv M) x y := by
  obtain ⟨u, hp, hf⟩ := h
  obtain ⟨y, hy, hxy⟩ := forall₂_mem_left hf hx
  exact ⟨y, hp.subset hy, hxy⟩

/-- `flatMap` over related lists with related images. -/
theorem StepEquiv.flatMap {α : Type} {xs ys : List α} (R : α → α → Prop)
    (hxy : ∃ ys', ys'.Perm ys ∧ List.Forall₂ R xs ys')
    {f : α → List A} {g : α → List B} (hfg : ∀ x y, R x y → (StepEquiv M) (f x) (g y)) :
    (StepEquiv M) (xs.flatMap f) (ys.flatMap g) := by
  obtain ⟨ys', hp, hf⟩ := hxy
  refine StepEquiv.trans ?_ (StepEquiv.of_perm (hp.flatMap_right g))
  clear hp
  induction hf with
  | nil => exact ⟨[], List.Perm.refl _, .nil⟩
  | cons h _ ih => simp only [List.flatMap_cons]; exact (hfg _ _ h).append ih

/-! ## What two steps show -/

/-- What two steps show is related: answers and final reports by `E`, and
certificates for the same level. -/
def Shown.Rel (E : List A → List B → Prop) : Shown A → Shown B → Prop
  | .answers xs, .answers ys => E xs ys
  | .level n, .level m => n = m
  | .final xs, .final ys => E xs ys
  | _, _ => False

theorem shownEquiv_iff {x : Shown A} {y : Shown B} : (ShownEquiv M) x y ↔ Shown.Rel (StepEquiv M) x y := by
  cases x <;> cases y <;> exact Iff.rfl

theorem ShownEquiv.refl (x : Shown A) : (ShownEquiv M) x x := by
  cases x with
  | answers xs => exact StepEquiv.refl xs
  | level n => exact rfl
  | final xs => exact StepEquiv.refl xs

theorem ShownEquiv.symm {x : Shown A} {y : Shown B} (h : (ShownEquiv M) x y) : (ShownEquiv M) y x := by
  cases x <;> cases y <;> first | exact StepEquiv.symm h | exact Eq.symm h | exact h.elim

theorem ShownEquiv.trans {x : Shown A} {y : Shown B} {z : Shown C} (h₁ : (ShownEquiv M) x y)
    (h₂ : (ShownEquiv M) y z) : (ShownEquiv M) x z := by
  cases x <;> cases y <;> cases z <;>
    first | exact StepEquiv.trans h₁ h₂ | exact Eq.trans h₁ h₂ | exact h₁.elim | exact h₂.elim

theorem ShownEquiv.swap {x : Shown A} {y : Shown B} (h : (ShownEquiv M) x y) :
    (ShownEquiv M) x.swap y.swap := by
  cases x <;> cases y <;> first | exact StepEquiv.map_swap h | exact h

theorem ShownEquiv.emits {x : Shown A} {y : Shown B} (h : (ShownEquiv M) x y) :
    (StepEquiv M) x.emits y.emits := by
  cases x <;> cases y <;>
    first | exact h | exact ⟨[], List.Perm.refl _, .nil⟩ | exact h.elim

theorem TraceEquiv.refl (t : List (Shown A)) : (TraceEquiv M) t t :=
  List.forall₂_same.2 fun x _ => ShownEquiv.refl x

theorem TraceEquiv.symm {t : List (Shown A)} {t' : List (Shown B)} (h : (TraceEquiv M) t t') :
    (TraceEquiv M) t' t :=
  (List.Forall₂.flip h).imp fun _ _ h => ShownEquiv.symm h

theorem TraceEquiv.trans : ∀ {t : List (Shown A)} {t' : List (Shown B)} {t'' : List (Shown C)},
    (TraceEquiv M) t t' → (TraceEquiv M) t' t'' → (TraceEquiv M) t t''
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h hs, .cons h' hs' => .cons (h.trans h') (TraceEquiv.trans hs hs')

/-- Traces that agree step for step emit the same answers overall, up to
order and equivalence. -/
theorem TraceEquiv.emits : ∀ {t : List (Shown A)} {t' : List (Shown B)}, (TraceEquiv M) t t' →
    (StepEquiv M) (t.flatMap Shown.emits) (t'.flatMap Shown.emits)
  | _, _, .nil => ⟨[], List.Perm.refl _, .nil⟩
  | _, _, .cons h hs => by
    simp only [List.flatMap_cons]; exact (ShownEquiv.emits h).append (TraceEquiv.emits hs)

/-! ## Lockstep simulation -/

/-- Two steps correspond: both emit, with related answers and related next
states, or both certify the same level and go to related states, or both are
done with related final reports. -/
def StepOf.Rel {S S' : Type} (E : List A → List B → Prop) (Sim : S → S' → Prop) :
    StepOf A S → StepOf B S' → Prop
  | .emit as t, .emit as' t' => E as as' ∧ Sim t t'
  | .progress n t, .progress n' t' => n = n' ∧ Sim t t'
  | .done fin, .done fin' => E fin fin'
  | _, _ => False

end

namespace Runtime

variable {M : Interp} {R R' : Runtime} {E : List R.Ans → List R'.Ans → Prop} {Sim : R.State → R'.State → Prop}

/-- A relation on states preserved by a step relates the traces step for
step. -/
theorem trace_of_sim (hstep : ∀ s s', Sim s s' → StepOf.Rel E Sim (R.step s) (R'.step s')) :
    ∀ (n : Nat) (s : R.State) (s' : R'.State), Sim s s' →
      List.Forall₂ (Shown.Rel E) (R.trace s n) (R'.trace s' n)
  | 0, _, _, _ => .nil
  | n + 1, s, s', h => by
    have hs := hstep s s' h
    cases h₁ : R.step s <;> cases h₂ : R'.step s' <;> rw [h₁, h₂] at hs <;>
      first
      | exact hs.elim
      | (rw [R.trace_succ_emit h₁, R'.trace_succ_emit h₂]
         exact .cons hs.1 (trace_of_sim hstep n _ _ hs.2))
      | (rw [R.trace_succ_progress h₁, R'.trace_succ_progress h₂]
         exact .cons hs.1 (trace_of_sim hstep n _ _ hs.2))
      | (rw [R.trace_succ_done h₁, R'.trace_succ_done h₂]
         exact .cons hs .nil)

/-- Runs related by a lockstep simulation halt together. -/
theorem halts_iff_of_sim (hstep : ∀ s s', Sim s s' → StepOf.Rel E Sim (R.step s) (R'.step s')) :
    ∀ (n : Nat) {s : R.State} {s' : R'.State}, Sim s s' → (R.Halts s n ↔ R'.Halts s' n)
  | 0, s, s', _ => iff_of_false (R.halts_zero s) (R'.halts_zero s')
  | n + 1, s, s', h => by
    have hs := hstep s s' h
    cases h₁ : R.step s <;> cases h₂ : R'.step s' <;> rw [h₁, h₂] at hs <;>
      first
      | exact hs.elim
      | (rw [R.halts_succ_emit h₁, R'.halts_succ_emit h₂]
         exact halts_iff_of_sim hstep n hs.2)
      | (rw [R.halts_succ_progress h₁, R'.halts_succ_progress h₂]
         exact halts_iff_of_sim hstep n hs.2)
      | exact iff_of_true (R.halts_succ_done h₁ n) (R'.halts_succ_done h₂ n)

/-- With `StepEquiv` as the relation on emissions, the two traces agree step
for step. -/
theorem traceEquiv_of_sim {Sim : R.State → R'.State → Prop}
    (hstep : ∀ s s', Sim s s' → StepOf.Rel (StepEquiv M) Sim (R.step s) (R'.step s'))
    (n : Nat) {s : R.State} {s' : R'.State} (h : Sim s s') :
    (TraceEquiv M) (R.trace s n) (R'.trace s' n) :=
  (trace_of_sim hstep n s s' h).imp fun _ _ h => shownEquiv_iff.2 h

/-- With `StepEquiv` as the relation on emissions, what the two runs have
emitted after `n` steps agrees up to order and equivalence. -/
theorem emitted_of_sim {Sim : R.State → R'.State → Prop}
    (hstep : ∀ s s', Sim s s' → StepOf.Rel (StepEquiv M) Sim (R.step s) (R'.step s'))
    (n : Nat) {s : R.State} {s' : R'.State} (h : Sim s s') :
    (StepEquiv M) (R.emitted s n) (R'.emitted s' n) := by
  rw [R.emitted_eq_flatMap_trace, R'.emitted_eq_flatMap_trace]
  exact TraceEquiv.emits (traceEquiv_of_sim hstep n h)

end Runtime

end RwLog
