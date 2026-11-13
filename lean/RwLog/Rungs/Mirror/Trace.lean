/-
# What the mirrored machine emits

`Mir C x z` says that the run of `C` from `z` is the mirror image of its run
from `x`, step for step: the same number of steps, and at every step the same
answers up to order, equivalence and swapping. For a machine with
`Runtime.DualTrace` the first states for a query and for its mirror image are
so related.

`trace_go` is the theorem of this file: started with the leader at `x` and
the other run some steps behind a state that mirrors `x`, the mirrored
machine emits, step for step, what `C` emits from `x` (swapped back when the
leader is the run on the mirror image), and stops when `C` does. Which of the
two runs wins a race changes who the leader is, and never what is emitted.
-/
import RwLog.Rungs.Mirror.Machine
import RwLog.Rungs.Framework.Trace

namespace RwLog

theorem TraceEquiv.map_swap {t t' : List (List Span)} (h : TraceEquiv t t') :
    TraceEquiv (t.map (·.map Span.swap)) (t'.map (·.map Span.swap)) := by
  unfold TraceEquiv at *
  induction h with
  | nil => exact .nil
  | cons h _ ih => exact .cons h.map_swap ih

theorem trace_swap_swap (t : List (List Span)) :
    (t.map (·.map Span.swap)).map (·.map Span.swap) = t := by
  rw [List.map_map]
  have : ((·.map Span.swap) ∘ (·.map Span.swap) : List Span → List Span) = id :=
    funext fun xs => map_swap_swap xs
  rw [this, List.map_id]

namespace Runtime

/-- The trace of a state depends only on its first step. -/
theorem trace_congr (R : Runtime) {s s' : R.State} (h : R.step s = R.step s') (n : Nat) :
    R.trace s n = R.trace s' n := by
  cases n with
  | zero => rfl
  | succ n => simp only [trace, h]

end Runtime

namespace Mirror

variable {C : CostedRuntime}

/-! ## Orienting answers -/

theorem orient_swap (f : Bool) (xs : List Span) : orient f (xs.map Span.swap) = orient (!f) xs := by
  cases f
  · exact map_swap_swap xs
  · rfl

theorem orient_congr (f : Bool) {xs ys : List Span} (h : StepEquiv xs ys) :
    StepEquiv (orient f xs) (orient f ys) := by
  cases f
  · exact h.map_swap
  · exact h

theorem trace_orient (f : Bool) {t t' : List (List Span)} (h : TraceEquiv t t') :
    TraceEquiv (t.map (orient f)) (t'.map (orient f)) := by
  unfold TraceEquiv at *
  induction h with
  | nil => exact .nil
  | cons h _ ih => exact .cons (orient_congr f h) ih

theorem map_orient_swap (f : Bool) (t : List (List Span)) :
    (t.map (·.map Span.swap)).map (orient f) = t.map (orient (!f)) := by
  rw [List.map_map]
  exact List.map_congr_left fun xs _ => orient_swap f xs

/-! ## Mirrored runs -/

/-- The run from `z` is the mirror image of the run from `x`, step for
step. -/
def Mir (C : CostedRuntime) (x z : C.State) : Prop :=
  ∀ n, TraceEquiv (C.runtime.trace z n) ((C.runtime.trace x n).map (·.map Span.swap))

theorem Mir.symm {x z : C.State} (h : Mir C x z) : Mir C z x := by
  intro n
  have := (h n).symm.map_swap
  rwa [trace_swap_swap] at this

/-- When one run takes a step, so does its mirror image, with the same
answers swapped, and what follows is mirrored. -/
theorem Mir.emit {x z x' : C.State} {as : List Span} (h : Mir C x z)
    (hx : (C.step x).val = .emit as x') :
    ∃ bs z', (C.step z).val = .emit bs z' ∧ StepEquiv bs (as.map Span.swap) ∧ Mir C x' z' := by
  have hx' : C.runtime.step x = .emit as x' := hx
  cases hz : (C.step z).val with
  | done =>
    have h1 := h 1
    rw [C.runtime.trace_succ_done (show C.runtime.step z = .done from hz),
      C.runtime.trace_succ_emit hx'] at h1
    cases h1
  | emit bs z' =>
    have hz' : C.runtime.step z = .emit bs z' := hz
    have key : ∀ n, StepEquiv bs (as.map Span.swap) ∧
        TraceEquiv (C.runtime.trace z' n) ((C.runtime.trace x' n).map (·.map Span.swap)) := by
      intro n
      have h1 := h (n + 1)
      rw [C.runtime.trace_succ_emit hz', C.runtime.trace_succ_emit hx', List.map_cons] at h1
      cases h1 with
      | cons a b => exact ⟨a, b⟩
    exact ⟨bs, z', rfl, (key 0).1, fun n => (key n).2⟩

/-- When one run is done, so is its mirror image. -/
theorem Mir.done {x z : C.State} (h : Mir C x z) (hx : (C.step x).val = .done) :
    (C.step z).val = .done := by
  cases hz : (C.step z).val with
  | done => rfl
  | emit bs z' =>
    have h1 := h 1
    rw [C.runtime.trace_succ_emit (show C.runtime.step z = .emit bs z' from hz),
      C.runtime.trace_succ_done (show C.runtime.step x = .done from hx)] at h1
    cases h1

/-- `y` is `g` steps behind `z`. -/
def Behind (C : CostedRuntime) : Nat → C.State → C.State → Prop
  | 0, y, z => y = z
  | g + 1, y, z => ∃ as y', (C.step y).val = .emit as y' ∧ Behind C g y' z

theorem Behind.snoc {z z' : C.State} {bs : List Span} (hz : (C.step z).val = .emit bs z') :
    ∀ {g : Nat} {y : C.State}, Behind C g y z → Behind C (g + 1) y z'
  | 0, y, h => by
    have : y = z := h
    subst this
    exact ⟨bs, z', hz, rfl⟩
  | g + 1, y, ⟨as, y', hy, h⟩ => ⟨as, y', hy, Behind.snoc hz h⟩

/-! ## The trace of the mirrored machine -/

/-- The statement of `trace_go` for one number of steps. -/
def TraceGo (C : CostedRuntime) (n g : Nat) (f : Bool) (x y : C.State) : Prop :=
  TraceEquiv ((machine C).runtime.trace ⟨x, y, f, g⟩ n) ((C.runtime.trace x n).map (orient f))

/-- One more step from level runs, given the statement for one step fewer. -/
theorem trace_level {n : Nat}
    (ih : ∀ g f x y z, Behind C g y z → Mir C x z → TraceGo C n g f x y)
    (f : Bool) (x y : C.State) (hm : Mir C x y) : TraceGo C (n + 1) 0 f x y := by
  unfold TraceGo
  have alone : wins x y = true → wins y x = false →
      TraceEquiv ((machine C).runtime.trace ⟨x, y, f, 0⟩ (n + 1))
        ((C.runtime.trace x (n + 1)).map (orient f)) := by
    intro h1 h2
    cases hx : (C.step x).val with
    | emit as x' =>
      have hs : (machine C).runtime.step ⟨x, y, f, 0⟩ = .emit (orient f as) ⟨x', y, f, 1⟩ :=
        congrArg Cost.val (go_alone_emit f h1 h2 hx)
      rw [(machine C).runtime.trace_succ_emit hs,
        C.runtime.trace_succ_emit (show C.runtime.step x = .emit as x' from hx), List.map_cons]
      obtain ⟨bs, y', hy, -, hm'⟩ := hm.emit hx
      exact List.Forall₂.cons (StepEquiv.refl _) (ih 1 f x' y y' ⟨bs, y', hy, rfl⟩ hm')
    | done =>
      have hs : (machine C).runtime.step ⟨x, y, f, 0⟩ = .done :=
        congrArg Cost.val (go_alone_done f h1 h2 hx)
      rw [(machine C).runtime.trace_succ_done hs,
        C.runtime.trace_succ_done (show C.runtime.step x = .done from hx)]
      exact List.Forall₂.nil
  have over : wins x y = false → wins y x = true →
      TraceEquiv ((machine C).runtime.trace ⟨x, y, f, 0⟩ (n + 1))
        ((C.runtime.trace x (n + 1)).map (orient f)) := by
    intro h1 h2
    cases hy : (C.step y).val with
    | done =>
      have hs : (machine C).runtime.step ⟨x, y, f, 0⟩ = .done :=
        congrArg Cost.val (go_overtake_done f h1 h2 hy)
      rw [(machine C).runtime.trace_succ_done hs,
        C.runtime.trace_succ_done (show C.runtime.step x = .done from hm.symm.done hy)]
      exact List.Forall₂.nil
    | emit bs y' =>
      obtain ⟨as, x', hx, he, hm'⟩ := hm.symm.emit hy
      have hs : (machine C).runtime.step ⟨x, y, f, 0⟩ =
          .emit (orient (!f) bs) ⟨y', x, !f, 1⟩ :=
        congrArg Cost.val (go_overtake f h1 h2 hy)
      rw [(machine C).runtime.trace_succ_emit hs,
        C.runtime.trace_succ_emit (show C.runtime.step x = .emit as x' from hx), List.map_cons]
      refine List.Forall₂.cons ?_ ?_
      · rw [← orient_swap]
        exact (orient_congr f he).symm
      · have h1 : TraceGo C n 1 (!f) y' x := ih 1 (!f) y' x x' ⟨as, x', hx, rfl⟩ hm'
        refine TraceEquiv.trans h1 ?_
        have h2 := trace_orient f (hm' n).symm
        rwa [map_orient_swap] at h2
  have both : wins x y = wins y x →
      TraceEquiv ((machine C).runtime.trace ⟨x, y, f, 0⟩ (n + 1))
        ((C.runtime.trace x (n + 1)).map (orient f)) := by
    intro h
    cases hx : (C.step x).val with
    | emit as x' =>
      obtain ⟨bs, y', hy, -, hm'⟩ := hm.emit hx
      have hs : (machine C).runtime.step ⟨x, y, f, 0⟩ = .emit (orient f as) ⟨x', y', f, 0⟩ :=
        congrArg Cost.val (go_both_emit f h hx hy)
      rw [(machine C).runtime.trace_succ_emit hs,
        C.runtime.trace_succ_emit (show C.runtime.step x = .emit as x' from hx), List.map_cons]
      exact List.Forall₂.cons (StepEquiv.refl _) (ih 0 f x' y' y' rfl hm')
    | done =>
      have hs : (machine C).runtime.step ⟨x, y, f, 0⟩ = .done :=
        congrArg Cost.val (go_both_done f h (.inl hx))
      rw [(machine C).runtime.trace_succ_done hs,
        C.runtime.trace_succ_done (show C.runtime.step x = .done from hx)]
      exact List.Forall₂.nil
  cases h1 : wins x y <;> cases h2 : wins y x
  · exact both (by rw [h1, h2])
  · exact over h1 h2
  · exact alone h1 h2
  · exact both (by rw [h1, h2])

/-- One more step with the other run behind, given the statement for one step
fewer and the statement from where the other run has caught up by one. -/
theorem trace_behind {n : Nat}
    (ih : ∀ g f x y z, Behind C g y z → Mir C x z → TraceGo C n g f x y)
    (g : Nat) (f : Bool) (x y z : C.State) (hb : Behind C (g + 1) y z) (hm : Mir C x z)
    (hc : ∀ as y', (C.step y).val = .emit as y' → TraceGo C (n + 1) g f x y') :
    TraceGo C (n + 1) (g + 1) f x y := by
  unfold TraceGo
  by_cases hw : wins x y = true
  · cases hx : (C.step x).val with
    | emit as x' =>
      have hs : (machine C).runtime.step ⟨x, y, f, g + 1⟩ =
          .emit (orient f as) ⟨x', y, f, g + 2⟩ :=
        congrArg Cost.val (go_lead_emit g f hw hx)
      rw [(machine C).runtime.trace_succ_emit hs,
        C.runtime.trace_succ_emit (show C.runtime.step x = .emit as x' from hx), List.map_cons]
      obtain ⟨bs, z', hz, -, hm'⟩ := hm.emit hx
      exact List.Forall₂.cons (StepEquiv.refl _) (ih (g + 2) f x' y z' (hb.snoc hz) hm')
    | done =>
      have hs : (machine C).runtime.step ⟨x, y, f, g + 1⟩ = .done :=
        congrArg Cost.val (go_lead_done g f hw hx)
      rw [(machine C).runtime.trace_succ_done hs,
        C.runtime.trace_succ_done (show C.runtime.step x = .done from hx)]
      exact List.Forall₂.nil
  · have hw : wins x y = false := by simpa using hw
    cases hy : (C.step y).val with
    | done =>
      obtain ⟨as, y', hy', -⟩ := hb
      rw [hy] at hy'; cases hy'
    | emit bs y' =>
      have hs : (machine C).runtime.step ⟨x, y, f, g + 1⟩ =
          (machine C).runtime.step ⟨x, y', f, g⟩ := by
        show (go C (g + 1) f x y).val = (go C g f x y').val
        rw [go_catch g f hw hy]
      rw [(machine C).runtime.trace_congr hs]
      exact hc bs y' hy

/-- Started with the leader at `x` and the other run `g` steps behind a state
that mirrors `x`, the mirrored machine emits, step for step, what `C` emits
from `x`, and stops when `C` does. -/
theorem trace_go : ∀ (n g : Nat) (f : Bool) (x y z : C.State), Behind C g y z → Mir C x z →
    TraceGo C n g f x y := by
  intro n
  induction n with
  | zero => intro g f x y z _ _; exact List.Forall₂.nil
  | succ n ih =>
    intro g
    induction g with
    | zero =>
      intro f x y z hb hm
      have : y = z := hb
      subst this
      exact trace_level ih f x y hm
    | succ g ihg =>
      intro f x y z hb hm
      refine trace_behind ih g f x y z hb hm fun as y' hy => ?_
      obtain ⟨as0, y0, hy0, hb0⟩ := hb
      rw [hy] at hy0
      cases hy0
      exact ihg f x y' z hb0 hm

end Mirror

end RwLog
