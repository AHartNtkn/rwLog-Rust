/-
# The mirrored machine does not depend on direction

For a machine `C` whose run on the mirror image is the mirror image of its
run (`Runtime.DualTrace`), started on the mirror image of a query the
mirrored machine races the same two runs, the other way round. No step of it
prefers a run except for being ahead, so:

* `dualBisim`: its run on the mirror image and its run on the query cost the
  same, step for step, and emit the same answers swapped, up to order and
  equivalence. The two runs go through the same states with the sense of the
  leader reversed (`Flipped`), or, while the runs of `C` are level, with the
  two the other way round (`Swapped`).
* `convBisim`: if the runs of `C` on `conv q` and on `q` cost the same step
  for step and emit the same answers swapped, so do those of the mirrored
  machine.
* `directionFree`: so the mirrored machine pays on the mirror image and on
  the converse what it pays on the query, up to what the first states cost.
* `simulates`: and it covers what `C` covers within a quadratic bound.
-/
import RwLog.Rungs.Mirror.Bounds
import RwLog.Rungs.Framework.Direction

namespace RwLog

namespace Mirror

open Cost

variable {C : CostedRuntime}

/-! ## Orienting answers -/

theorem orient_not (f : Bool) (as : List Span) : orient (!f) as = (orient f as).map Span.swap := by
  cases f
  · exact (map_swap_swap as).symm
  · rfl

theorem orient_map_swap (f : Bool) (as : List Span) :
    orient f (as.map Span.swap) = (orient f as).map Span.swap := by
  cases f <;> rfl

theorem orient_true : (orient true : List Span → List Span) = id := rfl

/-! ## The first state -/

theorem start_eq (P : Program) (q : Rel) :
    (machine C).start P q = ⟨C.start P q, C.start P.dual q.dual, true, 0⟩ := rfl

theorem init_ticks (P : Program) (q : Rel) :
    ((machine C).init P q).ticks = (C.init P q).ticks + (C.init P.dual q.dual).ticks := by
  show (C.init P q).ticks + ((C.init P.dual q.dual).ticks + 0) = _
  omega

theorem mir_start (hdual : C.runtime.DualTrace) {P : Program} {q : Rel} (hwf : P.WellFormed q) :
    Mir C (C.start P q) (C.start P.dual q.dual) := fun n => hdual P q n hwf.2.2

/-! ## The run on the mirror image -/

/-- The same two runs, with the sense of the leader reversed. -/
def Flipped (s t : StOf C.State) : Prop := t = ⟨s.lead, s.lag, !s.fwd, s.gap⟩

/-- The same two runs, level, the other way round. -/
def Swapped (s t : StOf C.State) : Prop :=
  s.gap = 0 ∧ t = ⟨s.lag, s.lead, s.fwd, 0⟩ ∧ Mir C s.lead s.lag

/-- How the state of the run on the mirror image is related to the state of
the run on the query. -/
def Dual (s t : StOf C.State) : Prop := Flipped s t ∨ Swapped s t

/-- Answers swapped, up to order and equivalence. -/
abbrev SwapEquiv (xs ys : List Span) : Prop := StepEquiv xs (ys.map Span.swap)

theorem level_flip (f : Bool) (x y : C.State) (r r' : Step C.State ⊕ Step C.State) :
    Step.Rel SwapEquiv Dual (level f x y r r') (level (!f) x y r r') := by
  have e : ∀ as : List Span, SwapEquiv (orient f as) (orient (!f) as) := fun as => by
    show StepEquiv _ _
    rw [orient_not, map_swap_swap]; exact StepEquiv.refl _
  rcases r with (_ | _) | (_ | _) <;> rcases r' with (_ | _) | (_ | _) <;>
    first
    | exact trivial
    | exact ⟨e _, .inl rfl⟩
    | exact ⟨by rw [Bool.not_not]; show StepEquiv _ _
                rw [← orient_not]; exact StepEquiv.refl _, .inl rfl⟩

/-- With the sense of the leader reversed, a step costs the same and emits
the same answers swapped. -/
theorem go_flip : ∀ (g : Nat) (f : Bool) (x y : C.State),
    (go C g f x y).ticks = (go C g (!f) x y).ticks ∧
      Step.Rel SwapEquiv Dual (go C g f x y).val (go C g (!f) x y).val
  | 0, f, x, y => by
    rw [go_zero, go_zero]
    exact ⟨rfl, level_flip f x y _ _⟩
  | g + 1, f, x, y => by
    have e : ∀ as : List Span, SwapEquiv (orient f as) (orient (!f) as) := fun as => by
      show StepEquiv _ _
      rw [orient_not, map_swap_swap]; exact StepEquiv.refl _
    by_cases hw : wins x y = true
    · cases hx : (C.step x).val with
      | emit as x' =>
        rw [go_lead_emit g f hw hx, go_lead_emit g (!f) hw hx]
        exact ⟨rfl, e as, .inl rfl⟩
      | done =>
        rw [go_lead_done g f hw hx, go_lead_done g (!f) hw hx]
        exact ⟨rfl, trivial⟩
    · have hw : wins x y = false := by simpa using hw
      cases hy : (C.step y).val with
      | done =>
        rw [go_lag_done g f hw hy, go_lag_done g (!f) hw hy]
        exact ⟨rfl, trivial⟩
      | emit bs y' =>
        rw [go_catch g f hw hy, go_catch g (!f) hw hy]
        obtain ⟨h1, h2⟩ := go_flip g f x y'
        exact ⟨by show _ + _ = _ + _; rw [h1], h2⟩

/-- Level runs the other way round: a step costs the same and emits the same
answers swapped, up to order and equivalence. -/
theorem go_swap (f : Bool) (x y : C.State) (hm : Mir C x y) :
    (go C 0 f x y).ticks = (go C 0 f y x).ticks ∧
      Step.Rel SwapEquiv Dual (go C 0 f x y).val (go C 0 f y x).val := by
  have e : ∀ as : List Span, SwapEquiv (orient f as) (orient (!f) as) := fun as => by
    show StepEquiv _ _
    rw [orient_not, map_swap_swap]; exact StepEquiv.refl _
  have e' : ∀ as : List Span, SwapEquiv (orient (!f) as) (orient f as) := fun as => by
    show StepEquiv _ _
    rw [← orient_not]; exact StepEquiv.refl _
  have ht : (go C 0 f x y).ticks = (go C 0 f y x).ticks := by
    rw [go_zero, go_zero]; show 1 + raced x y + raced y x = 1 + raced y x + raced x y; omega
  refine ⟨ht, ?_⟩
  have alone : wins x y = true → wins y x = false →
      Step.Rel SwapEquiv Dual (go C 0 f x y).val (go C 0 f y x).val := by
    intro h1 h2
    cases hx : (C.step x).val with
    | emit as x' =>
      rw [go_alone_emit f h1 h2 hx, go_overtake f h2 h1 hx]
      exact ⟨e as, .inl rfl⟩
    | done =>
      rw [go_alone_done f h1 h2 hx, go_overtake_done f h2 h1 hx]
      exact trivial
  have over : wins x y = false → wins y x = true →
      Step.Rel SwapEquiv Dual (go C 0 f x y).val (go C 0 f y x).val := by
    intro h1 h2
    cases hy : (C.step y).val with
    | emit bs y' =>
      rw [go_overtake f h1 h2 hy, go_alone_emit f h2 h1 hy]
      exact ⟨e' bs, .inl (by show _ = StOf.mk y' x (!(!f)) 1; rw [Bool.not_not])⟩
    | done =>
      rw [go_overtake_done f h1 h2 hy, go_alone_done f h2 h1 hy]
      exact trivial
  have both : wins x y = wins y x →
      Step.Rel SwapEquiv Dual (go C 0 f x y).val (go C 0 f y x).val := by
    intro h
    cases hx : (C.step x).val with
    | emit as x' =>
      obtain ⟨bs, y', hy, he, hm'⟩ := hm.emit hx
      rw [go_both_emit f h hx hy, go_both_emit f h.symm hy hx]
      refine ⟨?_, .inr ⟨rfl, rfl, hm'⟩⟩
      show StepEquiv _ _
      rw [← orient_map_swap]
      refine orient_congr f ?_
      have := he.map_swap.symm
      rwa [map_swap_swap] at this
    | done =>
      rw [go_both_done f h (.inl hx), go_both_done f h.symm (.inr hx)]
      exact trivial
  cases h1 : wins x y <;> cases h2 : wins y x
  · exact both (by rw [h1, h2])
  · exact over h1 h2
  · exact alone h1 h2
  · exact both (by rw [h1, h2])

/-- The run of the mirrored machine on the mirror image costs what its run on
the query costs, step for step, and emits the same answers swapped. -/
theorem dualBisim (hdual : C.runtime.DualTrace) : DualBisim (machine C) Dual where
  ticks s t h := by
    rcases h with h | ⟨hg, h, hm⟩
    · subst h; exact (go_flip s.gap s.fwd s.lead s.lag).1
    · subst h
      show (go C s.gap s.fwd s.lead s.lag).ticks = (go C 0 s.fwd s.lag s.lead).ticks
      rw [hg]; exact (go_swap s.fwd s.lead s.lag hm).1
  step s t h := by
    rcases h with h | ⟨hg, h, hm⟩
    · subst h; exact (go_flip s.gap s.fwd s.lead s.lag).2
    · subst h
      show Step.Rel SwapEquiv Dual (go C s.gap s.fwd s.lead s.lag).val
        (go C 0 s.fwd s.lag s.lead).val
      rw [hg]; exact (go_swap s.fwd s.lead s.lag hm).2
  start P q hwf := by
    refine .inr ⟨rfl, ?_, mir_start hdual hwf⟩
    show (machine C).start P.dual q.dual = _
    rw [start_eq, ProgramOf.dual_dual, RelOf.dual_dual]
    rfl

/-! ## The run on the converse -/

/-- The two runs are related, each to each. -/
def Lift (rel : C.State → C.State → Prop) (s t : StOf C.State) : Prop :=
  s.gap = t.gap ∧ s.fwd = t.fwd ∧ rel s.lead t.lead ∧ rel s.lag t.lag

/-- Answers swapped. -/
abbrev Swaps (xs ys : List Span) : Prop := xs = ys.map Span.swap

section Conv

variable {rel : C.State → C.State → Prop} (h : CostBisim C C Swaps rel)
include h

theorem conv_wins {x y x' y' : C.State} (hx : rel x x') (hy : rel y y') :
    wins x y = wins x' y' ∧ raced x y = raced x' y' := by
  unfold wins raced
  rw [h.ticks x x' hx, h.ticks y y' hy]
  exact ⟨rfl, rfl⟩

theorem conv_level (f : Bool) {x y x' y' : C.State} (hx : rel x x') (hy : rel y y')
    (b b' : Bool) :
    Step.Rel Swaps (Lift rel)
      (level f x y (if b then .inl (C.step x).val else .inr (C.step y).val)
        (if b' then .inr (C.step y).val else .inl (C.step x).val))
      (level f x' y' (if b then .inl (C.step x').val else .inr (C.step y').val)
        (if b' then .inr (C.step y').val else .inl (C.step x').val)) := by
  have sx := h.step x x' hx
  have sy := h.step y y' hy
  cases h1 : (C.step x).val <;> cases h1' : (C.step x').val <;> rw [h1, h1'] at sx <;>
    cases h2 : (C.step y).val <;> cases h2' : (C.step y').val <;> rw [h2, h2'] at sy <;>
    cases b <;> cases b' <;>
    first
    | exact sx.elim
    | exact sy.elim
    | exact trivial
    | exact ⟨by rw [sx.1]; exact orient_map_swap _ _, rfl, rfl, sx.2, hy⟩
    | exact ⟨by rw [sy.1]; exact orient_map_swap _ _, rfl, rfl, sy.2, hx⟩
    | exact ⟨by rw [sx.1]; exact orient_map_swap _ _, rfl, rfl, sx.2, sy.2⟩

theorem conv_go : ∀ (g : Nat) (f : Bool) (x y x' y' : C.State), rel x x' → rel y y' →
    (go C g f x y).ticks = (go C g f x' y').ticks ∧
      Step.Rel Swaps (Lift rel) (go C g f x y).val (go C g f x' y').val
  | 0, f, x, y, x', y', hx, hy => by
    obtain ⟨w1, r1⟩ := conv_wins h hx hy
    obtain ⟨w2, r2⟩ := conv_wins h hy hx
    rw [go_zero, go_zero, w1, w2, r1, r2]
    exact ⟨rfl, conv_level h f hx hy _ _⟩
  | g + 1, f, x, y, x', y', hx, hy => by
    obtain ⟨w1, r1⟩ := conv_wins h hx hy
    have sx := h.step x x' hx
    have sy := h.step y y' hy
    by_cases hw : wins x y = true
    · have hw' : wins x' y' = true := w1 ▸ hw
      cases h1 : (C.step x).val <;> cases h1' : (C.step x').val <;> rw [h1, h1'] at sx
      · rw [go_lead_emit g f hw h1, go_lead_emit g f hw' h1', r1]
        exact ⟨rfl, by rw [sx.1]; exact orient_map_swap _ _, rfl, rfl, sx.2, hy⟩
      · exact sx.elim
      · exact sx.elim
      · rw [go_lead_done g f hw h1, go_lead_done g f hw' h1', r1]
        exact ⟨rfl, trivial⟩
    · have hw : wins x y = false := by simpa using hw
      have hw' : wins x' y' = false := w1 ▸ hw
      cases h2 : (C.step y).val <;> cases h2' : (C.step y').val <;> rw [h2, h2'] at sy
      · rw [go_catch g f hw h2, go_catch g f hw' h2', r1]
        obtain ⟨t, s⟩ := conv_go g f _ _ _ _ hx sy.2
        exact ⟨by show _ + _ = _ + _; rw [t], s⟩
      · exact sy.elim
      · exact sy.elim
      · rw [go_lag_done g f hw h2, go_lag_done g f hw' h2', r1]
        exact ⟨rfl, trivial⟩

end Conv

/-- If the runs of `C` on `conv q` and on `q` cost the same, step for step,
and emit the same answers swapped, so do those of the mirrored machine. -/
theorem convBisim {rel : C.State → C.State → Prop} (h : ConvBisim C rel) :
    ConvBisim (machine C) (Lift rel) where
  ticks s t hr := by
    obtain ⟨hg, hf, hl, hla⟩ := hr
    show (go C s.gap s.fwd s.lead s.lag).ticks = (go C t.gap t.fwd t.lead t.lag).ticks
    rw [hg, hf]; exact (conv_go h.toCostBisim t.gap t.fwd _ _ _ _ hl hla).1
  step s t hr := by
    obtain ⟨hg, hf, hl, hla⟩ := hr
    show Step.Rel Swaps (Lift rel) (go C s.gap s.fwd s.lead s.lag).val
      (go C t.gap t.fwd t.lead t.lag).val
    rw [hg, hf]; exact (conv_go h.toCostBisim t.gap t.fwd _ _ _ _ hl hla).2
  start P q := ⟨rfl, rfl, h.start P q, h.start P.dual q.dual⟩

/-! ## Direction independence -/

/-- The mirrored machine does not depend on direction: on the mirror image
and on the converse it pays what it pays on the query, and for the converse
what the two first states cost more. -/
theorem directionFree {rel : C.State → C.State → Prop} {k : Nat}
    (hdual : C.runtime.DualTrace) (hconv : ConvBisim C rel)
    (hci : ∀ P q, (C.init P (.conv q)).ticks ≤ (C.init P q).ticks + k)
    (hci' : ∀ P q, (C.init P q).ticks ≤ (C.init P (.conv q)).ticks) :
    DirectionFree (machine C) fun c _ => c + 2 * k := by
  refine DirectionFree.of_bisim (dualBisim hdual) (convBisim hconv) (fun P q => ?_)
    (fun P q => ?_) fun P q => ?_
  · rw [init_ticks, init_ticks, ProgramOf.dual_dual, RelOf.dual_dual]; omega
  · rw [init_ticks, init_ticks]
    have := hci P q
    have := hci P.dual q.dual
    show _ + (C.init P.dual (.conv q.dual)).ticks ≤ _
    omega
  · rw [init_ticks, init_ticks]
    have := hci' P q
    have := hci' P.dual q.dual
    show _ ≤ _ + (C.init P.dual (.conv q.dual)).ticks
    omega

/-! ## Never much worse -/

/-- What the mirrored machine pays, in terms of what `C` has paid and of the
size of the input. -/
def bound (c n : Nat) : Nat := c + n + 2 * (c + 1) * (1 + 14 * c)

/-- The mirrored machine emits what `C` emits, step for step. -/
theorem trace_start (hdual : C.runtime.DualTrace) {P : Program} {q : Rel} (hwf : P.WellFormed q)
    (n : Nat) :
    TraceEquiv ((machine C).runtime.trace ((machine C).start P q) n)
      (C.runtime.trace (C.start P q) n) := by
  have := trace_go n 0 true (C.start P q) (C.start P.dual q.dual) _ rfl (mir_start hdual hwf)
  unfold TraceGo at this
  rwa [orient_true, List.map_id] at this

/-- The first `n` steps of the mirrored machine cost at most the two first
states and `2 n` rounds, each of at most one tick more than 14 times the
cheaper of the first `n` steps of `C` on the query and on its mirror
image. -/
theorem paid_le_min (P : Program) (q : Rel) (n : Nat) :
    (machine C).paid P q n ≤ (C.init P q).ticks + (C.init P.dual q.dual).ticks +
      2 * n * (1 + 14 * min (C.spent (C.start P q) n) (C.spent (C.start P.dual q.dual) n)) := by
  have h := spent_le n 0 true (C.start P q) (C.start P.dual q.dual)
  unfold SpentLe at h
  rw [Nat.add_zero, Nat.zero_add] at h
  show ((machine C).init P q).ticks + (machine C).spent ((machine C).start P q) n ≤ _
  rw [init_ticks, start_eq]
  omega

/-- The first `n` steps of the mirrored machine, in terms of the first `n`
steps of `C` on the query. -/
theorem paid_le (P : Program) (q : Rel) (n : Nat) :
    (machine C).paid P q n ≤ (C.init P q).ticks + (C.init P.dual q.dual).ticks +
      2 * n * (1 + 14 * C.spent (C.start P q) n) := by
  have h := paid_le_min (C := C) P q n
  have h2 : 2 * n * (1 + 14 * min (C.spent (C.start P q) n)
      (C.spent (C.start P.dual q.dual) n)) ≤ 2 * n * (1 + 14 * C.spent (C.start P q) n) :=
    Nat.mul_le_mul (Nat.le_refl _)
      (Nat.add_le_add_left (Nat.mul_le_mul_left 14 (Nat.min_le_left _ _)) 1)
  omega

/-- What the first step of `C` on the mirror image relates, swapped, the
first step of the mirrored machine on the query relates. -/
theorem covered_first (hdual : C.runtime.DualTrace) {P : Program} {q : Rel} (hwf : P.WellFormed q)
    {as : List Span} {s' : C.State}
    (hs : (C.step (C.start P.dual q.dual)).val = .emit as s') {a : Span} (ha : a ∈ as)
    {M : Interp} {x : GTerm × GTerm} (hx : (x.2, x.1) ∈ a.denAt M) :
    (machine C).Covered P q M x 1 := by
  have h1 := mir_start hdual hwf 1
  rw [C.runtime.trace_succ_emit (show C.runtime.step (C.start P.dual q.dual) = .emit as s' from hs)]
    at h1
  have h2 := trace_start hdual hwf 1
  cases hx0 : (C.step (C.start P q)).val with
  | done =>
    rw [C.runtime.trace_succ_done (show C.runtime.step (C.start P q) = .done from hx0)] at h1
    cases h1
  | emit bs x' =>
    rw [C.runtime.trace_succ_emit (show C.runtime.step (C.start P q) = .emit bs x' from hx0)]
      at h1 h2
    cases hm : ((machine C).step ((machine C).start P q)).val with
    | done =>
      rw [(machine C).runtime.trace_succ_done
        (show (machine C).runtime.step ((machine C).start P q) = .done from hm)] at h2
      cases h2
    | emit ms m' =>
      have hm' : (machine C).runtime.step ((machine C).start P q) = .emit ms m' := hm
      rw [(machine C).runtime.trace_succ_emit hm'] at h2
      rw [List.map_cons] at h1
      obtain ⟨e1, -⟩ := List.forall₂_cons.1 h1
      obtain ⟨e2, -⟩ := List.forall₂_cons.1 h2
      obtain ⟨b', hb', eb⟩ := e1.mem ha
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hb'
      obtain ⟨m, hm0, em⟩ := e2.symm.mem hb
      refine ⟨m, ?_, em.2.at_subset M (Span.mem_denAt_swap.1 (eb.2.at_subset M hx))⟩
      show m ∈ ((machine C).runtime.run ((machine C).start P q) 1).1
      rw [(machine C).runtime.run_succ_emit hm']
      exact List.mem_append_left _ hm0

/-- The mirrored machine simulates `C` within `bound`, for a machine whose
first state costs at most the size of the input and whose emitting steps cost
at least a tick each. -/
theorem simulates (hdual : C.runtime.DualTrace)
    (hinit : ∀ P q, (C.init P q).ticks ≤ P.size + q.size)
    (hpos : ∀ s as s', (C.step s).val = .emit as s' → 1 ≤ (C.step s).ticks) :
    Simulates C (machine C) bound := by
  refine simulates_of_trace fun P q hwf => ⟨trace_start hdual hwf, fun n m hmn hm => ?_⟩
  have h1 := paid_le (C := C) P q m
  have h2 := C.trace_length_le_spent hpos n (C.start P q)
  have h3 := C.spent_mono (C.start P q) hmn
  have h4 := hinit P.dual q.dual
  rw [ProgramOf.size_dual, RelOf.size_dual] at h4
  generalize C.spent (C.start P q) m = Sm at h1 h3
  have hc : C.paid P q n = (C.init P q).ticks + C.spent (C.start P q) n := rfl
  generalize C.spent (C.start P q) n = S at h2 h3 hc
  generalize C.paid P q n = c at hc
  have h5 : 2 * m * (1 + 14 * Sm) ≤ 2 * (c + 1) * (1 + 14 * c) :=
    Nat.mul_le_mul (by omega) (by omega)
  unfold bound
  omega

end Mirror

end RwLog
