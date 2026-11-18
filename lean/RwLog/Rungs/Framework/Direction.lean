/-
# Direction: the mirror image and the converse of a run

Facts used to establish `DirectionFree` (`Trusted/Cost.lean`).

* The mirror image: `dual` is an involution and keeps sizes and
  well-formedness; a swapped span relates the swapped pairs.
* `C.mirror` and `C.conv` spend what `C` spends and emit its answers swapped.
* `neverWorse_of_trace`: a machine whose trace agrees with another's, step for
  step, is never worse than it within any bound on what it has paid by the
  step the other has reached. A run is only followed as far as it shows
  something, and one step further when it stops, so the bound is needed for
  those steps only.
-/
import RwLog.Rungs.Framework.Covering
import RwLog.Rungs.Framework.Trace
import RwLog.Rungs.Framework.Cost
import RwLog.Kernel.Size
import RwLog.SpanLayer.Sorts

namespace RwLog

/-! ## The mirror image -/

theorem Span.mem_denAt_swap {M : Interp} {a : Span} {x : GTerm × GTerm} :
    x ∈ a.swap.denAt M ↔ (x.2, x.1) ∈ a.denAt M := by
  constructor <;> rintro ⟨σ, h1, h2, h3⟩ <;> exact ⟨σ, h2, h1, h3⟩

theorem RelOf.dual_dual : ∀ e : Rel, e.dual.dual = e
  | .zero => rfl
  | .span s => rfl
  | .or a b => by simp only [RelOf.dual, dual_dual a, dual_dual b]
  | .and a b => by simp only [RelOf.dual, dual_dual a, dual_dual b]
  | .seq a b => by simp only [RelOf.dual, dual_dual a, dual_dual b]
  | .conv a => by simp only [RelOf.dual, dual_dual a]
  | .call _ => rfl

theorem ProgramOf.dual_dual (P : Program) : P.dual.dual = P := by
  cases P with
  | mk defs sorts =>
    simp only [ProgramOf.dual, List.map_map]
    congr 1
    conv => rhs; rw [← List.map_id defs]
    exact List.map_congr_left fun d _ => by simp [RelOf.dual_dual]

theorem RelOf.size_dual : ∀ e : Rel, e.dual.size = e.size
  | .zero => rfl
  | .span s => by simp only [RelOf.dual, RelOf.size, Span.size_swap]
  | .or a b => by simp only [RelOf.dual, RelOf.size, size_dual a, size_dual b]
  | .and a b => by simp only [RelOf.dual, RelOf.size, size_dual a, size_dual b]
  | .seq a b => by simp only [RelOf.dual, RelOf.size, size_dual a, size_dual b]; omega
  | .conv a => by simp only [RelOf.dual, RelOf.size, size_dual a]
  | .call _ => rfl

theorem ProgramOf.size_dual (P : Program) : P.dual.size = P.size := by
  simp only [ProgramOf.size, ProgramOf.dual, List.map_map]
  congr 2
  exact List.map_congr_left fun d _ => by simp [RelOf.size_dual]

theorem RelOf.mem_calls_dual {n : Name} : ∀ e : Rel, n ∈ e.dual.calls ↔ n ∈ e.calls
  | .zero => Iff.rfl
  | .span _ => Iff.rfl
  | .or a b => by simp only [RelOf.dual, RelOf.calls, List.mem_append, mem_calls_dual a, mem_calls_dual b]
  | .and a b => by simp only [RelOf.dual, RelOf.calls, List.mem_append, mem_calls_dual a, mem_calls_dual b]
  | .seq a b => by
    simp only [RelOf.dual, RelOf.calls, List.mem_append, mem_calls_dual a, mem_calls_dual b]
    exact or_comm
  | .conv a => by simp only [RelOf.dual, RelOf.calls, mem_calls_dual a]
  | .call _ => Iff.rfl

/-- The spans of the mirror image are the spans, swapped. -/
theorem RelOf.mem_spans_dual : ∀ (e : Rel) {s : Span}, s ∈ e.dual.spans ↔ s.swap ∈ e.spans
  | .zero => by simp [RelOf.dual, RelOf.spans]
  | .span t => by
    simp only [RelOf.dual, RelOf.spans, List.mem_singleton]
    exact ⟨fun h => by rw [h]; rfl, fun h => by rw [← h]; rfl⟩
  | .or a b => by
    simp only [RelOf.dual, RelOf.spans, List.mem_append, mem_spans_dual a, mem_spans_dual b]
  | .and a b => by
    simp only [RelOf.dual, RelOf.spans, List.mem_append, mem_spans_dual a, mem_spans_dual b]
  | .seq a b => by
    simp only [RelOf.dual, RelOf.spans, List.mem_append, mem_spans_dual a, mem_spans_dual b]
    exact or_comm
  | .conv a => by simp only [RelOf.dual, RelOf.spans, mem_spans_dual a]
  | .call _ => by simp [RelOf.dual, RelOf.spans]

theorem ProgramOf.WellFormed.dual {P : Program} {q : Rel} (h : P.WellFormed q) :
    P.dual.WellFormed q.dual := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hfst : P.dual.defs.map Prod.fst = P.defs.map Prod.fst := by
    simp only [ProgramOf.dual, List.map_map]
    exact List.map_congr_left fun d _ => rfl
  have h5 : ∀ s ∈ q.dual.spans ++ (P.dual.defs.flatMap fun d => d.2.spans),
      s.firstOrder = true := by
    intro s hs
    rw [← Span.firstOrder_swap]
    refine h4 _ ?_
    rcases List.mem_append.1 hs with hs | hs
    · exact List.mem_append_left _ ((RelOf.mem_spans_dual q).1 hs)
    · refine List.mem_append_right _ ?_
      obtain ⟨d, hd, hsd⟩ := List.mem_flatMap.1 hs
      simp only [ProgramOf.dual, List.mem_map] at hd
      obtain ⟨d0, hd0, rfl⟩ := hd
      exact List.mem_flatMap.2 ⟨d0, hd0, (RelOf.mem_spans_dual d0.2).1 hsd⟩
  refine ⟨by rw [hfst]; exact h1, fun n hn => ?_, h3, h5⟩
  rw [hfst]
  refine h2 n ?_
  rcases List.mem_append.1 hn with hn | hn
  · exact List.mem_append_left _ ((RelOf.mem_calls_dual q).1 hn)
  · refine List.mem_append_right _ ?_
    obtain ⟨d, hd, hnd⟩ := List.mem_flatMap.1 hn
    simp only [ProgramOf.dual, List.mem_map] at hd
    obtain ⟨d0, hd0, rfl⟩ := hd
    exact List.mem_flatMap.2 ⟨d0, hd0, (RelOf.mem_calls_dual d0.2).1 hnd⟩

/-! ## Runs, as far as they show -/

namespace Runtime

variable (R : Runtime)

/-- Running for as many steps as the trace is long gives the same trace: a
trace is shorter than the number of steps only when the run is done. -/
theorem trace_trace_length : ∀ (n : Nat) (s : R.State),
    R.trace s (R.trace s n).length = R.trace s n
  | 0, _ => rfl
  | n + 1, s => by
    cases hs : R.step s with
    | done fin => rw [R.trace_succ_done hs]; exact R.trace_succ_done hs 0
    | emit as s' =>
      rw [R.trace_succ_emit hs, List.length_cons, R.trace_succ_emit hs, trace_trace_length n s']

/-- Two numbers of steps with the same trace have emitted the same answers
and halted together. -/
theorem emitted_eq_of_trace {s : R.State} {m n : Nat} (h : R.trace s m = R.trace s n) :
    R.emitted s m = R.emitted s n := by
  rw [R.emitted_eq_flatMap_trace, R.emitted_eq_flatMap_trace, h]

theorem halts_iff_trace {s : R.State} {n : Nat} :
    R.Halts s n ↔ ∃ fin, (R.trace s n).getLast? = some (.final fin) := by
  rw [R.halts_iff_final]
  exact exists_congr fun fin => R.final_eq_some_iff n s fin

end Runtime

/-- Traces that agree step for step end with a final report together. -/
theorem TraceEquiv.final {A B : Type} [Answer A] [Answer B] {M : Interp} :
    ∀ {t : List (Shown A)} {t' : List (Shown B)}, TraceEquiv M t t' →
      (∃ fin, t'.getLast? = some (.final fin)) → ∃ fin, t.getLast? = some (.final fin)
  | _, _, .nil, ⟨_, h⟩ => by simp at h
  | _, _, .cons (a := x) (b := y) h .nil, ⟨fin, hf⟩ => by
    simp only [List.getLast?_singleton, Option.some.injEq] at hf
    subst hf
    cases x with
    | final xs => exact ⟨xs, rfl⟩
    | answers xs => exact h.elim
  | _, _, .cons _ (.cons h' hs), ⟨fin, hf⟩ => by
    rw [List.getLast?_cons_cons] at hf ⊢
    exact TraceEquiv.final (.cons h' hs) ⟨fin, hf⟩

/-! ## Well-formed queries -/

/-- A query that calls and writes no more than a well-formed one is well
formed. -/
theorem ProgramOf.WellFormed.of_sub {P : Program} {q q' : Rel} (h : P.WellFormed q)
    (hc : ∀ n ∈ q'.calls, n ∈ q.calls) (hs : ∀ s ∈ q'.spans, s ∈ q.spans) :
    P.WellFormed q' := by
  refine ⟨h.1, fun n hn => h.2.1 n ?_, h.2.2.1, fun s hs' => h.2.2.2 s ?_⟩
  · rcases List.mem_append.1 hn with hn | hn
    · exact List.mem_append_left _ (hc n hn)
    · exact List.mem_append_right _ hn
  · rcases List.mem_append.1 hs' with hs' | hs'
    · exact List.mem_append_left _ (hs s hs')
    · exact List.mem_append_right _ hs'

theorem ProgramOf.WellFormed.conv {P : Program} {q : Rel} (h : P.WellFormed q) :
    P.WellFormed (.conv q) :=
  h.of_sub (fun _ h => h) (fun _ h => h)

theorem ProgramOf.WellFormed.seq_left {P : Program} {a b : Rel} (h : P.WellFormed (.seq a b)) :
    P.WellFormed a :=
  h.of_sub (fun _ h => List.mem_append_left _ h) (fun _ h => List.mem_append_left _ h)

theorem ProgramOf.WellFormed.seq_swap {P : Program} {a b : Rel} (h : P.WellFormed (.seq a b)) :
    P.WellFormed (.seq b a) :=
  h.of_sub
    (fun _ h => (List.mem_append.1 h).elim (List.mem_append_right _) (List.mem_append_left _))
    (fun _ h => (List.mem_append.1 h).elim (List.mem_append_right _) (List.mem_append_left _))

theorem ProgramOf.WellFormed.and_of_seq {P : Program} {a b : Rel} (h : P.WellFormed (.seq a b)) :
    P.WellFormed (.and a b) :=
  h.of_sub (fun _ h => h) (fun _ h => h)

/-- Swapping every answer keeps two traces in agreement. -/
theorem TraceEquiv.map_swap {A B : Type} [Answer A] [Answer B] {M : Interp}
    {t : List (Shown A)} {t' : List (Shown B)}
    (h : TraceEquiv M t t') : TraceEquiv M (t.map Shown.swap) (t'.map Shown.swap) :=
  List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2
    (List.Forall₂.imp (fun _ _ h => h.swap) h))

/-- Swapping twice gives equivalent answers. -/
theorem StepEquiv.swap_swap {A : Type} [Answer A] (M : Interp) (xs : List A) :
    StepEquiv M ((xs.map Answer.swap).map Answer.swap) xs := by
  refine StepEquiv.of_forall₂ ?_
  rw [List.map_map, List.forall₂_map_left_iff]
  refine List.forall₂_same.2 fun a _ => ?_
  have h : Answer.den M (Answer.swap (Answer.swap a)) = Answer.den M a := by
    rw [Answer.den_swap, Answer.den_swap]; rfl
  exact ⟨h.ge, h.le⟩

namespace CostedRuntime

variable (C : CostedRuntime)

/-- A machine whose steps each cost a tick has spent at least one tick per
step it has shown. -/
theorem trace_length_le_spent (hpos : ∀ s, 1 ≤ (C.step s).ticks) :
    ∀ (n : Nat) (s : C.State), (C.runtime.trace s n).length ≤ C.spent s n
  | 0, _ => Nat.le_refl 0
  | n + 1, s => by
    have := hpos s
    cases hs : (C.step s).val with
    | done fin =>
      rw [C.runtime.trace_succ_done (show C.runtime.step s = .done fin from hs),
        C.spent_succ_done hs]
      simpa using this
    | emit as s' =>
      rw [C.runtime.trace_succ_emit (show C.runtime.step s = .emit as s' from hs),
        C.spent_succ_emit hs]
      have := trace_length_le_spent hpos n s'
      simp only [List.length_cons]
      omega

/-! ## The machine on the mirror image and on the converse -/

/-- `C` with every answer swapped and another way to build the first state:
`C.mirror` and `C.conv` are both of this form. -/
def swapped (init : Program → Rel → Cost C.State) : CostedRuntime where
  Ans := C.Ans
  State := C.State
  init := init
  step s := ⟨(C.step s).val.swap, (C.step s).ticks, (C.step s).peak, (C.step s).held,
    (C.step s).held_le⟩
  live := C.live

theorem swapped_spent (init : Program → Rel → Cost C.State) : ∀ (n : Nat) (s : C.State), (C.swapped init).spent s n = C.spent s n
  | 0, _ => rfl
  | n + 1, s => by
    cases hs : (C.step s).val with
    | done fin =>
      have hs' : ((C.swapped init).step s).val = .done (fin.map Answer.swap) := by
        show (C.step s).val.swap = _; rw [hs]; rfl
      rw [(C.swapped init).spent_succ_done hs', C.spent_succ_done hs]; rfl
    | emit as s' =>
      have hs' : ((C.swapped init).step s).val = .emit (as.map Answer.swap) s' := by
        show (C.step s).val.swap = _; rw [hs]; rfl
      rw [(C.swapped init).spent_succ_emit hs', C.spent_succ_emit hs]
      exact congrArg ((C.step s).ticks + ·) (swapped_spent init n s')

theorem swapped_trace (init : Program → Rel → Cost C.State) : ∀ (n : Nat) (s : C.State),
    (C.swapped init).runtime.trace s n = (C.runtime.trace s n).map Shown.swap
  | 0, _ => rfl
  | n + 1, s => by
    cases hs : (C.step s).val with
    | done fin =>
      have hs' : (C.swapped init).runtime.step s = .done (fin.map Answer.swap) := by
        show (C.step s).val.swap = _; rw [hs]; rfl
      rw [(C.swapped init).runtime.trace_succ_done hs',
        C.runtime.trace_succ_done (show C.runtime.step s = .done fin from hs)]; rfl
    | emit as s' =>
      have hs' : (C.swapped init).runtime.step s = .emit (as.map Answer.swap) s' := by
        show (C.step s).val.swap = _; rw [hs]; rfl
      rw [(C.swapped init).runtime.trace_succ_emit hs',
        C.runtime.trace_succ_emit (show C.runtime.step s = .emit as s' from hs), List.map_cons]
      exact congrArg (Shown.answers (as.map Answer.swap) :: ·) (swapped_trace init n s')

theorem mirror_spent (n : Nat) (s : C.State) : C.mirror.spent s n = C.spent s n :=
  C.swapped_spent _ n s

theorem mirror_trace (n : Nat) (s : C.State) :
    C.mirror.runtime.trace s n = (C.runtime.trace s n).map Shown.swap :=
  C.swapped_trace _ n s

theorem mirror_paid (P : Program) (q : Rel) (n : Nat) :
    C.mirror.paid P q n = C.paid P.dual q.dual n := by
  exact congrArg ((C.init P.dual q.dual).ticks + ·) (C.mirror_spent n _)

theorem conv_spent (n : Nat) (s : C.State) : C.conv.spent s n = C.spent s n :=
  C.swapped_spent _ n s

theorem conv_trace (n : Nat) (s : C.State) :
    C.conv.runtime.trace s n = (C.runtime.trace s n).map Shown.swap :=
  C.swapped_trace _ n s

theorem conv_paid (P : Program) (q : Rel) (n : Nat) :
    C.conv.paid P q n = C.paid P (.conv q) n := by
  exact congrArg ((C.init P (.conv q)).ticks + ·) (C.conv_spent n _)

end CostedRuntime

/-! ## Never worse, from equal traces -/

/-- `B` is never worse than `A` within `p` when, on every input, the trace of
`B` agrees with the trace of `A` step for step, and `B` has paid at most `p`
of what `A` has paid by any step up to the last that `A` has shown. A run is
only followed as far as it shows something, so the bound is needed for those
steps only. The bound grows with the size. -/
theorem neverWorse_of_trace {A B : CostedRuntime} {p : Nat → Nat → Nat}
    (hp : ∀ a n n', n ≤ n' → p a n ≤ p a n')
    (h : ∀ P q, P.WellFormed q →
      (∀ m, TraceEquiv P.sorts.interp (B.runtime.trace (B.start P q) m) (A.runtime.trace (A.start P q) m)) ∧
      ∀ n m, m ≤ n → m ≤ (A.runtime.trace (A.start P q) n).length →
        B.paid P q m ≤ p (A.paid P q n) (P.size + q.size)) :
    NeverWorse A B p := by
  refine NeverWorse.of_steps hp fun P q hwf n => ?_
  obtain ⟨ht, hc⟩ := h P q hwf
  obtain ⟨L, hL⟩ : ∃ L, (A.runtime.trace (A.start P q) n).length = L := ⟨_, rfl⟩
  have hLn : L ≤ n := hL ▸ A.runtime.trace_length_le n (A.start P q)
  have htr : A.runtime.trace (A.start P q) L = A.runtime.trace (A.start P q) n :=
    hL ▸ A.runtime.trace_trace_length n (A.start P q)
  refine ⟨L, hc n L hLn (le_of_eq hL.symm), fun c hf p hp => ?_, fun hn => ?_⟩
  · obtain ⟨a, ha, hpa⟩ := hf p hp
    rw [← A.runtime.emitted_eq_of_trace htr] at ha
    have he : StepEquiv P.sorts.interp (A.runtime.emitted (A.start P q) L)
        (B.runtime.emitted (B.start P q) L) := by
      have h1 := A.runtime.emitted_eq_flatMap_trace L (A.start P q)
      have h2 := B.runtime.emitted_eq_flatMap_trace L (B.start P q)
      exact h1 ▸ h2 ▸ (TraceEquiv.emits (ht L)).symm
    obtain ⟨b, hb, e⟩ := he.mem ha
    exact ⟨b, hb, e.2 hpa⟩
  · refine (B.runtime.halts_iff_trace (s := B.start P q)).2 (TraceEquiv.final (ht L) ?_)
    rw [htr]
    exact (A.runtime.halts_iff_trace (s := A.start P q)).1 hn

end RwLog
