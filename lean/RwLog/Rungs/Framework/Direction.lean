/-
# Direction: the mirror image and the converse of a run

Facts used to establish `DirectionFree` (`Trusted/Cost.lean`).

* The mirror image: `dual` is an involution and keeps sizes and
  well-formedness; a swapped span relates the swapped pairs.
* `C.mirror` and `C.conv` spend what `C` spends and emit its answers swapped.
* `simulates_of_trace`: a machine whose trace agrees with another's, step for
  step, simulates it within any bound on what it has paid by the step the
  other has reached. A run is only followed as far as it emits, and one step
  further when it stops, so the bound is needed for those steps only.
* `CostBisim`: two machines go through related states at the same cost, step
  for step. `ConvBisim` is that for the runs of one machine on `conv q` and on
  `q`, and `DualBisim` for its runs on the mirror image and on the query.
* `DirectionFree.of_bisim`: a machine with both does not depend on
  direction, within what its first state costs more on a converse.
-/
import RwLog.Rungs.Framework.Latency
import RwLog.Rungs.Framework.Trace
import RwLog.Rungs.Framework.Cost
import RwLog.Kernel.Size

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
  | mk defs theory =>
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

theorem ProgramOf.WellFormed.dual {P : Program} {q : Rel} (h : P.WellFormed q) :
    P.dual.WellFormed q.dual := by
  obtain ⟨h1, h2, h3⟩ := h
  have hfst : P.dual.defs.map Prod.fst = P.defs.map Prod.fst := by
    simp only [ProgramOf.dual, List.map_map]
    exact List.map_congr_left fun d _ => rfl
  refine ⟨by rw [hfst]; exact h1, fun n hn => ?_, h3⟩
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
    | progress k s' =>
      rw [R.trace_succ_progress hs, List.length_cons, R.trace_succ_progress hs,
        trace_trace_length n s']

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
theorem TraceEquiv.final {A B : Type} [Answer A] [Answer B] :
    ∀ {t : List (Shown A)} {t' : List (Shown B)}, TraceEquiv t t' →
      (∃ fin, t'.getLast? = some (.final fin)) → ∃ fin, t.getLast? = some (.final fin)
  | _, _, .nil, ⟨_, h⟩ => by simp at h
  | _, _, .cons (a := x) (b := y) h .nil, ⟨fin, hf⟩ => by
    simp only [List.getLast?_singleton, Option.some.injEq] at hf
    subst hf
    cases x with
    | final xs => exact ⟨xs, rfl⟩
    | answers xs => exact h.elim
    | level n => exact h.elim
  | _, _, .cons _ (.cons h' hs), ⟨fin, hf⟩ => by
    rw [List.getLast?_cons_cons] at hf ⊢
    exact TraceEquiv.final (.cons h' hs) ⟨fin, hf⟩

/-- Swapping twice gives equivalent answers. -/
theorem StepEquiv.swap_swap {A : Type} [Answer A] (xs : List A) :
    StepEquiv ((xs.map Answer.swap).map Answer.swap) xs := by
  refine StepEquiv.of_forall₂ ?_
  rw [List.map_map, List.forall₂_map_left_iff]
  refine List.forall₂_same.2 fun a _ => ?_
  have h : ∀ M, Answer.den M (Answer.swap (Answer.swap a)) = Answer.den M a := by
    intro M; rw [Answer.den_swap, Answer.den_swap]; rfl
  exact ⟨fun M => (h M).ge, fun M => (h M).le⟩

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
    | progress k s' =>
      rw [C.runtime.trace_succ_progress (show C.runtime.step s = .progress k s' from hs),
        C.spent_succ_progress hs]
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
  step s := ⟨(C.step s).val.swap, (C.step s).ticks⟩

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
    | progress k s' =>
      have hs' : ((C.swapped init).step s).val = .progress k s' := by
        show (C.step s).val.swap = _; rw [hs]; rfl
      rw [(C.swapped init).spent_succ_progress hs', C.spent_succ_progress hs]
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
    | progress k s' =>
      have hs' : (C.swapped init).runtime.step s = .progress k s' := by
        show (C.step s).val.swap = _; rw [hs]; rfl
      rw [(C.swapped init).runtime.trace_succ_progress hs',
        C.runtime.trace_succ_progress (show C.runtime.step s = .progress k s' from hs),
        List.map_cons]
      exact congrArg (Shown.level k :: ·) (swapped_trace init n s')

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

/-! ## Simulation from equal traces -/

/-- `B` simulates `A` within `p` when, on every input, the trace of `B` agrees
with the trace of `A` step for step, and `B` has paid at most `p` of what `A`
has paid by any step up to the last that `A` has shown. -/
theorem simulates_of_trace {A B : CostedRuntime} {p : Nat → Nat → Nat}
    (h : ∀ P q, P.WellFormed q →
      (∀ m, TraceEquiv (B.runtime.trace (B.start P q) m) (A.runtime.trace (A.start P q) m)) ∧
      ∀ n m, m ≤ n → m ≤ (A.runtime.trace (A.start P q) n).length →
        B.paid P q m ≤ p (A.paid P q n) (P.size + q.size)) :
    Simulates A B p := by
  refine Simulates.of_steps fun P q hwf n => ?_
  obtain ⟨ht, hc⟩ := h P q hwf
  obtain ⟨L, hL⟩ : ∃ L, (A.runtime.trace (A.start P q) n).length = L := ⟨_, rfl⟩
  have hLn : L ≤ n := hL ▸ A.runtime.trace_length_le n (A.start P q)
  have htr : A.runtime.trace (A.start P q) L = A.runtime.trace (A.start P q) n :=
    hL ▸ A.runtime.trace_trace_length n (A.start P q)
  refine ⟨L, hc n L hLn (le_of_eq hL.symm), fun a ha => ?_, fun hn => ?_⟩
  · rw [← A.runtime.emitted_eq_of_trace htr] at ha
    have he : StepEquiv (A.runtime.emitted (A.start P q) L) (B.runtime.emitted (B.start P q) L) := by
      have h1 := A.runtime.emitted_eq_flatMap_trace L (A.start P q)
      have h2 := B.runtime.emitted_eq_flatMap_trace L (B.start P q)
      exact h1 ▸ h2 ▸ (TraceEquiv.emits (ht L)).symm
    obtain ⟨b, hb, e⟩ := he.mem ha
    exact ⟨b, hb, e.2.live⟩
  · refine (B.runtime.halts_iff_trace (s := B.start P q)).2 (TraceEquiv.final (ht L) ?_)
    rw [htr]
    exact (A.runtime.halts_iff_trace (s := A.start P q)).1 hn

/-! ## Runs that cost the same, step for step -/

/-- From states related by `rel`, `A` and `B` take steps that cost the same,
show answers related by `E`, and end in related states. -/
structure CostBisim (A B : CostedRuntime) (E : List A.Ans → List B.Ans → Prop)
    (rel : A.State → B.State → Prop) : Prop where
  ticks : ∀ s t, rel s t → (A.step s).ticks = (B.step t).ticks
  step : ∀ s t, rel s t → StepOf.Rel E rel (A.step s).val (B.step t).val

namespace CostBisim

variable {A B : CostedRuntime} {E : List A.Ans → List B.Ans → Prop}
  {rel : A.State → B.State → Prop}

theorem spent (h : CostBisim A B E rel) : ∀ (n : Nat) (s : A.State) (t : B.State), rel s t →
    A.spent s n = B.spent t n
  | 0, _, _, _ => rfl
  | n + 1, s, t, hr => by
    have hs := h.step s t hr
    have ht := h.ticks s t hr
    cases h1 : (A.step s).val <;> cases h2 : (B.step t).val <;> rw [h1, h2] at hs <;>
      first
      | exact hs.elim
      | rw [A.spent_succ_emit h1, B.spent_succ_emit h2, ht, spent h n _ _ hs.2]
      | rw [A.spent_succ_progress h1, B.spent_succ_progress h2, ht, spent h n _ _ hs.2]
      | rw [A.spent_succ_done h1, B.spent_succ_done h2, ht]

theorem trace (h : CostBisim A B E rel) (n : Nat) (s : A.State) (t : B.State) (hr : rel s t) :
    List.Forall₂ (Shown.Rel E) (A.runtime.trace s n) (B.runtime.trace t n) :=
  Runtime.trace_of_sim (R := A.runtime) (R' := B.runtime) h.step n s t hr

theorem mono {E' : List A.Ans → List B.Ans → Prop} (h : CostBisim A B E rel)
    (hE : ∀ as bs, E as bs → E' as bs) : CostBisim A B E' rel where
  ticks := h.ticks
  step s t hr := by
    have hs := h.step s t hr
    cases h1 : (A.step s).val <;> cases h2 : (B.step t).val <;> rw [h1, h2] at hs <;>
      first
      | exact hs.elim
      | exact ⟨hE _ _ hs.1, hs.2⟩
      | exact hs
      | exact hE _ _ hs

/-- The same relation read from the other side. -/
theorem flip (h : CostBisim A B E rel) :
    CostBisim B A (fun bs as => E as bs) (fun t s => rel s t) where
  ticks t s hr := (h.ticks s t hr).symm
  step t s hr := by
    have hs := h.step s t hr
    cases h1 : (A.step s).val <;> cases h2 : (B.step t).val <;> rw [h1, h2] at hs <;>
      first
      | exact hs.elim
      | exact ⟨hs.1.symm, hs.2⟩
      | exact hs

/-- With the second machine's answers swapped back. -/
theorem toMirror (h : CostBisim A B (fun as bs => E as (bs.map Answer.swap)) rel) :
    CostBisim A B.mirror E rel where
  ticks := h.ticks
  step s t hr := by
    have hs := h.step s t hr
    show StepOf.Rel E rel (A.step s).val (B.step t).val.swap
    cases h1 : (A.step s).val <;> cases h2 : (B.step t).val <;> rw [h1, h2] at hs <;> exact hs

/-- With the first machine's answers swapped back. -/
theorem ofMirror (h : CostBisim A B (fun as bs => E (as.map Answer.swap) bs) rel) :
    CostBisim A.mirror B E rel where
  ticks := h.ticks
  step s t hr := by
    have hs := h.step s t hr
    show StepOf.Rel E rel (A.step s).val.swap (B.step t).val
    cases h1 : (A.step s).val <;> cases h2 : (B.step t).val <;> rw [h1, h2] at hs <;> exact hs

theorem toConv (h : CostBisim A B (fun as bs => E as (bs.map Answer.swap)) rel) :
    CostBisim A B.conv E rel := ⟨h.toMirror.ticks, h.toMirror.step⟩

theorem ofConv (h : CostBisim A B (fun as bs => E (as.map Answer.swap) bs) rel) :
    CostBisim A.conv B E rel := ⟨h.ofMirror.ticks, h.ofMirror.step⟩

/-- Two machines that start in related states, take steps of the same cost
and show the same answers up to order and equivalence: the second simulates
the first within what its first state costs more. -/
theorem simulates (h : CostBisim A B StepEquiv rel) (k : Nat)
    (hstart : ∀ P q, P.WellFormed q → rel (A.start P q) (B.start P q))
    (hinit : ∀ P q, (B.init P q).ticks ≤ (A.init P q).ticks + k) :
    Simulates A B fun c _ => c + k := by
  refine simulates_of_trace fun P q hwf => ⟨fun m => ?_, fun n m hmn _ => ?_⟩
  · exact TraceEquiv.symm
      ((h.trace m _ _ (hstart P q hwf)).imp fun _ _ h => shownEquiv_iff.2 h)
  · show (B.init P q).ticks + B.spent (B.start P q) m ≤
      (A.init P q).ticks + A.spent (A.start P q) n + k
    rw [← h.spent m _ _ (hstart P q hwf)]
    have := A.spent_mono (A.start P q) hmn
    have := hinit P q
    omega

end CostBisim

/-! ## The run on the converse -/

/-- The run of `C` on `conv q` and its run on `q` go through states related
by `rel`: every step costs the same and shows the same answers swapped. -/
structure ConvBisim (C : CostedRuntime) (rel : C.State → C.State → Prop) : Prop
    extends CostBisim C C (fun xs ys => xs = ys.map Answer.swap) rel where
  start : ∀ P q, rel (C.start P (.conv q)) (C.start P q)

/-- The run of `C` on the mirror image and its run on the query go through
states related by `rel`: every step costs the same and shows the same answers
swapped, up to order and equivalence. -/
structure DualBisim (C : CostedRuntime) (rel : C.State → C.State → Prop) : Prop
    extends CostBisim C C (fun xs ys => StepEquiv xs (ys.map Answer.swap)) rel where
  start : ∀ P q, P.WellFormed q → rel (C.start P q) (C.start P.dual q.dual)

/-- A machine whose runs on the mirror image and on the converse cost what
its run on the query costs, step for step, does not depend on direction: the
only difference is what the first state costs, which for the mirror image is
the same and for the converse at most `k` more. -/
theorem DirectionFree.of_bisim {C : CostedRuntime} {D rel : C.State → C.State → Prop} {k : Nat}
    (hd : DualBisim C D) (hc : ConvBisim C rel)
    (hdi : ∀ P q, (C.init P.dual q.dual).ticks = (C.init P q).ticks)
    (hci : ∀ P q, (C.init P (.conv q)).ticks ≤ (C.init P q).ticks + k)
    (hci' : ∀ P q, (C.init P q).ticks ≤ (C.init P (.conv q)).ticks) :
    DirectionFree C fun c _ => c + k where
  toMirror :=
    hd.toCostBisim.toMirror.simulates k hd.start fun P q =>
      show (C.init P.dual q.dual).ticks ≤ _ by rw [hdi]; omega
  ofMirror := by
    have h1 : CostBisim C C (fun xs ys => StepEquiv (xs.map Answer.swap) ys)
        (fun t s => D s t) :=
      hd.toCostBisim.flip.mono fun _ _ h => h.symm
    exact h1.ofMirror.simulates k (fun P q hwf => hd.start P q hwf) fun P q =>
      show _ ≤ (C.init P.dual q.dual).ticks + k by rw [hdi]; omega
  toConv := by
    have h1 : CostBisim C C (fun xs ys => StepEquiv xs (ys.map Answer.swap))
        (fun t s => rel s t) :=
      hc.toCostBisim.flip.mono fun as bs h => by
        subst h; exact (StepEquiv.swap_swap as).symm
    exact h1.toConv.simulates k (fun P q _ => hc.start P q) fun P q => hci P q
  ofConv := by
    have h1 : CostBisim C C (fun xs ys => StepEquiv (xs.map Answer.swap) ys) rel :=
      hc.toCostBisim.mono fun as bs h => by
        subst h; exact StepEquiv.swap_swap bs
    exact h1.ofConv.simulates k (fun P q _ => hc.start P q) fun P q =>
      show _ ≤ (C.init P (.conv q)).ticks + k by have := hci' P q; omega

end RwLog
