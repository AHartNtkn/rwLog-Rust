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

/-! ## Runs, as far as they emit -/

namespace Runtime

variable (R : Runtime)

/-- A run that stopped early has reported that it is done one step after its
last answer. -/
theorem halts_trace_length_succ : ∀ (n : Nat) (s : R.State), (R.trace s n).length < n →
    R.Halts s ((R.trace s n).length + 1)
  | 0, _, h => by simp [trace] at h
  | n + 1, s, h => by
    cases hs : R.step s with
    | done =>
      rw [R.trace_succ_done hs]
      show (R.run s 1).2 = true
      rw [R.run_succ_done hs]
    | emit as s' =>
      rw [R.trace_succ_emit hs] at h ⊢
      have ih := halts_trace_length_succ n s' (by simpa using h)
      show (R.run s ((R.trace s' n).length + 1 + 1)).2 = true
      rw [R.run_succ_emit hs]
      exact ih

end Runtime

namespace CostedRuntime

variable (C : CostedRuntime)

/-- A machine whose emitting steps each cost a tick has spent at least one
tick per step it has emitted. -/
theorem trace_length_le_spent
    (hpos : ∀ s as s', (C.step s).val = .emit as s' → 1 ≤ (C.step s).ticks) :
    ∀ (n : Nat) (s : C.State), (C.runtime.trace s n).length ≤ C.spent s n
  | 0, _ => Nat.le_refl 0
  | n + 1, s => by
    cases hs : (C.step s).val with
    | done =>
      rw [C.runtime.trace_succ_done (show C.runtime.step s = .done from hs)]
      exact Nat.zero_le _
    | emit as s' =>
      rw [C.runtime.trace_succ_emit (show C.runtime.step s = .emit as s' from hs),
        C.spent_succ_emit hs]
      have := trace_length_le_spent hpos n s'
      have := hpos s as s' hs
      simp only [List.length_cons]
      omega

/-! ## The machine on the mirror image and on the converse -/

theorem mirror_spent : ∀ (n : Nat) (s : C.State), C.mirror.spent s n = C.spent s n
  | 0, _ => rfl
  | n + 1, s => by
    cases hs : (C.step s).val with
    | done =>
      have hs' : (C.mirror.step s).val = .done := by
        show (C.step s).val.swap = _; rw [hs]; rfl
      rw [C.mirror.spent_succ_done hs', C.spent_succ_done hs]; rfl
    | emit as s' =>
      have hs' : (C.mirror.step s).val = .emit (as.map Span.swap) s' := by
        show (C.step s).val.swap = _; rw [hs]; rfl
      rw [C.mirror.spent_succ_emit hs', C.spent_succ_emit hs]
      exact congrArg ((C.step s).ticks + ·) (mirror_spent n s')

theorem mirror_trace : ∀ (n : Nat) (s : C.State),
    C.mirror.runtime.trace s n = (C.runtime.trace s n).map (·.map Span.swap)
  | 0, _ => rfl
  | n + 1, s => by
    cases hs : (C.step s).val with
    | done =>
      have hs' : C.mirror.runtime.step s = .done := by
        show (C.step s).val.swap = _; rw [hs]; rfl
      rw [C.mirror.runtime.trace_succ_done hs',
        C.runtime.trace_succ_done (show C.runtime.step s = .done from hs)]; rfl
    | emit as s' =>
      have hs' : C.mirror.runtime.step s = .emit (as.map Span.swap) s' := by
        show (C.step s).val.swap = _; rw [hs]; rfl
      rw [C.mirror.runtime.trace_succ_emit hs',
        C.runtime.trace_succ_emit (show C.runtime.step s = .emit as s' from hs), List.map_cons]
      exact congrArg (as.map Span.swap :: ·) (mirror_trace n s')

theorem mirror_paid (P : Program) (q : Rel) (n : Nat) :
    C.mirror.paid P q n = C.paid P.dual q.dual n := by
  exact congrArg ((C.init P.dual q.dual).ticks + ·) (C.mirror_spent n _)

theorem conv_spent : ∀ (n : Nat) (s : C.State), C.conv.spent s n = C.spent s n
  | 0, _ => rfl
  | n + 1, s => by
    cases hs : (C.step s).val with
    | done =>
      have hs' : (C.conv.step s).val = .done := by
        show (C.step s).val.swap = _; rw [hs]; rfl
      rw [C.conv.spent_succ_done hs', C.spent_succ_done hs]; rfl
    | emit as s' =>
      have hs' : (C.conv.step s).val = .emit (as.map Span.swap) s' := by
        show (C.step s).val.swap = _; rw [hs]; rfl
      rw [C.conv.spent_succ_emit hs', C.spent_succ_emit hs]
      exact congrArg ((C.step s).ticks + ·) (conv_spent n s')

theorem conv_trace : ∀ (n : Nat) (s : C.State),
    C.conv.runtime.trace s n = (C.runtime.trace s n).map (·.map Span.swap)
  | 0, _ => rfl
  | n + 1, s => by
    cases hs : (C.step s).val with
    | done =>
      have hs' : C.conv.runtime.step s = .done := by
        show (C.step s).val.swap = _; rw [hs]; rfl
      rw [C.conv.runtime.trace_succ_done hs',
        C.runtime.trace_succ_done (show C.runtime.step s = .done from hs)]; rfl
    | emit as s' =>
      have hs' : C.conv.runtime.step s = .emit (as.map Span.swap) s' := by
        show (C.step s).val.swap = _; rw [hs]; rfl
      rw [C.conv.runtime.trace_succ_emit hs',
        C.runtime.trace_succ_emit (show C.runtime.step s = .emit as s' from hs), List.map_cons]
      exact congrArg (as.map Span.swap :: ·) (conv_trace n s')

theorem conv_paid (P : Program) (q : Rel) (n : Nat) :
    C.conv.paid P q n = C.paid P (.conv q) n := by
  exact congrArg ((C.init P (.conv q)).ticks + ·) (C.conv_spent n _)

end CostedRuntime

/-! ## Simulation from equal traces -/

/-- `B` simulates `A` within `p` when, on every input, the trace of `B` agrees
with the trace of `A` step for step, and `B` has paid at most `p` of what `A`
has paid by any step up to one past the last at which `A` emitted. -/
theorem simulates_of_trace {A B : CostedRuntime} {p : Nat → Nat → Nat}
    (h : ∀ P q, P.WellFormed q →
      (∀ m, TraceEquiv (B.runtime.trace (B.start P q) m) (A.runtime.trace (A.start P q) m)) ∧
      ∀ n m, m ≤ n → m ≤ (A.runtime.trace (A.start P q) n).length + 1 →
        B.paid P q m ≤ p (A.paid P q n) (P.size + q.size)) :
    Simulates A B p := by
  refine Simulates.of_steps fun P q hwf n => ?_
  obtain ⟨ht, hc⟩ := h P q hwf
  obtain ⟨L, hL⟩ : ∃ L, (A.runtime.trace (A.start P q) n).length = L := ⟨_, rfl⟩
  have hlen : ∀ (n : Nat) (s : A.runtime.State), (A.runtime.trace s n).length ≤ n := by
    intro n
    induction n with
    | zero => intro s; exact Nat.le_refl 0
    | succ n ih =>
      intro s
      cases hs : A.runtime.step s with
      | done => rw [A.runtime.trace_succ_done hs]; exact Nat.zero_le _
      | emit as s' =>
        rw [A.runtime.trace_succ_emit hs]
        exact Nat.succ_le_succ (ih s')
  have hLn : L ≤ n := hL ▸ hlen n (A.start P q)
  have hhalt : L < n → A.runtime.Halts (A.start P q) (L + 1) := fun hlt =>
    hL ▸ A.runtime.halts_trace_length_succ n (A.start P q) (hL ▸ hlt)
  have hB : ∀ m, A.runtime.Halts (A.start P q) m → B.runtime.Halts (B.start P q) m := by
    intro m hm
    refine (B.runtime.halts_iff_trace_length m (B.start P q)).2 ?_
    have h1 := (A.runtime.halts_iff_trace_length m (A.start P q)).1 hm
    have h2 := (ht m).length_eq
    omega
  have hem : ∀ m, ∀ a ∈ A.runtime.emitted (A.start P q) m,
      ∃ b ∈ B.runtime.emitted (B.start P q) m, b.CoversLive P.theory a := by
    intro m a ha
    have he : StepEquiv (A.runtime.emitted (A.start P q) m) (B.runtime.emitted (B.start P q) m) := by
      have h1 := A.runtime.emitted_eq_flatten_trace m (A.start P q)
      have h2 := B.runtime.emitted_eq_flatten_trace m (B.start P q)
      exact h1 ▸ h2 ▸ (TraceEquiv.flatten (ht m)).symm
    obtain ⟨b, hb, e⟩ := he.mem ha
    exact ⟨b, hb, e.2.live⟩
  by_cases hlt : L < n
  · refine ⟨L + 1, hc n (L + 1) (by omega) (le_of_eq (congrArg (· + 1) hL.symm)),
      fun a ha => ?_, fun _ => hB _ (hhalt hlt)⟩
    exact hem (L + 1) a (A.runtime.emitted_of_halts (hhalt hlt) n ha)
  · exact ⟨n, hc n n (Nat.le_refl _) (by omega), hem n, hB n⟩

/-! ## Runs that cost the same, step for step -/

/-- From states related by `rel`, `A` and `B` take steps that cost the same,
emit answers related by `E`, and end in related states. -/
structure CostBisim (A B : CostedRuntime) (E : List Span → List Span → Prop)
    (rel : A.State → B.State → Prop) : Prop where
  ticks : ∀ s t, rel s t → (A.step s).ticks = (B.step t).ticks
  step : ∀ s t, rel s t → Step.Rel E rel (A.step s).val (B.step t).val

namespace CostBisim

variable {A B : CostedRuntime} {E : List Span → List Span → Prop}
  {rel : A.State → B.State → Prop}

theorem spent (h : CostBisim A B E rel) : ∀ (n : Nat) (s : A.State) (t : B.State), rel s t →
    A.spent s n = B.spent t n
  | 0, _, _, _ => rfl
  | n + 1, s, t, hr => by
    have hs := h.step s t hr
    have ht := h.ticks s t hr
    cases h1 : (A.step s).val with
    | done =>
      cases h2 : (B.step t).val with
      | done => rw [A.spent_succ_done h1, B.spent_succ_done h2, ht]
      | emit as' t' => rw [h1, h2] at hs; exact hs.elim
    | emit as s' =>
      cases h2 : (B.step t).val with
      | done => rw [h1, h2] at hs; exact hs.elim
      | emit as' t' =>
        rw [h1, h2] at hs
        rw [A.spent_succ_emit h1, B.spent_succ_emit h2, ht, spent h n s' t' hs.2]

theorem trace (h : CostBisim A B E rel) (n : Nat) (s : A.State) (t : B.State) (hr : rel s t) :
    List.Forall₂ E (A.runtime.trace s n) (B.runtime.trace t n) :=
  Runtime.trace_of_sim (R := A.runtime) (R' := B.runtime) h.step n s t hr

theorem mono {E' : List Span → List Span → Prop} (h : CostBisim A B E rel)
    (hE : ∀ as bs, E as bs → E' as bs) : CostBisim A B E' rel where
  ticks := h.ticks
  step s t hr := by
    have hs := h.step s t hr
    cases h1 : (A.step s).val <;> cases h2 : (B.step t).val <;> rw [h1, h2] at hs
    · exact ⟨hE _ _ hs.1, hs.2⟩
    · exact hs
    · exact hs
    · exact hs

/-- The same relation read from the other side. -/
theorem flip (h : CostBisim A B E rel) :
    CostBisim B A (fun bs as => E as bs) (fun t s => rel s t) where
  ticks t s hr := (h.ticks s t hr).symm
  step t s hr := by
    have hs := h.step s t hr
    cases h1 : (A.step s).val <;> cases h2 : (B.step t).val <;> rw [h1, h2] at hs
    · exact hs
    · exact hs
    · exact hs
    · exact hs

/-- With the second machine's answers swapped back. -/
theorem toMirror (h : CostBisim A B (fun as bs => E as (bs.map Span.swap)) rel) :
    CostBisim A B.mirror E rel where
  ticks := h.ticks
  step s t hr := by
    have hs := h.step s t hr
    show Step.Rel E rel (A.step s).val (B.step t).val.swap
    cases h1 : (A.step s).val <;> cases h2 : (B.step t).val <;> rw [h1, h2] at hs
    · exact hs
    · exact hs
    · exact hs
    · exact hs

/-- With the first machine's answers swapped back. -/
theorem ofMirror (h : CostBisim A B (fun as bs => E (as.map Span.swap) bs) rel) :
    CostBisim A.mirror B E rel where
  ticks := h.ticks
  step s t hr := by
    have hs := h.step s t hr
    show Step.Rel E rel (A.step s).val.swap (B.step t).val
    cases h1 : (A.step s).val <;> cases h2 : (B.step t).val <;> rw [h1, h2] at hs
    · exact hs
    · exact hs
    · exact hs
    · exact hs

theorem toConv (h : CostBisim A B (fun as bs => E as (bs.map Span.swap)) rel) :
    CostBisim A B.conv E rel := ⟨h.toMirror.ticks, h.toMirror.step⟩

theorem ofConv (h : CostBisim A B (fun as bs => E (as.map Span.swap) bs) rel) :
    CostBisim A.conv B E rel := ⟨h.ofMirror.ticks, h.ofMirror.step⟩

/-- Two machines that start in related states, take steps of the same cost
and emit the same answers up to order and equivalence: the second simulates
the first within what its first state costs more. -/
theorem simulates (h : CostBisim A B StepEquiv rel) (k : Nat)
    (hstart : ∀ P q, P.WellFormed q → rel (A.start P q) (B.start P q))
    (hinit : ∀ P q, (B.init P q).ticks ≤ (A.init P q).ticks + k) :
    Simulates A B fun c _ => c + k := by
  refine simulates_of_trace fun P q hwf => ⟨fun m => ?_, fun n m hmn _ => ?_⟩
  · exact TraceEquiv.symm (h.trace m _ _ (hstart P q hwf))
  · show (B.init P q).ticks + B.spent (B.start P q) m ≤
      (A.init P q).ticks + A.spent (A.start P q) n + k
    rw [← h.spent m _ _ (hstart P q hwf)]
    have := A.spent_mono (A.start P q) hmn
    have := hinit P q
    omega

end CostBisim

/-! ## The run on the converse -/

/-- The run of `C` on `conv q` and its run on `q` go through states related
by `rel`: every step costs the same and emits the same answers swapped. -/
structure ConvBisim (C : CostedRuntime) (rel : C.State → C.State → Prop) : Prop
    extends CostBisim C C (fun xs ys => xs = ys.map Span.swap) rel where
  start : ∀ P q, rel (C.start P (.conv q)) (C.start P q)

/-- The run of `C` on the mirror image and its run on the query go through
states related by `rel`: every step costs the same and emits the same answers
swapped, up to order and equivalence. -/
structure DualBisim (C : CostedRuntime) (rel : C.State → C.State → Prop) : Prop
    extends CostBisim C C (fun xs ys => StepEquiv xs (ys.map Span.swap)) rel where
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
    have h1 : CostBisim C C (fun xs ys => StepEquiv (xs.map Span.swap) ys)
        (fun t s => D s t) :=
      hd.toCostBisim.flip.mono fun _ _ h => h.symm
    exact h1.ofMirror.simulates k (fun P q hwf => hd.start P q hwf) fun P q =>
      show _ ≤ (C.init P.dual q.dual).ticks + k by rw [hdi]; omega
  toConv := by
    have h1 : CostBisim C C (fun xs ys => StepEquiv xs (ys.map Span.swap))
        (fun t s => rel s t) :=
      hc.toCostBisim.flip.mono fun as bs h => by
        subst h; rw [map_swap_swap]; exact StepEquiv.refl _
    exact h1.toConv.simulates k (fun P q _ => hc.start P q) fun P q => hci P q
  ofConv := by
    have h1 : CostBisim C C (fun xs ys => StepEquiv (xs.map Span.swap) ys) rel :=
      hc.toCostBisim.mono fun as bs h => by
        subst h; rw [map_swap_swap]; exact StepEquiv.refl _
    exact h1.ofConv.simulates k (fun P q _ => hc.start P q) fun P q =>
      show _ ≤ (C.init P (.conv q)).ticks + k by have := hci' P q; omega

end RwLog
