/-
# Finishing a level: proving the improvement statements

`Trusted/Cost.lean` states improvement by the cost of finishing a level: what
a machine has used when it has reported a level `c` or higher, or that it is
done. The ways a rung establishes those statements are here, for any costed
runtime.

* A level once finished stays finished, and finishing a level finishes every
  lower one (`Runtime.Finished.mono`, `Runtime.Finished.anti`). A run that
  is done has finished every level (`Runtime.Finished.of_halts`).
* A run has finished a level exactly when it is done or its trace shows a
  report of that level or a higher one (`Runtime.finished_iff_trace`).
* A machine that reports no level (`Runtime.Silent`) reports levels truly,
  and finishes a level only by reporting that it is done.
* `NeverWorse.of_steps`: step by step, the new machine has finished every
  level the old one has, at a bounded cost, and has halted if the old one
  has.
* A machine that is never worse than one that finishes every level finishes
  every level (`NeverWorse.finishesEveryLevel`), and it halts where the
  other halts (`NeverWorse.terminates`).
* Every rung of a ladder has the laws and reports levels truly
  (`Ladder.lawful`, `Ladder.honest`).
-/
import RwLog.Rungs.Framework.Cost
import RwLog.Trusted.Properties
import RwLog.Rungs.Framework.Runtime
import RwLog.SpanLayer.Coverage

namespace RwLog

namespace Runtime

variable (R : Runtime)

/-- A run that is done has finished every level. -/
theorem Finished.of_halts {s : R.State} {n : Nat} (h : R.Halts s n) (c : Nat) :
    R.Finished s c n := Or.inl h

/-- A level once finished stays finished. -/
theorem Finished.mono {s : R.State} {c m n : Nat} (h : R.Finished s c m) (hmn : m ≤ n) :
    R.Finished s c n := by
  rcases h with h | ⟨k, j, hk, hc, hj⟩
  · exact Or.inl (Runtime.Halts.mono R h hmn)
  · exact Or.inr ⟨k, j, lt_of_lt_of_le hk hmn, hc, hj⟩

/-- A run that has finished a level has finished every lower one. -/
theorem Finished.anti {s : R.State} {c c' n : Nat} (h : R.Finished s c n) (hc : c' ≤ c) :
    R.Finished s c' n := by
  rcases h with h | ⟨k, j, hk, hcert, hj⟩
  · exact Or.inl h
  · exact Or.inr ⟨k, j, hk, hcert, hc.trans hj⟩

/-- The first `k + 1` steps of a longer run show what the run shows. -/
theorem trace_getElem?_of_lt : ∀ (k n : Nat) (s : R.State), k < n →
    (R.trace s n)[k]? = (R.trace s (k + 1))[k]?
  | k, 0, _, h => absurd h (Nat.not_lt_zero _)
  | 0, n + 1, s, _ => by
    cases hs : R.step s with
    | done fin => rw [R.trace_succ_done hs, R.trace_succ_done hs]
    | emit as s' => rw [R.trace_succ_emit hs, R.trace_succ_emit hs]; rfl
    | progress j s' => rw [R.trace_succ_progress hs, R.trace_succ_progress hs]; rfl
  | k + 1, n + 1, s, h => by
    cases hs : R.step s with
    | done fin => rw [R.trace_succ_done hs, R.trace_succ_done hs]
    | emit as s' =>
      rw [R.trace_succ_emit hs, R.trace_succ_emit hs, List.getElem?_cons_succ,
        List.getElem?_cons_succ]
      exact trace_getElem?_of_lt k n s' (Nat.lt_of_succ_lt_succ h)
    | progress j s' =>
      rw [R.trace_succ_progress hs, R.trace_succ_progress hs, List.getElem?_cons_succ,
        List.getElem?_cons_succ]
      exact trace_getElem?_of_lt k n s' (Nat.lt_of_succ_lt_succ h)

/-- A run has finished a level exactly when it is done or its trace shows a
report of that level or a higher one. -/
theorem finished_iff_trace {s : R.State} {c n : Nat} :
    R.Finished s c n ↔ R.Halts s n ∨ ∃ m, c ≤ m ∧ Shown.level m ∈ R.trace s n := by
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨k, m, hk, hcert, hm⟩
    refine ⟨m, hm, ?_⟩
    have h : (R.trace s n)[k]? = some (.level m) := by
      rw [R.trace_getElem?_of_lt k n s hk]; exact hcert
    exact List.mem_of_getElem? h
  · rintro ⟨m, hm, hmem⟩
    obtain ⟨k, hk, hget⟩ := List.getElem_of_mem hmem
    have hkn : k < n := lt_of_lt_of_le hk (R.trace_length_le n s)
    refine ⟨k, m, hkn, ?_, hm⟩
    show (R.trace s (k + 1))[k]? = some (.level m)
    rw [← R.trace_getElem?_of_lt k n s hkn, List.getElem?_eq_getElem hk, hget]

/-- The runtime reports no level: on a well-formed input no step of a run
shows one. Such a machine finishes a level only by reporting that it is
done. -/
def Silent : Prop :=
  ∀ P q, P.WellFormed q → ∀ n, ∀ x ∈ R.trace (R.init P q) n, ∀ k, x ≠ .level k

variable {R}

/-- A runtime that reports no level reports levels truly. -/
theorem Silent.honestReports (h : R.Silent) : R.HonestReports := fun P q wf k n hc =>
  absurd rfl (h P q wf (k + 1) _ (List.mem_of_getElem? hc) n)

/-- A runtime that reports no level has finished a level only when it is
done. -/
theorem Silent.halts_of_finished (h : R.Silent) {P : Program} {q : Rel} (wf : P.WellFormed q)
    {c n : Nat} (hf : R.Finished (R.init P q) c n) : R.Halts (R.init P q) n := by
  rcases R.finished_iff_trace.1 hf with hh | ⟨m, -, hm⟩
  · exact hh
  · exact absurd rfl (h P q wf n _ hm m)

end Runtime

namespace CostedRuntime

variable (C : CostedRuntime)

theorem Finished.mono {P : Program} {q : Rel} {c m n : Nat} (h : C.Finished P q c m)
    (hmn : m ≤ n) : C.Finished P q c n := Runtime.Finished.mono _ h hmn

theorem FinishesUsing.mono {μ : Meter} {P : Program} {q : Rel} {c b b' : Nat}
    (h : C.FinishesUsing μ P q c b) (hb : b ≤ b') : C.FinishesUsing μ P q c b' := by
  obtain ⟨n, hn, hs⟩ := h
  exact ⟨n, hn, le_trans hs hb⟩

theorem ExhaustsWithin.mono {P : Program} {q : Rel} {b b' : Nat}
    (h : C.ExhaustsWithin P q b) (hb : b ≤ b') : C.ExhaustsWithin P q b' := by
  obtain ⟨n, hn, hs⟩ := h
  exact ⟨n, hn, le_trans hs hb⟩

/-- A machine that reports that it is done within a bound finishes every
level within it. -/
theorem ExhaustsWithin.finishes {P : Program} {q : Rel} {b : Nat}
    (h : C.ExhaustsWithin P q b) (c : Nat) : C.FinishesUsing Meter.time P q c b := by
  obtain ⟨n, hn, hs⟩ := h
  exact ⟨n, Or.inl hn, hs⟩

end CostedRuntime

/-- `New` is never worse than `Old` when, for every number of steps of `Old`,
some number of steps of `New` costs at most `p` of what `Old` paid, has
finished every level `Old` has finished, and has halted if `Old` has. The
bound grows with the size. -/
theorem NeverWorse.of_steps {Old New : CostedRuntime} {p : Nat → Nat → Nat}
    (hp : ∀ a n n', n ≤ n' → p a n ≤ p a n')
    (h : ∀ P q, P.WellFormed q → ∀ n, ∃ m,
      New.paid P q m ≤ p (Old.paid P q n) (P.size + q.size) ∧
      (∀ c, Old.Finished P q c n → New.Finished P q c m) ∧
      (Old.runtime.Halts (Old.start P q) n → New.runtime.Halts (New.start P q) m)) :
    NeverWorse Old New p := by
  intro P q hwf n
  obtain ⟨m, hs, hfin, hh⟩ := h P q hwf n
  exact ⟨fun c hc => ⟨m, hfin c hc, le_trans hs (hp _ _ _ (Nat.le_add_right _ _))⟩,
    fun hn => ⟨m, hh hn, hs⟩⟩

/-- Never worse within `p` is never worse within any larger bound. -/
theorem NeverWorse.mono {Old New : CostedRuntime} {p p' : Nat → Nat → Nat}
    (h : NeverWorse Old New p) (hp : ∀ c n, p c n ≤ p' c n) : NeverWorse Old New p' := by
  intro P q hwf n
  obtain ⟨h1, h2⟩ := h P q hwf n
  exact ⟨fun c hc => CostedRuntime.FinishesUsing.mono _ (h1 c hc) (hp _ _),
    fun hn => CostedRuntime.ExhaustsWithin.mono _ (h2 hn) (hp _ _)⟩

/-- A machine that is never worse than one that finishes every level
finishes every level. -/
theorem NeverWorse.finishesEveryLevel {Old New : CostedRuntime} {p : Nat → Nat → Nat}
    (h : NeverWorse Old New p) (ho : Old.runtime.FinishesEveryLevel) :
    New.runtime.FinishesEveryLevel := by
  intro P q hwf c
  obtain ⟨n, hn⟩ := ho P q hwf c
  obtain ⟨m, hm, -⟩ := (h P q hwf n).1 c hn
  exact ⟨m, hm⟩

/-- A machine that is never worse than one that halts on an input halts on
it. -/
theorem NeverWorse.terminates {Old New : CostedRuntime} {p : Nat → Nat → Nat}
    (h : NeverWorse Old New p) {P : Program} {q : Rel} (hwf : P.WellFormed q)
    (ho : Old.runtime.Terminates P q) : New.runtime.Terminates P q := by
  obtain ⟨n, hn⟩ := ho
  obtain ⟨m, hm, -⟩ := (h P q hwf n).2 hn
  exact ⟨m, hm⟩

/-- A rung without preprocessing is its engine at the kernel rung. -/
theorem CostedRung.machine_nil (κ : KernelRung) (E : Engine) (A : ArtifactStore) :
    (CostedRung.mk [] E false).machine κ A = E.costed κ := rfl

/-- The rung as one runtime on the original input is the rung's machine with
the ticks forgotten. -/
theorem CostedRung.runtime_machine (G : CostedRung) (κ : KernelRung) (A : ArtifactStore) :
    (G.machine κ A).runtime = (G.rung κ).runtime κ A := rfl

/-- Two rungs without preprocessing: the improvement of the machines, and
preprocessing costs nothing. -/
theorem Advances.of_nil {κ : KernelRung} {kind : Kind} {Old New : Engine} {b : Bounds}
    {C : ProgClass} (h : Improves kind (Old.costed κ) (New.costed κ) b C) :
    Advances κ kind ⟨[], Old, false⟩ ⟨[], New, false⟩ b (fun _ => 0) C where
  improves _ := h
  preCost _ _ _ _ := Nat.le_refl 0

/-- An admitted rung halts on every input on which the rung below halts. -/
theorem Admits.halts {κ : KernelRung} {kind : Kind} {Old New : CostedRung} {b : Bounds}
    {d : PolyBound} {pre : Nat → Nat} {C : ProgClass} 
    (h : Admits κ kind Old New b d pre C) (A : ArtifactStore) {P : Program}
    {q : Rel} (hwf : P.WellFormed q) (ho : (Old.machine κ A).runtime.Terminates P q) :
    (New.machine κ A).runtime.Terminates P q :=
  (h.neverWorse A).terminates hwf ho

/-- Every rung of a ladder has the laws. -/
theorem Ladder.lawful {κ : KernelRung} {base G : CostedRung}
    (h : Ladder κ base G) : G.Lawful κ := by
  cases h with
  | base hb _ => exact hb
  | admit _ _ hl _ => exact hl

/-- Every rung of a ladder reports levels truly. -/
theorem Ladder.honest {κ : KernelRung} {base G : CostedRung}
    (h : Ladder κ base G) : G.Honest κ := by
  cases h with
  | base _ hb => exact hb
  | admit _ _ _ hh => exact hh

/-- Two rungs without preprocessing: admission is the improvement of the
machines, that the new one is never worse than the old one, and the
direction bound of the new one. -/
theorem Admits.of_nil {κ : KernelRung} {kind : Kind} {Old New : Engine} {b : Bounds}
    {d : PolyBound} {C : ProgClass} 
    (h : Improves kind (Old.costed κ) (New.costed κ) b C)
    (hn : NeverWorse (Old.costed κ) (New.costed κ) (b.worse kind.gap))
    (hd : DirectionFree (New.costed κ) d.fn) :
    Admits κ kind ⟨[], Old, false⟩ ⟨[], New, false⟩ b d (fun _ => 0) C where
  toAdvances := Advances.of_nil h
  neverWorse _ := hn
  direction _ := hd

end RwLog
