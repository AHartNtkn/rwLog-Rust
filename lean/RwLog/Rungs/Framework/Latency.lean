/-
# Latency: proving the improvement statements

`Trusted/Cost.lean` states improvement by coverage latency: the ticks a
machine has spent when an emitted answer first relates a ground pair. The
ways a rung establishes those statements are here, for any costed runtime.

* `Simulates.of_steps`: step by step, the new machine has emitted an answer
  that covers each answer of the old one, at a bounded cost, and has halted if
  the old one has. Covering answers covers their pairs.
* `CostedRuntime.coversWithin_of_halts`: a machine that reports exhaustion
  honestly has covered every pair of the query by the time it halts, so on an
  input that halts the cost of halting bounds every coverage latency.
* `CostedRuntime.le_spent_of_covered`: a machine that has emitted nothing in
  its first `N` steps has paid for `N + 1` steps before it covers anything.
-/
import RwLog.Rungs.Framework.Cost
import RwLog.Rungs.Framework.Runtime
import RwLog.SpanLayer.Coverage

namespace RwLog

namespace CostedRuntime

variable (C : CostedRuntime)

theorem Covered.mono {P : Program} {q : Rel} {M : Interp} {x : GTerm × GTerm} {m n : Nat}
    (h : C.Covered P q M x m) (hmn : m ≤ n) : C.Covered P q M x n := by
  obtain ⟨a, ha, hx⟩ := h
  exact ⟨a, C.runtime.emitted_subset _ hmn ha, hx⟩

theorem CoversWithin.mono {P : Program} {q : Rel} {M : Interp} {x : GTerm × GTerm} {c c' : Nat}
    (h : C.CoversWithin P q M x c) (hc : c ≤ c') : C.CoversWithin P q M x c' := by
  obtain ⟨n, hn, hs⟩ := h
  exact ⟨n, hn, le_trans hs hc⟩

/-- On an input that halts, an honest machine has covered every pair of the
query when it halts. -/
theorem coversWithin_of_halts (hC : C.runtime.HonestExhaustion) {P : Program} {q : Rel}
    (hwf : P.WellFormed q) {n c : Nat} (hn : C.runtime.Halts (C.start P q) n)
    (hc : C.paid P q n ≤ c) {x : GTerm × GTerm}
    (hx : x ∈ P.pairs q) : C.CoversWithin P q P.sorts.interp x c := by
  have h := hC P q hwf n hn
  rw [h] at hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨a, ha, hxa⟩ := hx
  exact ⟨n, ⟨a, ha, hxa⟩, hc⟩

/-- A machine that has emitted nothing in its first `N` steps has paid for
`N + 1` steps at any step at which it has covered a pair. -/
theorem le_spent_of_covered {s : C.State} {N lo : Nat} (hq : C.runtime.emitted s N = [])
    (hlo : lo ≤ C.spent s (N + 1)) {n : Nat} {a : C.Ans} (ha : a ∈ C.runtime.emitted s n) :
    lo ≤ C.spent s n := by
  by_cases h : n ≤ N
  · have := C.runtime.emitted_subset s h ha
    rw [hq] at this
    exact absurd this List.not_mem_nil
  · exact le_trans hlo (C.spent_mono s (by omega))

end CostedRuntime

/-- `New` simulates `Old` when, for every number of steps of `Old`, some
number of steps of `New` costs at most `p` of what `Old` paid, has emitted an
answer covering each answer `Old` has emitted, and has halted if `Old` has. -/
theorem Simulates.of_steps {Old New : CostedRuntime} {p : Nat → Nat → Nat}
    (h : ∀ P q, P.WellFormed q → ∀ n, ∃ m,
      New.paid P q m ≤ p (Old.paid P q n) (P.size + q.size) ∧
      (∀ a ∈ Old.runtime.emitted (Old.start P q) n,
        ∃ b ∈ New.runtime.emitted (New.start P q) m, Answer.Covers P.sorts.interp b a) ∧
      (Old.runtime.Halts (Old.start P q) n → New.runtime.Halts (New.start P q) m)) :
    Simulates Old New p := by
  intro P q hwf n
  obtain ⟨m, hs, hcov, hh⟩ := h P q hwf n
  refine ⟨?_, fun hn => ⟨m, hh hn, hs⟩⟩
  rintro x ⟨a, ha, hx⟩
  obtain ⟨b, hb, hba⟩ := hcov a ha
  exact ⟨m, ⟨b, hb, hba hx⟩, hs⟩

/-- A simulation within `p` is a simulation within any larger bound. -/
theorem Simulates.mono {Old New : CostedRuntime} {p p' : Nat → Nat → Nat}
    (h : Simulates Old New p) (hp : ∀ c n, p c n ≤ p' c n) : Simulates Old New p' := by
  intro P q hwf n
  obtain ⟨h1, h2⟩ := h P q hwf n
  refine ⟨fun x hx => CostedRuntime.CoversWithin.mono _ (h1 x hx) (hp _ _), fun hn => ?_⟩
  obtain ⟨m, hm, hs⟩ := h2 hn
  exact ⟨m, hm, le_trans hs (hp _ _)⟩

/-- A rung without preprocessing is its engine at the kernel rung. -/
theorem CostedRung.machine_id (κ : KernelRung) (E : Engine) (A : ArtifactStore) :
    (CostedRung.mk Preprocessor.id E false).machine κ A = E.costed κ := by
  have h : ∀ P q, (Preprocessor.id.run κ A P q).val = (P, q, A) := fun P q =>
    congrArg Cost.val ((κ.refines P.sorts).pure_eq _)
  unfold CostedRung.machine
  simp only [h]
  rfl

/-- Two rungs without preprocessing: the improvement of the machines, and
preprocessing costs nothing. -/
theorem Advances.of_id {κ : KernelRung} {kind : Kind} {Old New : Engine} {b : Bounds}
    {C : ProgClass} (h : Improves kind (Old.costed κ) (New.costed κ) b C) :
    Advances κ kind ⟨Preprocessor.id, Old, false⟩ ⟨Preprocessor.id, New, false⟩ b (fun _ => 0) C where
  improves A := by rw [CostedRung.machine_id, CostedRung.machine_id]; exact h
  preCost A P q _ := by
    show (Preprocessor.id.run κ A P q).ticks ≤ 0
    rw [show Preprocessor.id.run κ A P q = pure (P, q, A) from (κ.refines P.sorts).pure_eq _]
    exact Nat.le_refl 0

/-- A bound that is met is met by anything larger. -/
theorem MeetsOn.mono {μ : Meter} {M : CostedRuntime} {C : ProgClass} {hi hi' : Nat → Nat}
    {f f' : Nat → Nat → Nat → Nat} (h : MeetsOn μ M C hi f) (hhi : ∀ k, hi k ≤ hi' k)
    (hf : ∀ k res n, f k res n ≤ f' k res n) : MeetsOn μ M C hi' f' where
  alone P r hm x hx := by
    obtain ⟨n, hn, hc⟩ := h.alone P r hm x hx
    exact ⟨n, hn, le_trans hc (hhi _)⟩
  inContext P r hm K hK hwf y hy res hres := by
    obtain ⟨n, hn, hc⟩ := h.inContext P r hm K hK hwf y hy res hres
    exact ⟨n, hn, le_trans hc (hf _ _ _)⟩

/-- A win is kept within any larger factor. -/
theorem Win.KeptBy.mono {w : Win} {M : CostedRuntime} {c c' : Nat} (h : w.KeptBy M c)
    (hc : c ≤ c') : w.KeptBy M c' :=
  MeetsOn.mono h (fun _ => Nat.mul_le_mul_right _ hc) fun _ _ _ => Nat.mul_le_mul_right _ hc

/-- A machine that improves by a win keeps that win, within the factor 1. -/
theorem Improves.keptBy {kind : Kind} {Old New : CostedRuntime} {b : Bounds} {C : ProgClass}
    (h : Improves kind Old New b C) : Win.KeptBy ⟨kind, C, b⟩ New 1 :=
  MeetsOn.mono h.separates.toMeetsOn (fun _ => (Nat.one_mul _).ge) fun _ _ _ => (Nat.one_mul _).ge

/-- An admitted rung keeps its own win and every win on the record it was
admitted over. -/
theorem Admits.keptBy {κ : KernelRung} {kind : Kind} {Old New : CostedRung} {b : Bounds}
    {d : DirBound} {pre : Nat → Nat} {C : ProgClass} {record : List Win} {keep : Nat}
    (h : Admits κ kind Old New b d pre C record keep) (A : ArtifactStore) :
    ∀ w ∈ (⟨kind, C, b⟩ : Win) :: record, w.KeptBy (New.machine κ A) (keep + 1) := by
  intro w hw
  rcases List.mem_cons.1 hw with rfl | hw
  · exact (h.improves A).keptBy.mono (Nat.le_add_left _ _)
  · exact (h.keeps A w hw).mono (Nat.le_succ _)

/-- Every rung of a ladder keeps every win on its record, each within a
constant factor of the bound the win was admitted with: no win is given back
by a later rung, of whatever kind. -/
theorem Ladder.keeps {κ : KernelRung} {base G : CostedRung} {record : List Win}
    (h : Ladder κ base G record) : ∃ c, ∀ A, ∀ w ∈ record, w.KeptBy (G.machine κ A) c := by
  cases h with
  | base => exact ⟨0, fun _ _ hw => absurd hw List.not_mem_nil⟩
  | admit _ ha => exact ⟨_, fun A => ha.keptBy A⟩

/-- Two rungs without preprocessing: admission is the improvement of the
machines, the direction bound of the new one, and that it keeps the wins on
the record. -/
theorem Admits.of_id {κ : KernelRung} {kind : Kind} {Old New : Engine} {b : Bounds}
    {d : DirBound} {C : ProgClass} {record : List Win} {keep : Nat}
    (h : Improves kind (Old.costed κ) (New.costed κ) b C)
    (hd : DirectionFree (New.costed κ) d.fn) (hk : ∀ w ∈ record, w.KeptBy (New.costed κ) keep) :
    Admits κ kind ⟨Preprocessor.id, Old, false⟩ ⟨Preprocessor.id, New, false⟩ b d (fun _ => 0) C record keep where
  toAdvances := Advances.of_id h
  direction A := by rw [CostedRung.machine_id]; exact hd
  keeps A := by rw [CostedRung.machine_id]; exact hk

end RwLog
