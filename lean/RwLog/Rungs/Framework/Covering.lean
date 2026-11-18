/-
# Covering a level: proving the improvement statements

`Trusted/Cost.lean` states improvement by the cost of covering a level: what
a machine has used when the answers it has emitted relate every pair of the
level. The ways a rung establishes those statements are here, for any costed
runtime.

* A level once covered stays covered (`CostedRuntime.Covered.mono`).
* `NeverWorse.of_steps`: step by step, the new machine has covered every
  level the old one has, at a bounded cost, and has halted if the old one
  has.
* A machine that is never worse than one that halts on an input halts on it
  (`NeverWorse.terminates`).
* Every rung of a ladder has the laws (`Ladder.lawful`).
-/
import RwLog.Rungs.Framework.Cost
import RwLog.Trusted.Properties
import RwLog.Rungs.Framework.Runtime
import RwLog.SpanLayer.Coverage

namespace RwLog

namespace CostedRuntime

variable (C : CostedRuntime)

/-- A level once covered stays covered. -/
theorem Covered.mono {P : Program} {q : Rel} {c m n : Nat} (h : C.Covered P q c m)
    (hmn : m ≤ n) : C.Covered P q c n := fun p hp => by
  obtain ⟨a, ha, hpa⟩ := h p hp
  exact ⟨a, (C.runtime.emitted_prefix _ hmn).subset ha, hpa⟩

theorem CoversUsing.mono {μ : Meter} {P : Program} {q : Rel} {c b b' : Nat}
    (h : C.CoversUsing μ P q c b) (hb : b ≤ b') : C.CoversUsing μ P q c b' := by
  obtain ⟨n, hn, hs⟩ := h
  exact ⟨n, hn, le_trans hs hb⟩

theorem ExhaustsWithin.mono {P : Program} {q : Rel} {b b' : Nat}
    (h : C.ExhaustsWithin P q b) (hb : b ≤ b') : C.ExhaustsWithin P q b' := by
  obtain ⟨n, hn, hs⟩ := h
  exact ⟨n, hn, le_trans hs hb⟩

end CostedRuntime

/-- `New` is never worse than `Old` when, for every number of steps of `Old`,
some number of steps of `New` costs at most `p` of what `Old` paid, has
covered every level `Old` has covered, and has halted if `Old` has. The
bound grows with the size. -/
theorem NeverWorse.of_steps {Old New : CostedRuntime} {p : Nat → Nat → Nat}
    (hp : ∀ a n n', n ≤ n' → p a n ≤ p a n')
    (h : ∀ P q, P.WellFormed q → ∀ n, ∃ m,
      New.paid P q m ≤ p (Old.paid P q n) (P.size + q.size) ∧
      (∀ c, Old.Covered P q c n → New.Covered P q c m) ∧
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
  exact ⟨fun c hc => CostedRuntime.CoversUsing.mono _ (h1 c hc) (hp _ _),
    fun hn => CostedRuntime.ExhaustsWithin.mono _ (h2 hn) (hp _ _)⟩

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
  | base hb => exact hb
  | admit _ _ hl => exact hl

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
