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
    (hwf : P.WellFormed q) {n c : Nat} (hn : C.runtime.Halts (C.init P q) n)
    (hc : C.spent (C.init P q) n ≤ c) {M : Interp} (hM : P.theory.Model M) {x : GTerm × GTerm}
    (hx : x ∈ P.semAt M q) : C.CoversWithin P q M x c := by
  have h := hC P q hwf n hn M hM
  rw [h] at hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨a, ha, hxa⟩ := hx
  exact ⟨n, ⟨a, ha, hxa⟩, hc⟩

/-- A machine that has emitted nothing in its first `N` steps has paid for
`N + 1` steps at any step at which it has covered a pair. -/
theorem le_spent_of_covered {s : C.State} {N lo : Nat} (hq : C.runtime.emitted s N = [])
    (hlo : lo ≤ C.spent s (N + 1)) {n : Nat} {a : Span} (ha : a ∈ C.runtime.emitted s n) :
    lo ≤ C.spent s n := by
  by_cases h : n ≤ N
  · have := C.runtime.emitted_subset s h ha
    rw [hq] at this
    simp at this
  · exact le_trans hlo (C.spent_mono s (by omega))

end CostedRuntime

/-- `New` simulates `Old` when, for every number of steps of `Old`, some
number of steps of `New` costs at most `p` of what `Old` paid, has emitted an
answer covering each answer `Old` has emitted, and has halted if `Old` has. -/
theorem Simulates.of_steps {Old New : CostedRuntime} {p : Nat → Nat → Nat}
    (h : ∀ P q, P.WellFormed q → ∀ n, ∃ m,
      New.spent (New.init P q) m ≤ p (Old.spent (Old.init P q) n) (P.size + q.size) ∧
      (∀ a ∈ Old.runtime.emitted (Old.init P q) n,
        ∃ b ∈ New.runtime.emitted (New.init P q) m, b.CoversLive P.theory a) ∧
      (Old.runtime.Halts (Old.init P q) n → New.runtime.Halts (New.init P q) m)) :
    Simulates Old New p := by
  intro P q hwf n
  obtain ⟨m, hs, hcov, hh⟩ := h P q hwf n
  refine ⟨?_, fun hn => ⟨m, hh hn, hs⟩⟩
  rintro M hM x ⟨a, ha, hx⟩
  obtain ⟨b, hb, hba⟩ := hcov a ha
  exact ⟨m, ⟨b, hb, hba M hM hx⟩, hs⟩

end RwLog
