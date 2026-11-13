/-
# What the hedge keeps

`Hedge.machine A B` emits answers of `A` and answers of `B`, covers every
answer of `A`, and halts exactly when `A` does. So of the properties every
rung keeps (`Trusted/Properties.lean`):

* it is sound and its answers are derivation-general when that holds of `A`
  and of `B`;
* it is complete, exhausts honestly, terminates where `A` does and fails
  finitely on an empty side when that holds of `A` alone: `B` need be neither
  complete nor ever done;
* no answer is covered by an earlier one when that holds of `A`: an answer of
  one machine that an answer of the other covers is dropped.

Monotonicity in the theory follows from completeness and derivation-general
answers for any runtime (`Runtime.theory_mono_answers`).

The trace laws (`OrComm`, `OrAssoc`, `ConvTrace`, `DualTrace`) compare runs
on different queries and depend on what the two machines cost; they are in
`Laws.lean`.
-/
import RwLog.Rungs.Hedge.Runs
import RwLog.Rungs.Hedge.FirstBound
import RwLog.Rungs.Framework.Tier0

namespace RwLog

open Cost

namespace Hedge

variable {A B : CostedRuntime}

theorem sound (hAs : A.runtime.Sound) (hBs : B.runtime.Sound) : (machine A B).runtime.Sound := by
  intro P q hP m x hx
  rcases emitted_origin P q m x hx with ⟨n, h⟩ | ⟨n, h⟩
  · exact hAs P q hP n x h
  · exact hBs P q hP n x h

theorem derivationGeneral (hAg : A.runtime.DerivationGeneral) (hBg : B.runtime.DerivationGeneral) :
    (machine A B).runtime.DerivationGeneral := by
  intro P q hP x ⟨m, hx⟩
  rcases emitted_origin P q m x hx with ⟨n, h⟩ | ⟨n, h⟩
  · exact hAg P q hP x ⟨n, h⟩
  · exact hBg P q hP x ⟨n, h⟩

theorem noSubsumed_of (hAn : A.runtime.NoSubsumed) : (machine A B).runtime.NoSubsumed :=
  fun P q hP m => noSubsumed P q (hAn P q hP) m

/-- When the hedge halts, `A` has. -/
theorem terminates_first {P : Program} {q : Rel} (h : (machine A B).runtime.Terminates P q) :
    A.runtime.Terminates P q := by
  obtain ⟨m, hm⟩ := h
  obtain ⟨n, hn, -⟩ := halts_first P q m hm
  exact ⟨n, hn⟩

theorem honest (hs : (machine A B).runtime.Sound) (hAh : A.runtime.HonestExhaustion) :
    (machine A B).runtime.HonestExhaustion := by
  intro P q hP m hm M hM
  obtain ⟨n, hn, hcov⟩ := halts_first P q m hm
  apply Set.Subset.antisymm
  · rw [hAh P q hP n hn M hM]
    intro p hp
    obtain ⟨x, hx, hpx⟩ := Set.mem_iUnion₂.1 hp
    obtain ⟨y, hy, hyx⟩ := hcov x hx
    exact Set.mem_iUnion₂.2 ⟨y, hy, hyx.at_subset M hpx⟩
  · intro p hp
    obtain ⟨y, hy, hpy⟩ := Set.mem_iUnion₂.1 hp
    exact hs P q hP m y hy M hM hpy

section

variable (hA : ∀ (s : A.State) (as : List Span) (s' : A.State),
    (A.step s).val = .emit as s' → sizes as ≤ (A.step s).ticks)
  (hB : ∀ (s : B.State) (bs : List Span) (s' : B.State),
    (B.step s).val = .emit bs s' → sizes bs ≤ (B.step s).ticks)
include hA hB

theorem complete (hAc : A.runtime.Complete) : (machine A B).runtime.Complete := by
  intro P q hP s hs
  rcases hAc P q hP s hs with hdead | ⟨n, a, ha, hcov⟩
  · exact .inl hdead
  · obtain ⟨m, -, hc, -⟩ := follows_first hA hB P q n
    obtain ⟨y, hy, hya⟩ := hc a ha
    exact .inr ⟨m, y, hy, fun M hM => (hcov M hM).trans (hya.at_subset M)⟩

/-- When `A` halts, the hedge does. -/
theorem terminates_of_first {P : Program} {q : Rel} (h : A.runtime.Terminates P q) :
    (machine A B).runtime.Terminates P q := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨m, -, -, hh⟩ := follows_first hA hB P q n
  exact ⟨m, hh hn⟩

theorem terminatesWhere {Base : Runtime} (hAt : A.runtime.TerminatesWhere Base) :
    (machine A B).runtime.TerminatesWhere Base :=
  fun P q hP hb => terminates_of_first hA hB (hAt P q hP hb)

theorem emptySide (hAe : A.runtime.EmptySide) : (machine A B).runtime.EmptySide := by
  intro P a b hP ht he
  have hAt := terminates_first ht
  have hAe' : A.runtime.Answers P a = ∅ := by
    apply Set.eq_empty_of_forall_notMem
    rintro x ⟨n, hx⟩
    obtain ⟨m, -, hc, -⟩ := follows_first hA hB P a n
    obtain ⟨y, hy, -⟩ := hc x hx
    have : y ∈ (machine A B).runtime.Answers P a := ⟨m, hy⟩
    rw [he] at this
    exact this
  obtain ⟨h1, h2, h3, h4⟩ := hAe P a b hP hAt hAe'
  exact ⟨terminates_of_first hA hB h1, terminates_of_first hA hB h2,
    terminates_of_first hA hB h3, terminates_of_first hA hB h4⟩

end

end Hedge

end RwLog
