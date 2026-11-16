/-
# Carrying every kept property along a trace

`SameRun` (`Rungs/Framework/Transfer.lean`) carries Tier 0 between two
machines that have emitted the same answers after every number of steps. The
properties of `Runtime.Keeps` that are stated on the trace (the certificates,
the converse, the mirrored program, no answer covered by an earlier one) need
more: `SameTrace R' R` says the two machines show the same thing at every
step, up to the order of the answers of the step and up to equivalent
answers.

* `SameTrace.sameRun`: such machines run the same.
* `SameTrace.certifies`, `.terminates`: they certify and halt together.
* `SameTrace.keeps`: `R'` keeps every property `R` keeps, with the same base.
  The laws of `|` of `R'` are asked beside: they are equalities of traces and
  hold of every engine (`Engine.orComm`, `Engine.orAssoc`).

`HonestProgress.of_never` is honest progress for a machine that emits no
certificate.

The lemmas on well-formed queries (`ProgramOf.WellFormed.of_sub` and the
queries built from the sides of a `;`) are here too.
-/
import RwLog.Rungs.Framework.Transfer
import RwLog.Rungs.Framework.Direction

namespace RwLog

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

/-! ## Traces -/

section trace

variable {A B : Type} [Answer A] [Answer B] {M : Interp}

theorem Answer.Covers.of_equiv {a b : A} {a' b' : B} (ea : Answer.Equiv M a a')
    (eb : Answer.Equiv M b b') (h : Answer.Covers M a b) : Answer.Covers M a' b' :=
  fun _ hp => ea.2 (h (eb.1 hp))

theorem TraceEquiv.map_swap {t : List (Shown A)} {t' : List (Shown B)}
    (h : TraceEquiv M t t') : TraceEquiv M (t.map Shown.swap) (t'.map Shown.swap) :=
  List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2
    (List.Forall₂.imp (fun _ _ h => h.swap) h))

/-- Traces that show the same answers at every step, in another order,
agree. -/
theorem TraceEquiv.of_perm {t t' : List (Shown A)}
    (h : List.Forall₂ (Shown.Rel fun xs ys => xs.Perm ys) t t') : TraceEquiv M t t' :=
  List.Forall₂.imp (fun x y hxy => by
    cases x <;> cases y <;> first | exact StepEquiv.of_perm hxy | exact hxy) h

end trace

namespace Runtime

variable {R' R Base : Runtime}

/-- Honest progress of a machine that emits no certificate. -/
theorem HonestProgress.of_never
    (h : ∀ P q, P.WellFormed q → ∀ k n, ¬ R.Certifies (R.init P q) k n) : R.HonestProgress :=
  fun P q wf k n hc => absurd hc (h P q wf k n)

/-- `R'` shows at every step what `R` shows, up to the order of the answers
of the step and up to equivalent answers. -/
structure SameTrace (R' R : Runtime) : Prop where
  trace : ∀ P q, P.WellFormed q → ∀ n,
    TraceEquiv P.sorts.interp (R'.trace (R'.init P q) n) (R.trace (R.init P q) n)

namespace SameTrace

theorem refl (R : Runtime) : SameTrace R R := ⟨fun _ _ _ _ => TraceEquiv.refl _⟩

theorem symm (h : SameTrace R' R) : SameTrace R R' := ⟨fun P q wf n => (h.trace P q wf n).symm⟩

variable {P : Program} {q : Rel}

theorem halts (h : SameTrace R' R) (wf : P.WellFormed q) (n : Nat) :
    R'.Halts (R'.init P q) n ↔ R.Halts (R.init P q) n := by
  have key : ∀ {R' R : Runtime}, SameTrace R' R → R.Halts (R.init P q) n →
      R'.Halts (R'.init P q) n := fun {R' R} h hn => by
    obtain ⟨fin, hfin⟩ := Option.isSome_iff_exists.1 hn
    obtain ⟨fin', hfin'⟩ := TraceEquiv.final (h.trace P q wf n)
      ⟨fin, (R.final_eq_some_iff n _ fin).1 hfin⟩
    exact Option.isSome_iff_exists.2 ⟨fin', (R'.final_eq_some_iff n _ fin').2 hfin'⟩
  exact ⟨key h.symm, key h⟩

theorem terminates (h : SameTrace R' R) (wf : P.WellFormed q) :
    R'.Terminates P q ↔ R.Terminates P q :=
  ⟨fun ⟨n, hn⟩ => ⟨n, (h.halts wf n).1 hn⟩, fun ⟨n, hn⟩ => ⟨n, (h.halts wf n).2 hn⟩⟩

/-- Machines that show the same thing at every step run the same. -/
theorem sameRun (h : SameTrace R' R) : SameRun R' R where
  emitted P q wf n := by
    rw [R'.emitted_eq_flatMap_trace, R.emitted_eq_flatMap_trace]
    exact TraceEquiv.emits (h.trace P q wf n)
  halts _ _ wf n := h.halts wf n

/-- They certify together. -/
theorem certifies (h : SameTrace R' R) (wf : P.WellFormed q) (k n : Nat) :
    R'.Certifies (R'.init P q) k n ↔ R.Certifies (R.init P q) k n := by
  have key : ∀ {R' R : Runtime}, SameTrace R' R → R'.Certifies (R'.init P q) k n →
      R.Certifies (R.init P q) k n := fun {R' R} h hc => by
    obtain ⟨y, hy, hxy⟩ := forall₂_getElem? (h.trace P q wf (k + 1)) hc
    cases y with
    | level m => obtain rfl : n = m := hxy; exact hy
    | answers _ => exact hxy.elim
    | final _ => exact hxy.elim
  exact ⟨key h, key h.symm⟩

theorem honestProgress (h : SameTrace R' R) (hp : R.HonestProgress) : R'.HonestProgress :=
  fun P q wf k n hc p hpq h₁ h₂ => by
    obtain ⟨a, ha, hpa⟩ := hp P q wf k n ((h.certifies wf k n).1 hc) p hpq h₁ h₂
    obtain ⟨a', ha', e⟩ := h.sameRun.symm.answer wf ha
    exact ⟨a', ha', e.2 hpa⟩

theorem emptySide (h : SameTrace R' R) (he : R.EmptySide) : R'.EmptySide :=
  fun P a b wf ht hemp => by
    have ht' : R.Terminates P a := (h.terminates wf.seq_left).1 ht
    have he' : R.Answers P a = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun x ⟨n, hx⟩ => ?_
      obtain ⟨x', hx', -⟩ := h.sameRun.symm.answer wf.seq_left hx
      have : x' ∈ R'.Answers P a := ⟨n, hx'⟩
      rw [hemp] at this
      exact this
    obtain ⟨h₁, h₂, h₃, h₄⟩ := he P a b wf ht' he'
    exact ⟨(h.terminates wf).2 h₁, (h.terminates wf.seq_swap).2 h₂,
      (h.terminates wf.and_of_seq).2 h₃, (h.terminates wf.seq_swap.and_of_seq).2 h₄⟩

theorem convTrace (h : SameTrace R' R) (hc : R.ConvTrace) : R'.ConvTrace :=
  fun P q n wf => (h.trace P (.conv q) wf.conv n).trans
    ((hc P q n wf).trans (h.trace P q wf n).symm.map_swap)

theorem dualTrace (h : SameTrace R' R) (hd : R.DualTrace) : R'.DualTrace :=
  fun P q n wf => (h.trace P.dual q.dual wf.dual n).trans
    ((hd P q n wf).trans (h.trace P q wf n).symm.map_swap)

/-- **A machine that shows at every step what another shows keeps every
property the other keeps.** The laws of `|` are equalities of traces of the
machine itself and hold of every engine. -/
theorem keeps (h : SameTrace R' R) (hk : R.Keeps Base)
    (orComm : R'.OrComm) (orAssoc : R'.OrAssoc) : R'.Keeps Base where
  sound := h.sameRun.sound hk.sound
  pointComplete := (h.sameRun.complete hk.complete).pointwise
  honest := h.sameRun.honest ⟨hk.sound, hk.complete, hk.honest⟩
  honestProgress := h.honestProgress hk.honestProgress
  derivationGeneral := h.sameRun.derivationGeneral hk.derivationGeneral
  terminates := fun P q wf ht => (h.terminates wf).2 (hk.terminates P q wf ht)
  orComm := orComm
  orAssoc := orAssoc
  emptySide := h.emptySide hk.emptySide
  convTrace := h.convTrace hk.convTrace
  dualTrace := h.dualTrace hk.dualTrace
  complete := h.sameRun.complete hk.complete

end SameTrace

end Runtime

end RwLog
