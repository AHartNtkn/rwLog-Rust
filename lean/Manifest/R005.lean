import RwLog.Rungs.R005.Sorts
import RwLog.Rungs.R005.Bounds
import RwLog.Lib.Audit

/-!
# Manifest of R005, the yardstick

What is claimed of R005, in one file the build checks (roadmap L06).

* **Headline theorems.** Each is restated here in full and proved by the
  theorem it names, so the build fails if a statement changes or weakens.
* **Bounds.** The lower bound on a mirrored machine that is proved, and the
  two lower bounds on R005 that are stated and not proved.
* **Trusted files.** The files under `Trusted/` this manifest depends on, and
  the files whose definitions those are written with, compared with the
  list written here.
* **Axioms.** The headline theorems use only Lean's three standard axioms.
-/

namespace RwLog.Manifest.R005

/-! ## Headline theorems -/

section

variable {R : Sorts → Type} [∀ S, Answer (R S)] [∀ S, DecidableEq (R S)]
  {dom : ∀ S, Domain (R S)} {K : ∀ S, Kernel (R S) Cost} {hK : ∀ S, (K S).Refines (dom S)}
  (hD : ∀ S : Sorts, S.WellFormed → (dom S).Lawful S.interp)

/-- R005 keeps every property of `Runtime.Keeps`, and halts where R001
halts, at every kernel that refines a lawful domain. -/
example : (R005.engine.costedAt dom K hK).runtime.Keeps (R001.engine.costedAt dom K hK).runtime :=
  R005.keeps hD

/-- R005 shows what R004 shows, step for step, up to the order of the answers
of a step. -/
example {P : Program} {q : Rel} (wf : P.WellFormed q) (n : Nat) :
    List.Forall₂ (Shown.Rel fun xs ys => xs.Perm ys)
      ((R005.engine.costedAt dom K hK).runtime.trace
        ((R005.engine.costedAt dom K hK).runtime.init P q) n)
      ((R004.engine.costedAt dom K hK).runtime.trace
        ((R004.engine.costedAt dom K hK).runtime.init P q) n) :=
  R005.trace hD wf n

/-- R005 runs the same whatever the grouping of `;` and the order and grouping
of `&`, and when it is done it reports the maximal answers it emitted. -/
example : (R005.engine.costedAt dom K hK).runtime.SeqAssoc ∧
    (R005.engine.costedAt dom K hK).runtime.AndComm ∧
    (R005.engine.costedAt dom K hK).runtime.AndAssoc ∧
    (R005.engine.costedAt dom K hK).runtime.FinalMaximal :=
  ⟨(R005.record hD).seqAssoc, (R005.record hD).andComm, (R005.record hD).andAssoc,
    (R005.record hD).finalMaximal⟩

/-- R005 emits no progress certificate. -/
example {P : Program} {q : Rel} (wf : P.WellFormed q) (k n : Nat) :
    ¬ (R005.engine.costedAt dom K hK).runtime.Certifies
      ((R005.engine.costedAt dom K hK).runtime.init P q) k n :=
  R005.neverCertifies hD wf k n

end

/-- At a kernel rung no hypothesis is left: its domain is lawful. -/
example (κ : KernelRung) :
    (R005.engine.costed κ).runtime.Keeps (R001.engine.costed κ).runtime :=
  R005.keeps_rung κ

/-- At the domain of sorts no hypothesis is left. -/
example {K : ∀ S, Kernel (Sorts.Rep S) Cost} {hK : ∀ S, (K S).Refines (Sorts.dom S)} :
    (R005.engine.costedAt Sorts.dom K hK).runtime.Keeps
      (R001.engine.costedAt Sorts.dom K hK).runtime :=
  R005.keeps_sorts

/-! ## Bounds -/

/-- Proved: a mirrored engine has paid at least the cheaper of its two runs. -/
example (E : Engine) {R : Sorts → Type} [∀ S, Answer (R S)] [∀ S, DecidableEq (R S)]
    (dom : ∀ S, Domain (R S)) (K : ∀ S, Kernel (R S) Cost) (hK : ∀ S, (K S).Refines (dom S))
    (P : Program) (q : Rel) (n : Nat) :
    min (Mirror.cost (E.stepAt dom K hK P) (E.startAt dom K hK P q.norm) n)
        (Mirror.cost (E.stepAt dom K hK P) (E.startAt dom K hK P q.norm.normConv) n) ≤
      (E.mirrored.costedAt dom K hK).paid P q n :=
  Mirror.paid_ge_min E dom K hK P q n

/-- Stated, not proved: on the chain restricted in the middle each run of
R004 has cost `2 ^ k` by any step at which R005 relates `z` to `z`. -/
example (κ : KernelRung) : R005.MidLower κ ↔
    ∀ k, Mirror.LowerOn κ R004.engine ⟨[], []⟩ (R005.mid k) (.sym "z", .sym "z") (2 ^ k) :=
  Iff.rfl

/-- Stated, not proved: on the free factor beside an answer each run of R004
has cost `2 ^ k` by any step at which R005 relates `a` to `a`. -/
example (κ : KernelRung) : R005.FreeLower κ ↔
    ∀ k, Mirror.LowerOn κ R004.engine (R005.freeProg k) R005.freeRel (.sym "a", .sym "a") (2 ^ k) :=
  Iff.rfl

/-- What either gives: the bound on what R005 has paid. -/
example (κ : KernelRung) (h : R005.FreeLower κ) (k : Nat) {n : Nat}
    (hx : (R005.engine.costed κ).Covered (R005.freeProg k) R005.freeRel (Sorts.interp [])
      (.sym "a", .sym "a") n) :
    2 ^ k ≤ (R005.engine.costed κ).paid (R005.freeProg k) R005.freeRel n :=
  h.paid k hx

/-! ## Trusted files -/

/--
info: [RwLog.Trusted.Charged,
 RwLog.Trusted.Cost,
 RwLog.Trusted.CostMonad,
 RwLog.Trusted.Domain,
 RwLog.Trusted.Engine,
 RwLog.Trusted.Kernel,
 RwLog.Trusted.Properties,
 RwLog.Trusted.Runtime,
 RwLog.Trusted.Semantics,
 RwLog.Trusted.Syntax]
and the definitions they are written with:
[RwLog.Kernel.Canon,
 RwLog.Kernel.Covers,
 RwLog.Kernel.Derivation,
 RwLog.Kernel.Iface,
 RwLog.Kernel.Match,
 RwLog.Kernel.NormalForm,
 RwLog.Kernel.NormalFormCorrect,
 RwLog.Kernel.Order,
 RwLog.Kernel.Solve,
 RwLog.Kernel.Span,
 RwLog.Kernel.TermFacts,
 RwLog.SpanLayer.Algebra,
 RwLog.SpanLayer.Bridge,
 RwLog.SpanLayer.Coverage,
 RwLog.SpanLayer.Derives,
 RwLog.SpanLayer.Modulo,
 RwLog.SpanLayer.Triples]
-/
#guard_msgs in #trusted_files RwLog.Trusted

/-! ## Axioms -/

#assert_axioms RwLog.R005.keeps RwLog.R005.keeps_rung RwLog.R005.keeps_sorts RwLog.R005.trace
  RwLog.R005.record RwLog.R005.neverCertifies RwLog.Mirror.paid_ge_min

end RwLog.Manifest.R005
