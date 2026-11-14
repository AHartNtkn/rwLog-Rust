import RwLog.Rungs.R005.Sorts
import RwLog.Rungs.R005.Bounds
import Tests.R005Runs
import Lean

/-!
# Manifest of R005, the yardstick

What is claimed of R005, in one file the build checks (roadmap L06).

* **Headline theorems.** Each is restated here in full and proved by the
  theorem it names, so the build fails if a statement changes or weakens.
* **Bounds.** The lower bound on a mirrored machine that is proved, and the
  two lower bounds on R005 that are stated and not proved.
* **Trusted files.** The files under `Trusted/` this manifest depends on,
  compared with the list written here.
* **Axioms.** The headline theorems use only Lean's three standard axioms.
* **Space.** What R005 pays and the most cells it has live at one moment
  (`CostedRuntime.space`, the space component of `Cost`), measured on the
  conformance programs and the two families. These are measurements at the
  kernel of spans as they are written; no bound on space is proved.
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
example : R005.MidLower ↔
    ∀ k, Mirror.LowerOn R004.engine ⟨[], []⟩ (R005.mid k) (.sym "z", .sym "z") (2 ^ k) :=
  Iff.rfl

/-- Stated, not proved: on the free factor beside an answer each run of R004
has cost `2 ^ k` by any step at which R005 relates `a` to `a`. -/
example : R005.FreeLower ↔
    ∀ k, Mirror.LowerOn R004.engine (R005.freeProg k) R005.freeRel (.sym "a", .sym "a") (2 ^ k) :=
  Iff.rfl

/-- What either gives: the bound on what R005 has paid. -/
example (h : R005.FreeLower) (k : Nat) {n : Nat}
    (hx : R005.engine.costed.Covered (R005.freeProg k) R005.freeRel (Sorts.interp [])
      (.sym "a", .sym "a") n) :
    2 ^ k ≤ R005.engine.costed.paid (R005.freeProg k) R005.freeRel n :=
  h.paid k hx

/-! ## Trusted files -/

open Lean Elab Command in
/-- The files under `Trusted/` among everything this file imports. -/
elab "#trusted_files" : command => do
  let ms := (← getEnv).header.moduleNames.filter fun m => (`RwLog.Trusted).isPrefixOf m
  logInfo m!"{(ms.map toString).qsort (· < ·)}"

/--
info: [RwLog.Trusted.Charged,
 RwLog.Trusted.Cost,
 RwLog.Trusted.CostMonad,
 RwLog.Trusted.Domain,
 RwLog.Trusted.Engine,
 RwLog.Trusted.Kernel,
 RwLog.Trusted.KernelRung,
 RwLog.Trusted.Properties,
 RwLog.Trusted.Runtime,
 RwLog.Trusted.Semantics,
 RwLog.Trusted.Syntax]
-/
#guard_msgs in #trusted_files

/-! ## Axioms -/

/-- info: 'RwLog.R005.keeps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R005.keeps
/-- info: 'RwLog.R005.keeps_sorts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R005.keeps_sorts
/-- info: 'RwLog.R005.trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R005.trace
/-- info: 'RwLog.R005.record' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R005.record
/-- info: 'RwLog.R005.neverCertifies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R005.neverCertifies
/-- info: 'RwLog.Mirror.paid_ge_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Mirror.paid_ge_min

/-! ## Space -/

open RwLog.Tests

/-- The ticks paid and the most cells live at one moment, in the first `n`
steps. -/
def use (E : Engine) (P : Program) (q : Rel) (n : Nat) : Nat × Nat :=
  (E.costed.paid P q n, E.costed.space P q n)

-- `add ; @2`, to its end, and twelve steps of the left-recursive `lr`.
#guard use R005.engine addP (.seq (.call "add") (.at_ (num 2))) 40 == (3477773, 85440)
#guard use R005.engine (prog [("lr", lr)]) (.call "lr") 12 == (121814, 2072)

-- The chain restricted in the middle, `k` from 0 to 3, to its end: R005, and
-- R004 on the query alone.
#guard (List.range 4).map (fun k => use R005.engine empty (R005.mid k) 12) ==
  [(445, 22), (52933, 1012), (393232, 9170), (803420, 15712)]
#guard (List.range 4).map (fun k => use R004.engine empty (R005.mid k) 12) ==
  [(68, 16), (8781, 841), (49695, 3592), (139922, 10265)]

-- The free factor beside an answer, `k` from 0 to 3, to the step at which
-- `a -> a` arrives.
#guard (List.range 4).map (fun k => use R005.engine (R005.freeProg k) R005.freeRel 4) ==
  [(10931, 729), (27343, 1521), (60258, 2601), (220960, 3969)]

end RwLog.Manifest.R005
