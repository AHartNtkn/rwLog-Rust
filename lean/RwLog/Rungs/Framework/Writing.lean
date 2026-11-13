/-
# What every engine has because it starts from the normal form

An engine (`Trusted/Cost.lean`) is handed the root node of the normal form of
the query, and sees nothing else of the query. Two queries with the same
normal form are therefore started in the same state and have the same run
(`Engine.init_of_norm`, `Engine.trace_of_norm`).

The normal form (`Kernel/NormalForm.lean`) flattens `;`, sorts the members of
`&` and makes a sorted set of the members of `|`. So for every engine, at
every kernel of every constraint domain, the run does not depend on

* the order and the grouping of `|` (`Engine.orComm`, `Engine.orAssoc`),
* the grouping of `;` (`Engine.seqAssoc`),
* the order and the grouping of `&` (`Engine.andComm`, `Engine.andAssoc`),

at the top of the query. These are the five laws of
`Trusted/Properties.lean`, as equations between traces. Nothing about the
engine is used.
-/
import RwLog.Rungs.Framework.Derivation
import RwLog.Kernel.NormalFormCorrect

namespace RwLog

namespace Engine

variable (E : Engine) {R : Sorts → Type} [∀ S, Answer (R S)] [∀ S, DecidableEq (R S)]
  (dom : ∀ S, Domain (R S)) (K : ∀ S, Kernel (R S) Cost) (hK : ∀ S, (K S).Refines (dom S))

/-- An engine starts two queries with the same normal form in the same
state. -/
theorem init_of_norm (P : Program) {q q' : Rel} (h : q.norm = q'.norm) :
    (E.costedAt dom K hK).runtime.init P q = (E.costedAt dom K hK).runtime.init P q' := by
  show ((E.costedAt dom K hK).init P q).val = ((E.costedAt dom K hK).init P q').val
  simp only [costedAt, Cost.bind_val, Charged.load, Charged.op_val, h]

/-- Two queries with the same normal form have the same run. -/
theorem trace_of_norm (P : Program) {q q' : Rel} (h : q.norm = q'.norm) (n : Nat) :
    (E.costedAt dom K hK).runtime.trace ((E.costedAt dom K hK).runtime.init P q) n =
      (E.costedAt dom K hK).runtime.trace ((E.costedAt dom K hK).runtime.init P q') n := by
  rw [E.init_of_norm dom K hK P h]

/-- P1.1 for every engine: swapping the branches of `|` does not change the
run. -/
theorem orComm : (E.costedAt dom K hK).runtime.OrComm := fun P a b n =>
  E.trace_of_norm dom K hK P (normB_or_comm false a b) n

/-- P1.1 for every engine: regrouping `|` does not change the run. -/
theorem orAssoc : (E.costedAt dom K hK).runtime.OrAssoc := fun P a b c n =>
  E.trace_of_norm dom K hK P (normB_or_assoc false a b c) n

/-- Regrouping `;` does not change the run of any engine. -/
theorem seqAssoc : (E.costedAt dom K hK).runtime.SeqAssoc := fun P a b c n =>
  E.trace_of_norm dom K hK P (normB_seq_assoc false a b c) n

/-- Swapping the sides of `&` does not change the run of any engine. -/
theorem andComm : (E.costedAt dom K hK).runtime.AndComm := fun P a b n =>
  E.trace_of_norm dom K hK P (normB_and_comm false a b) n

/-- Regrouping `&` does not change the run of any engine. -/
theorem andAssoc : (E.costedAt dom K hK).runtime.AndAssoc := fun P a b c n =>
  E.trace_of_norm dom K hK P (normB_and_assoc false a b c) n

end Engine

end RwLog
