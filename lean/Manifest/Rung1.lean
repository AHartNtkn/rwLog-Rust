import RwLog.Rungs.Symmetric.Rung
import RwLog.Rungs.Framework.Latency
import RwLog.Lib.Audit

/-!
# Manifest of rung 1

What is claimed of rung 1, the symmetric engine with the raced unfolding, in
one file the build checks.

* **Headline theorems.** Each is restated here in full and proved by the
  theorem it names, so the build fails if a statement changes or weakens.
* **Trusted files.** The files under `Trusted/` this manifest depends on, and
  the files whose definitions those are written with, compared with the
  list written here.
* **Axioms.** The headline theorems use only Lean's three standard axioms.
-/

namespace RwLog.Manifest.Rung1

/-! ## Headline theorems -/

/-- Rung 1 has the three laws at every kernel rung: whatever the artifact
store, it is sound, every pair the relation relates is related by an answer
it emits, and when it reports that it is done its answers relate exactly the
pairs of the relation. -/
example (κ : KernelRung) (A : ArtifactStore) :
    ((Symmetric.rung1.rung κ).runtime κ A).Sound ∧
    ((Symmetric.rung1.rung κ).runtime κ A).PointComplete ∧
    ((Symmetric.rung1.rung κ).runtime κ A).HonestExhaustion :=
  ⟨(Symmetric.rung1_lawful κ A).sound, (Symmetric.rung1_lawful κ A).complete,
    (Symmetric.rung1_lawful κ A).honest⟩

/-- Rung 1 is the base of the ladder, with an empty record of gains. -/
example (κ : KernelRung) : Ladder κ Symmetric.rung1 Symmetric.rung1 [] :=
  Symmetric.rung1_ladder κ

/-- Every rung of a ladder has the laws. -/
example {κ : KernelRung} {base G : CostedRung} {record : List Win}
    (h : Ladder κ base G record) : G.Lawful κ :=
  h.lawful

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

#assert_axioms RwLog.Symmetric.rung1_lawful RwLog.Symmetric.rung1_ladder RwLog.Symmetric.laws
  RwLog.Ladder.lawful

end RwLog.Manifest.Rung1
