import RwLog

/-!
# Axiom audit

Every headline theorem must depend only on Lean's three standard axioms.
`#guard_msgs` makes the build fail if any theorem picks up `sorryAx` or a
new axiom.
-/

/-- info: 'RwLog.sem_eq_derivable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.sem_eq_derivable

/-- info: 'RwLog.Conformance.c2_nonzero_z' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Conformance.c2_nonzero_z

/-- info: 'RwLog.Conformance.c2_different_pair_zz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Conformance.c2_different_pair_zz

/-- info: 'RwLog.Conformance.c2_nonzero_sz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Conformance.c2_nonzero_sz

/-- info: 'RwLog.Conformance.c4_neq_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Conformance.c4_neq_self

/-- info: 'RwLog.Conformance.c4_eq_and_neq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Conformance.c4_eq_and_neq

/-- info: 'RwLog.Conformance.different_alone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Conformance.different_alone

/-- info: 'RwLog.Conformance.stores_combine_across_seq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Conformance.stores_combine_across_seq

/-- info: 'RwLog.Conformance.eqNeq_wellFormed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Conformance.eqNeq_wellFormed

/-- info: 'RwLog.Conformance.c4_pin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Conformance.c4_pin

/-- info: 'RwLog.Conformance.pinTheory_wellFormed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Conformance.pinTheory_wellFormed

/-- info: 'RwLog.Conformance.c4_pinKeep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Conformance.c4_pinKeep

/-- info: 'RwLog.Conformance.pinKeep_model_empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Conformance.pinKeep_model_empty

/-- info: 'RwLog.Conformance.c4_pin_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Conformance.c4_pin_at

/-- info: 'RwLog.Conformance.c4_pinKeep_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Conformance.c4_pinKeep_at

/-- info: 'RwLog.Refutes.sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Refutes.sound

/-- info: 'RwLog.Conformance.pinKeep_wellFormed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Conformance.pinKeep_wellFormed

/-! ## Shared kernel and rung framework -/

/-- info: 'RwLog.Span.covers?_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Span.covers?_iff

/-- info: 'RwLog.Theory.refutes?_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Theory.refutes?_sound

/-- info: 'RwLog.Theory.simplify_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Theory.simplify_exact

/-- info: 'RwLog.Theory.present_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Theory.present_exact

/-- info: 'RwLog.Theory.simplify_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Theory.simplify_stable

/-- info: 'RwLog.ProgramOf.sem_dual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.ProgramOf.sem_dual

/-- info: 'RwLog.Runtime.finite_answers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Runtime.finite_answers

/-- info: 'RwLog.Runtime.Tier0Cert.tier0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Runtime.Tier0Cert.tier0

/-- info: 'RwLog.Runtime.derivationGeneral_of_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Runtime.derivationGeneral_of_refines

/-- info: 'RwLog.Runtime.theory_mono_answers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Runtime.theory_mono_answers

/-- info: 'RwLog.Runtime.trace_of_sim' depends on axioms: [propext] -/
#guard_msgs in #print axioms RwLog.Runtime.trace_of_sim

/-- info: 'RwLog.Runtime.SameRun.tier0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Runtime.SameRun.tier0

/-- info: 'RwLog.Runtime.SameRun.terminatesOn' does not depend on any axioms -/
#guard_msgs in #print axioms RwLog.Runtime.SameRun.terminatesOn

/-- info: 'RwLog.Runtime.HonestExhaustion.transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Runtime.HonestExhaustion.transfer

/-- info: 'RwLog.Rung.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Rung.sound

/-- info: 'RwLog.Rung.pointComplete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Rung.pointComplete

/-- info: 'RwLog.Rung.honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Rung.honest

/-- info: 'RwLog.simpLaws_of_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.simpLaws_of_wf

/-! ## Chains, costs and equal runtimes -/

/-- info: 'RwLog.Span.denO_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Span.denO_chain

/-- info: 'RwLog.Span.chain_isSome_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Span.chain_isSome_iff

/-- info: 'RwLog.Span.chain_isSome_fuse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Span.chain_isSome_fuse

/-- info: 'RwLog.Span.chain_eq_none_of_compose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Span.chain_eq_none_of_compose

/-- info: 'RwLog.Runtime.SameRun.of_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Runtime.SameRun.of_eq

/-- info: 'RwLog.CostedRuntime.spent_mono' depends on axioms: [propext] -/
#guard_msgs in #print axioms RwLog.CostedRuntime.spent_mono

/-- info: 'RwLog.CostedRuntime.spent_of_halts' depends on axioms: [propext] -/
#guard_msgs in #print axioms RwLog.CostedRuntime.spent_of_halts

/-- info: 'RwLog.Cost.mapL_val' depends on axioms: [propext] -/
#guard_msgs in #print axioms RwLog.Cost.mapL_val

/-- info: 'RwLog.R000.unfoldN_call' does not depend on any axioms -/
#guard_msgs in #print axioms RwLog.R000.unfoldN_call

/-- info: 'RwLog.Simulates.of_steps' depends on axioms: [propext] -/
#guard_msgs in #print axioms RwLog.Simulates.of_steps

/-- info: 'RwLog.CostedRuntime.coversWithin_of_halts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.CostedRuntime.coversWithin_of_halts

/-- info: 'RwLog.CostedRuntime.coversUsing_time' does not depend on any axioms -/
#guard_msgs in #print axioms RwLog.CostedRuntime.coversUsing_time

/-- info: 'RwLog.denoteAt_ofPairs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RwLog.denoteAt_ofPairs

/-- info: 'RwLog.Ctx.denAt_fill' depends on axioms: [propext] -/
#guard_msgs in #print axioms RwLog.Ctx.denAt_fill

/-- info: 'RwLog.Ctx.denAt_union' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Ctx.denAt_union

/-- info: 'RwLog.Context.demands_alone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Context.demands_alone

/-- info: 'RwLog.Context.demands_orL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Context.demands_orL

/-- info: 'RwLog.Context.Demands.related' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Context.Demands.related

/-- info: 'RwLog.Context.Demands.related_ofPairs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Context.Demands.related_ofPairs

/-- info: 'RwLog.ProgClass.points_proper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.ProgClass.points_proper

/-- info: 'RwLog.CostedRuntime.le_spent_of_covered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RwLog.CostedRuntime.le_spent_of_covered

/-! ## Lists -/

/-- info: 'RwLog.firsts_eq_eraseDups' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RwLog.firsts_eq_eraseDups

/-- info: 'RwLog.addAll_flatMap_firsts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.addAll_flatMap_firsts

/-! ## Direction: the mirrored machine -/

/-- info: 'RwLog.simulates_of_trace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RwLog.simulates_of_trace

/-- info: 'RwLog.CostBisim.simulates' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RwLog.CostBisim.simulates

/-- info: 'RwLog.DirectionFree.of_bisim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.DirectionFree.of_bisim

/-! ## Goal-directed tables and the hedge -/

/-- info: 'RwLog.gd_normB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.gd_normB

/-- info: 'RwLog.sem_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.sem_norm

/-- info: 'RwLog.Valid.join' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Valid.join

/-- info: 'RwLog.Valid.meet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Valid.meet

/-- info: 'RwLog.Engine.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Engine.sound

/-- info: 'RwLog.Engine.derivationGeneral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Engine.derivationGeneral

/-! ## Answers, whole rungs and fairness -/

/-- info: 'RwLog.Span.covers_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Span.covers_iff

/-- info: 'RwLog.Span.equiv_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Span.equiv_iff

/-- info: 'RwLog.Rung.honestProgress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Rung.honestProgress

/-- info: 'RwLog.Rung.Keeps.of_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Rung.Keeps.of_id

/-- info: 'RwLog.Runtime.FinalMaximal.maximal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Runtime.FinalMaximal.maximal

/-- info: 'RwLog.Alternative.semAt_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Alternative.semAt_subset

/-- info: 'RwLog.Fair.flat_ticks' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Fair.flat_ticks

/-- info: 'RwLog.firstWording_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.firstWording_false
