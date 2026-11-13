import RwLog

/-!
# Axiom audit

Every headline theorem must depend only on Lean's three standard axioms.
`#guard_msgs` makes the build fail if any theorem picks up `sorryAx` or a
new axiom.
-/

/-- info: 'RwLog.sem_eq_derivable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.sem_eq_derivable

/-- info: 'RwLog.R000.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R000.sound

/-- info: 'RwLog.R000.complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R000.complete

/-- info: 'RwLog.R000.honest_exhaustion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R000.honest_exhaustion

/-- info: 'RwLog.R000.terminates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R000.terminates

/-- info: 'RwLog.R000.dual_answers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R000.dual_answers

/-- info: 'RwLog.R000.dual_terminates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R000.dual_terminates

/-- info: 'RwLog.R000.or_comm_answers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R000.or_comm_answers

/-- info: 'RwLog.R000.or_comm_terminates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R000.or_comm_terminates

/-- info: 'RwLog.R000.or_assoc_answers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R000.or_assoc_answers

/-- info: 'RwLog.R000.or_assoc_terminates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R000.or_assoc_terminates

/-- info: 'RwLog.R000.theory_answers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R000.theory_answers

/-- info: 'RwLog.R000.theory_terminates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R000.theory_terminates

/-- info: 'RwLog.R000.terminates_recursionFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R000.terminates_recursionFree

/-- info: 'RwLog.R000.terminates_callTreeFinite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R000.terminates_callTreeFinite

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

/-- info: 'RwLog.R001.covers_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R001.covers_iff

/-- info: 'RwLog.R001.iface_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R001.iface_exact

/-- info: 'RwLog.R001.iface_equiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R001.iface_equiv

/-- info: 'RwLog.R001.denote_dual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R001.denote_dual

/-- info: 'RwLog.R001.boundary_lifting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R001.boundary_lifting

/-- info: 'RwLog.R001.Lifting.toDerives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R001.Lifting.toDerives

/-- info: 'RwLog.R001.Lifting.toGDerives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R001.Lifting.toGDerives

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

/-- info: 'RwLog.R001.theory_mono_answers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R001.theory_mono_answers
/-- info: 'RwLog.R001.refutes_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R001.refutes_sound

/-- info: 'RwLog.R001.simplify_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R001.simplify_exact

/-- info: 'RwLog.R001.simplify_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R001.simplify_stable

/-- info: 'RwLog.R001.simplify_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R001.simplify_mono

/-- info: 'RwLog.R001.present_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R001.present_exact
/-- info: 'RwLog.R001.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R001.sound

/-- info: 'RwLog.R001.complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R001.complete

/-- info: 'RwLog.R001.honest_exhaustion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R001.honest_exhaustion

/-- info: 'RwLog.R001.derivation_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R001.derivation_general

/-- info: 'RwLog.R001.prompt_pruning' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R001.prompt_pruning

/-- info: 'RwLog.R001.no_subsumed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R001.no_subsumed

/-- info: 'RwLog.R001.finite_answers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R001.finite_answers

/-- info: 'RwLog.R001.table_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R001.table_sound

/-- info: 'RwLog.R001.completion_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R001.completion_sound

/-- info: 'RwLog.R001.table_fair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R001.table_fair

/-- info: 'RwLog.R001.gderives_same' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R001.gderives_same
/-- info: 'RwLog.R001.conv_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R001.conv_trace

/-- info: 'RwLog.R001.or_comm_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R001.or_comm_trace

/-- info: 'RwLog.R001.or_assoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R001.or_assoc

/-- info: 'RwLog.R001.terminates_iff_cert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R001.terminates_iff_cert

/-- info: 'RwLog.R001.terminates_finitelyNormalising' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R001.terminates_finitelyNormalising

/-- info: 'RwLog.R001.finite_side_seq_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R001.finite_side_seq_left

/-- info: 'RwLog.R001.finite_side_seq_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R001.finite_side_seq_right

/-- info: 'RwLog.R001.finite_side_and' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R001.finite_side_and

/-- info: 'RwLog.R001.empty_side' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R001.empty_side

/-- info: 'RwLog.R001.tabling_termination' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R001.tabling_termination

/-- info: 'RwLog.R001.addition_fixed_modes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R001.addition_fixed_modes

/-- info: 'RwLog.R001.dual_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R001.dual_trace

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

/-- info: 'RwLog.Program.sem_dual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Program.sem_dual

/-- info: 'RwLog.Runtime.finite_answers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Runtime.finite_answers

/-- info: 'RwLog.Runtime.Tier0Cert.tier0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Runtime.Tier0Cert.tier0

/-- info: 'RwLog.Runtime.derivationGeneral_of_ref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Runtime.derivationGeneral_of_ref

/-- info: 'RwLog.Runtime.theory_mono_answers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Runtime.theory_mono_answers

/-- info: 'RwLog.Runtime.trace_of_sim' depends on axioms: [propext] -/
#guard_msgs in #print axioms RwLog.Runtime.trace_of_sim

/-- info: 'RwLog.Runtime.SameRun.tier0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Runtime.SameRun.tier0

/-- info: 'RwLog.Runtime.SameRun.terminatesOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Runtime.SameRun.terminatesOn

/-- info: 'RwLog.Runtime.HonestExhaustion.transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Runtime.HonestExhaustion.transfer

/-- info: 'RwLog.Rung.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Rung.sound

/-- info: 'RwLog.Rung.pointComplete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Rung.pointComplete

/-- info: 'RwLog.Rung.honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Rung.honest

/-- info: 'RwLog.R000.cert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R000.cert

/-- info: 'RwLog.R001.cert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R001.cert

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

/-- info: 'RwLog.R002.eager_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R002.eager_exact

/-- info: 'RwLog.R002.onDemand_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R002.onDemand_exact

/-- info: 'RwLog.R002.Tabled.machine_runtime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R002.Tabled.machine_runtime

/-- info: 'RwLog.R002.baseline_exact_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R002.baseline_exact_of

/-- info: 'RwLog.R002.runtime_eq_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R002.runtime_eq_of

/-- info: 'RwLog.R002.sound_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R002.sound_of

/-- info: 'RwLog.R002.complete_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R002.complete_of

/-- info: 'RwLog.R002.honest_exhaustion_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R002.honest_exhaustion_of

/-- info: 'RwLog.R002.baseline_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R002.baseline_exact

/-- info: 'RwLog.R002.runtime_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R002.runtime_eq

/-- info: 'RwLog.R002.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R002.sound

/-- info: 'RwLog.R002.complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R002.complete

/-- info: 'RwLog.R002.honest_exhaustion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R002.honest_exhaustion
