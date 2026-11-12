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

/-- info: 'RwLog.R001.Symmetry.dual_trace_of_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.R001.Symmetry.dual_trace_of_mono
