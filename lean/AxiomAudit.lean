import RwLog

/-!
# Axiom audit

Every headline theorem must depend only on Lean's three standard axioms.
`#guard_msgs` makes the build fail if any theorem picks up `sorryAx` or a
new axiom.
-/

/-- info: 'RwLog.sem_eq_derivable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.sem_eq_derivable

/-! ## Shared kernel and rung framework -/

/-- info: 'RwLog.Span.covers?_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Span.covers?_iff

/-- info: 'RwLog.ProgramOf.sem_dual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.ProgramOf.sem_dual

/-- info: 'RwLog.Runtime.finite_answers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Runtime.finite_answers

/-- info: 'RwLog.Runtime.Tier0Cert.tier0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Runtime.Tier0Cert.tier0

/-- info: 'RwLog.Runtime.derivationGeneral_of_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Runtime.derivationGeneral_of_refines

/-- info: 'RwLog.Runtime.trace_of_sim' depends on axioms: [propext] -/
#guard_msgs in #print axioms RwLog.Runtime.trace_of_sim

/-- info: 'RwLog.Runtime.SameRun.tier0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Runtime.SameRun.tier0

/-- info: 'RwLog.Runtime.SameRun.terminatesOn' depends on axioms: [propext] -/
#guard_msgs in #print axioms RwLog.Runtime.SameRun.terminatesOn

/-- info: 'RwLog.Runtime.HonestExhaustion.transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Runtime.HonestExhaustion.transfer

/-- info: 'RwLog.Rung.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Rung.sound

/-- info: 'RwLog.Rung.pointComplete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Rung.pointComplete

/-- info: 'RwLog.Rung.honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Rung.honest


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

/-- info: 'RwLog.normal_normB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.normal_normB

/-- info: 'RwLog.Normal.norm_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Normal.norm_eq

/-- info: 'RwLog.normB_normB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.normB_normB

/-- info: 'RwLog.Normal.view_members' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Normal.view_members

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

/-! ## The constraint domain -/

/-- info: 'RwLog.Sorts.wellFormed_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Sorts.wellFormed_nil

/-- info: 'RwLog.Kernel.std_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Kernel.std_refines

/-- info: 'RwLog.Domain.Lawful.denO_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Domain.Lawful.denO_inj

/-- info: 'RwLog.Domain.Lawful.swap_swap' depends on axioms: [propext] -/
#guard_msgs in #print axioms RwLog.Domain.Lawful.swap_swap

/-- info: 'RwLog.Domain.Lawful.rep_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Domain.Lawful.rep_swap

/-- info: 'RwLog.Domain.Lawful.compose_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Domain.Lawful.compose_swap

/-- info: 'RwLog.Domain.Lawful.meet_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Domain.Lawful.meet_swap

/-- info: 'RwLog.Domain.Lawful.swap_of_isBound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Domain.Lawful.swap_of_isBound

/-- info: 'RwLog.Domain.Lawful.covers_swap' depends on axioms: [propext] -/
#guard_msgs in #print axioms RwLog.Domain.Lawful.covers_swap

/-- info: 'RwLog.Domain.Lawful.compose_assoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Domain.Lawful.compose_assoc

/-- info: 'RwLog.Domain.Lawful.meet_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Domain.Lawful.meet_comm

/-- info: 'RwLog.Domain.Lawful.meet_assoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Domain.Lawful.meet_assoc

/-- info: 'RwLog.Domain.Lawful.meet_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Domain.Lawful.meet_self

/-- info: 'RwLog.Domain.Lawful.covers_antisymm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Domain.Lawful.covers_antisymm

/-- info: 'RwLog.Valid.swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Valid.swap

/-- info: 'RwLog.Valid.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Valid.sound

/-! ## The constraint domain of sorts -/

/-- info: 'RwLog.Sorts.Raw.Normal.eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Sorts.Raw.Normal.eq

/-- info: 'RwLog.Sorts.Prob.normal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Sorts.Prob.normal

/-- info: 'RwLog.Sorts.dom_lawful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Sorts.dom_lawful

/-- info: 'RwLog.Sorts.Rep.no_hidden' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Sorts.Rep.no_hidden

/-- info: 'RwLog.Sorts.Raw.toSpan_den' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Sorts.Raw.toSpan_den

/-- info: 'RwLog.Sorts.wellFormed_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Sorts.wellFormed_iff

/-- info: 'RwLog.Sorts.count_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Sorts.count_none

/-- info: 'RwLog.Sorts.count_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Sorts.count_one

/-- info: 'RwLog.Sorts.count_many' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Sorts.count_many

/-- info: 'RwLog.Sorts.count_many_infinite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Sorts.count_many_infinite

/-- info: 'RwLog.Sorts.inclBut_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Sorts.inclBut_iff

/-- info: 'RwLog.Sorts.sole_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Sorts.sole_sound

/-- info: 'RwLog.Sorts.sole_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Sorts.sole_none

/-- info: 'RwLog.Sorts.unitOn_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Sorts.unitOn_iff

/-- info: 'RwLog.Sorts.expStore_den' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.Sorts.expStore_den

/-- info: 'RwLog.ProgramOf.check_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLog.ProgramOf.check_iff
