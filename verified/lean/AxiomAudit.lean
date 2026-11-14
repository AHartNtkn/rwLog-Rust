import RwLogVerified

/-!
# Axiom audit

Every headline theorem must depend only on Lean's three standard axioms.
`#guard_msgs` makes the build fail if any theorem picks up `sorryAx` or a
new axiom.
-/

/-- info: 'RwLogVerified.new_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.new_spec

/-- info: 'RwLogVerified.alloc_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.alloc_spec

/-- info: 'RwLogVerified.read_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.read_spec

/-- info: 'RwLogVerified.same_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.same_spec

/-- info: 'RwLogVerified.get_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.get_spec

/-- info: 'RwLogVerified.set_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.set_spec

/-- info: 'RwLogVerified.get_flag_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.get_flag_spec

/-- info: 'RwLogVerified.set_flag_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.set_flag_spec

/-- info: 'RwLogVerified.clear_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.clear_spec

/-- info: 'RwLogVerified.push_w' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.push_w

/-- info: 'RwLogVerified.pop_w' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.pop_w

/-- info: 'RwLogVerified.drop_stack_w' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.drop_stack_w

/-- info: 'RwLogVerified.rebuild_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.rebuild_spec

/-- info: 'RwLogVerified.occurs_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.occurs_spec

/-- info: 'RwLogVerified.act_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.act_spec

/-- info: 'RwLogVerified.solve_into_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.solve_into_spec

/-- info: 'RwLogVerified.compose_bridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.compose_bridge

/-- info: 'RwLogVerified.meet_bridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.meet_bridge

/-- info: 'RwLogVerified.rename_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.rename_spec

/-- info: 'RwLogVerified.unstack_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.unstack_spec

/-- info: 'RwLogVerified.append_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.append_spec

/-- info: 'RwLogVerified.compose_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.compose_spec

/-- info: 'RwLogVerified.meet_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.meet_spec

/-- info: 'RwLogVerified.composable_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.composable_spec

/-- info: 'RwLogVerified.mmatch_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.mmatch_spec

/-- info: 'RwLogVerified.covers_plain_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.covers_plain_spec

/-- info: 'RwLogVerified.span_eq_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.span_eq_spec

/-- info: 'RwLogVerified.mark_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.mark_spec

/-- info: 'RwLogVerified.all_marked_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.all_marked_spec

/-- info: 'RwLogVerified.keep_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.keep_spec

/-- info: 'RwLogVerified.iface_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.iface_spec

/-- info: 'RwLogVerified.right_bound_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.right_bound_spec

/-- info: 'RwLogVerified.left_bound_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.left_bound_spec

/-- info: 'RwLogVerified.rustKernel_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.rustKernel_refines

/-- info: 'RwLogVerified.compose_realised' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.compose_realised

/-- info: 'RwLogVerified.meet_realised' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.meet_realised

/-- info: 'RwLogVerified.composable_realised' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.composable_realised

/-- info: 'RwLogVerified.eq_realised' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.eq_realised

/-- info: 'RwLogVerified.covers_realised' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.covers_realised

/-- info: 'RwLogVerified.rightBound_realised' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.rightBound_realised

/-- info: 'RwLogVerified.leftBound_realised' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.leftBound_realised

/-- info: 'RwLogVerified.spine_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.spine_spec

/-- info: 'RwLogVerified.same_len_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.same_len_spec

/-- info: 'RwLogVerified.find_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.find_spec

/-- info: 'RwLogVerified.lookup_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.lookup_spec

/-- info: 'RwLogVerified.fill_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.fill_spec

/-- info: 'RwLogVerified.step_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.step_spec

/-- info: 'RwLogVerified.push_args_loop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.push_args_loop_spec

/-- info: 'RwLogVerified.member_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.member_spec

/-- info: 'RwLogVerified.conj_of_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.conj_of_spec

/-- info: 'RwLogVerified.conj_meet_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.conj_meet_spec

/-- info: 'RwLogVerified.step_conj_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.step_conj_spec

/-- info: 'RwLogVerified.step_conj_conj_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.step_conj_conj_spec

/-- info: 'RwLogVerified.names_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.names_spec

/-- info: 'RwLogVerified.mem_namesList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.mem_namesList

/-- info: 'RwLogVerified.nodup_namesList' depends on axioms: [propext] -/
#guard_msgs in #print axioms RwLogVerified.nodup_namesList

/-- info: 'RwLogVerified.live_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.live_spec

/-- info: 'RwLogVerified.count_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.count_spec

/-- info: 'RwLogVerified.out_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.out_spec

/-- info: 'RwLogVerified.included_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.included_spec

/-- info: 'RwLogVerified.included_but_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.included_but_spec

/-- info: 'RwLogVerified.push_sort_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.push_sort_spec

/-- info: 'RwLogVerified.sole_root_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.sole_root_spec

/-- info: 'RwLogVerified.unit_on_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.unit_on_spec

/-- info: 'RwLogVerified.gone_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.gone_spec

/-- info: 'RwLogVerified.var_succ_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.var_succ_spec

/-- info: 'RwLogVerified.settle_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.settle_spec

/-- info: 'RwLogVerified.settle_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.settle_link

/-- info: 'RwLogVerified.open_var_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.open_var_spec

/-- info: 'RwLogVerified.rev_onto_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.rev_onto_spec

/-- info: 'RwLogVerified.always_on_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.always_on_spec

/-- info: 'RwLogVerified.any_always_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.any_always_spec

/-- info: 'RwLogVerified.first_sole_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.first_sole_spec

/-- info: 'RwLogVerified.tightRun_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.tightRun_total

/-- info: 'RwLogVerified.tighten_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.tighten_spec

/-- info: 'RwLogVerified.tighten_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.tighten_sound

/-- info: 'RwLogVerified.firsts_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.firsts_spec

/-- info: 'RwLogVerified.conj_at_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.conj_at_spec

/-- info: 'RwLogVerified.uppers_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.uppers_spec

/-- info: 'RwLogVerified.renumber_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.renumber_spec

/-- info: 'RwLogVerified.places_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.places_spec

/-- info: 'RwLogVerified.orient_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.orient_spec

/-- info: 'RwLogVerified.push_all_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.push_all_spec

/-- info: 'RwLogVerified.ups_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.ups_spec

/-- info: 'RwLogVerified.close_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.close_spec

/-- info: 'RwLogVerified.norm_ex_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.norm_ex_spec

/-- info: 'RwLogVerified.ofTight_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.ofTight_abs
