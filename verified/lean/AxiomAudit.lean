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
