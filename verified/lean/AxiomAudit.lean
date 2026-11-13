import RwLogVerified

/-!
# Axiom audit

Every headline theorem must depend only on Lean's three standard axioms.
`#guard_msgs` makes the build fail if any theorem picks up `sorryAx` or a
new axiom.
-/

/-- info: 'RwLogVerified.term_eq_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.term_eq_spec

/-- info: 'RwLogVerified.match_into_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.match_into_spec

/-- info: 'RwLogVerified.match_into_empty_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.match_into_empty_spec

/-- info: 'RwLogVerified.instantiate_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.instantiate_spec

/-- info: 'RwLogVerified.alloc_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.alloc_spec

/-- info: 'RwLogVerified.read_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.read_spec

/-- info: 'RwLogVerified.same_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.same_spec

/-- info: 'RwLogVerified.word_eq_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.word_eq_spec

/-- info: 'RwLogVerified.lookup_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RwLogVerified.lookup_spec
