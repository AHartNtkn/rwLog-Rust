/-
# Rust code of the engine, translated by Aeneas and proved against the specification

* `RwlogCore` (generated, not edited): `verified/rust/src` as Lean functions.
* `RwLogVerified.Digits`, `RwLogVerified.TrieModel`: the keys of nodes and the
  trie that finds a node by its key, as a list.
* `RwLogVerified.Store`: the invariant of the Rust store; each primitive
  keeps it, does what it says, and costs one tick.
* `RwLogVerified.Repr`: an identifier stands for a specification term.
* `RwLogVerified.Walk`: what the frames on the stack of a loop over a term
  stand for.
* `RwLogVerified.Rebuild`, `Occurs`: applying a binding to a term and the
  occurs check, each once per distinct subterm.
* `RwLogVerified.SolveCost`, `Solve`: the unifier `solve_into` returns what
  `RwLog.Eqns.solveOn` returns, within the number of variables times the distinct subterms and equations.
* `RwLogVerified.SpanSpec`, `Compose`: `compose` and `meet` of spans.
* `RwLogVerified.Chain`: the test that a chain of spans composes.
* `RwLogVerified.MatchSpec`, `Cover`: one-way matching, coverage when the
  covering span has no constraints, and equality of spans.
* `RwLogVerified.Iface`: the interfaces of a span as boundaries.
* `RwLogVerified.Kernel`: the kernel rung whose charges are those bounds.
* `RwLogVerified.KernelRuns`: its charges on a worked composition.

Every theorem says the Rust function does not panic, returns the
specification's result, and advances the store's tick counter by at most a
stated amount.
-/
import RwLogVerified.Digits
import RwLogVerified.TrieModel
import RwLogVerified.Store
import RwLogVerified.Repr
import RwLogVerified.Walk
import RwLogVerified.Rebuild
import RwLogVerified.Occurs
import RwLogVerified.SolveCost
import RwLogVerified.Solve
import RwLogVerified.SpanSpec
import RwLogVerified.Compose
import RwLogVerified.Chain
import RwLogVerified.MatchSpec
import RwLogVerified.Cover
import RwLogVerified.Iface
import RwLogVerified.Kernel
import RwLogVerified.KernelRuns
