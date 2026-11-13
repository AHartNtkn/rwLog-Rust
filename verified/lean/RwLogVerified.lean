/-
# Rust code of the engine, translated by Aeneas and proved against the specification

* `RwlogCore` (generated, not edited): `verified/rust/src` as Lean functions.
* `RwLogVerified.Digits`, `RwLogVerified.TrieModel`: the keys of nodes and the
  trie that finds a node by its key, as a list.
* `RwLogVerified.Store`: the invariant of the Rust store; each primitive
  keeps it, does what it says, and costs one tick.

Every theorem says the Rust function does not panic, returns the
specification's result, and advances the store's tick counter by at most a
stated amount.
-/
import RwLogVerified.Digits
import RwLogVerified.TrieModel
import RwLogVerified.Store
