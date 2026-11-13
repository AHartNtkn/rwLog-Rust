/-
# Rust code of the engine, translated by Aeneas and proved against the specification

* `RwlogCore` (generated, not edited): `verified/rust/src` as Lean functions.
* `RwLogVerified.Store`: each primitive of the Rust store costs one tick.
* `RwLogVerified.Repr`: what a store identifier stands for.
* `RwLogVerified.Matching`: term equality and substitution lookup.
* `RwLogVerified.MatchInto`: the Rust `match_into` computes `RwLog.matchInto`.
* `RwLogVerified.Instantiate`: the Rust `instantiate` computes `Term.bind`.

Every theorem says the Rust function does not panic, returns the
specification's result, and advances the store's tick counter by at most a
stated amount.
-/
import RwLogVerified.Store
import RwLogVerified.Repr
import RwLogVerified.Matching
import RwLogVerified.MatchInto
import RwLogVerified.Instantiate
