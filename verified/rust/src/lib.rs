//! The part of an rwLog engine that is translated to Lean by Aeneas.
//!
//! `store` is the base machine: terms are nodes in a store, and the only
//! things that cost anything are reading a node, allocating a node, and
//! comparing two identifiers or two words. `matching` is written on top of it
//! and can spend ticks only by calling it.

pub mod matching;
pub mod store;
