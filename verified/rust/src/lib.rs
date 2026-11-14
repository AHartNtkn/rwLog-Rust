//! The part of an rwLog engine that is translated to Lean by Aeneas.
//!
//! `store` is the base machine: terms are nodes in a store, and the only
//! things that cost anything are reading a node, asking for the identifier
//! of a node, comparing two identifiers or two words, and reading or writing
//! a cell of a table. The other modules are written on top of it and can
//! spend ticks only by calling it. They keep no collection of their own:
//! lists are lists of the store.

pub mod cover;
pub mod dom;
pub mod sorts;
pub mod span;
pub mod store;
pub mod term;
