//! Runtime execution engine for rwlog relations.
//!
//! This module implements a demand-driven, dual-symmetric dataflow evaluator
//! that handles non-ground queries correctly. The architecture follows the
//! design in NEW_DESIGN.md.
//!
//! Key components:
//! - `goal`: Goal struct and compatibility checking
//! - `node`: Node types (Atom, Or, Join, Table, Call)
//! - `scheduler`: Worklist scheduler
//! - `compile`: Rel AST to node graph compilation
//! - `engine`: Public API

pub mod compile;
pub mod engine;
pub mod goal;
pub mod node;
pub mod scheduler;

pub use compile::{compile_program, compile_rel};
pub use engine::{Engine, FuelResult, OutOfFuel};
pub use goal::{canon_goal, goal_matches, Goal};
pub use node::{JoinOp, JoinSide, JoinTask, Node, NodeId, NodeKind, NodeState, StepResult};
pub use scheduler::Runtime;
