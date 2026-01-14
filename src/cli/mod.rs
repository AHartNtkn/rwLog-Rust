//! CLI module for rwlog.
//!
//! Provides a REPL interface and command parsing for the logic engine.

pub mod compiler;
pub mod file_parser;
pub mod parse;
pub mod repl;

pub use compiler::{CompileError, Compiler};
pub use file_parser::{FileParseError, FileParser, ParsedExpr, ParsedFile, ParsedTerm, RelationDef};
pub use parse::{Command, ParseError, Parser};
pub use repl::Repl;
