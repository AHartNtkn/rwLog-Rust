//! Input parsing for CLI commands.
//!
//! Supports parsing simple relational queries and definitions.

use std::fmt;

/// Commands that can be entered in the REPL.
#[derive(Debug, Clone, PartialEq)]
pub enum Command {
    /// Define a new relation: def name(args) = body
    Define { name: String, body: String },
    /// Query a relation: ?- goal
    Query { goal: String },
    /// Load a file: load "filename"
    Load { filename: String },
    /// Show help: help
    Help,
    /// Exit the REPL: quit
    Quit,
    /// List defined relations: list
    List,
    /// Empty input
    Empty,
}

/// Parse errors.
#[derive(Debug, Clone, PartialEq)]
pub enum ParseError {
    /// Unexpected end of input.
    UnexpectedEof,
    /// Unexpected character.
    UnexpectedChar(char),
    /// Invalid command.
    InvalidCommand(String),
    /// Missing argument.
    MissingArgument(String),
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParseError::UnexpectedEof => write!(f, "Unexpected end of input"),
            ParseError::UnexpectedChar(c) => write!(f, "Unexpected character: '{}'", c),
            ParseError::InvalidCommand(cmd) => write!(f, "Invalid command: '{}'", cmd),
            ParseError::MissingArgument(arg) => write!(f, "Missing argument: {}", arg),
        }
    }
}

impl std::error::Error for ParseError {}

/// Parser for CLI input.
pub struct Parser {
    input: Vec<char>,
    pos: usize,
}

impl Parser {
    /// Create a new parser for the given input.
    pub fn new(input: &str) -> Self {
        Self {
            input: input.chars().collect(),
            pos: 0,
        }
    }

    /// Parse the input into a command.
    pub fn parse(&mut self) -> Result<Command, ParseError> {
        self.skip_whitespace();

        if self.is_at_end() {
            return Ok(Command::Empty);
        }

        // Check for query prefix
        if self.peek() == Some('?') {
            self.advance();
            if self.peek() == Some('-') {
                self.advance();
                self.skip_whitespace();
                let goal = self.parse_until_end();
                if goal.is_empty() {
                    return Err(ParseError::MissingArgument("query goal".to_string()));
                }
                return Ok(Command::Query { goal });
            }
            return Err(ParseError::UnexpectedChar(self.peek().unwrap_or('?')));
        }

        // Parse keyword command
        let keyword = self.parse_identifier();
        self.skip_whitespace();

        match keyword.as_str() {
            "def" | "define" => {
                let rest = self.parse_until_end();
                if rest.is_empty() {
                    return Err(ParseError::MissingArgument("definition body".to_string()));
                }
                // Parse name from rest
                let parts: Vec<&str> = rest.splitn(2, '=').collect();
                if parts.len() < 2 {
                    return Err(ParseError::MissingArgument("definition body after '='".to_string()));
                }
                let name = parts[0].trim().to_string();
                let body = parts[1].trim().to_string();
                Ok(Command::Define { name, body })
            }
            "load" => {
                let filename = self.parse_string_or_word()?;
                if filename.is_empty() {
                    return Err(ParseError::MissingArgument("filename".to_string()));
                }
                Ok(Command::Load { filename })
            }
            "help" | "h" | "?" => Ok(Command::Help),
            "quit" | "exit" | "q" => Ok(Command::Quit),
            "list" | "ls" => Ok(Command::List),
            _ => {
                // Could be a query without the ?- prefix
                if keyword.is_empty() {
                    Ok(Command::Empty)
                } else {
                    Err(ParseError::InvalidCommand(keyword))
                }
            }
        }
    }

    fn is_at_end(&self) -> bool {
        self.pos >= self.input.len()
    }

    fn peek(&self) -> Option<char> {
        self.input.get(self.pos).copied()
    }

    fn advance(&mut self) -> Option<char> {
        let c = self.peek();
        if c.is_some() {
            self.pos += 1;
        }
        c
    }

    fn skip_whitespace(&mut self) {
        while let Some(c) = self.peek() {
            if c.is_whitespace() {
                self.advance();
            } else {
                break;
            }
        }
    }

    fn parse_identifier(&mut self) -> String {
        let mut result = String::new();
        while let Some(c) = self.peek() {
            if c.is_alphanumeric() || c == '_' {
                result.push(c);
                self.advance();
            } else {
                break;
            }
        }
        result
    }

    fn parse_filename(&mut self) -> String {
        let mut result = String::new();
        while let Some(c) = self.peek() {
            if c.is_alphanumeric() || c == '_' || c == '.' || c == '/' || c == '-' {
                result.push(c);
                self.advance();
            } else {
                break;
            }
        }
        result
    }

    fn parse_until_end(&mut self) -> String {
        let result: String = self.input[self.pos..].iter().collect();
        self.pos = self.input.len();
        result.trim().to_string()
    }

    fn parse_string_or_word(&mut self) -> Result<String, ParseError> {
        self.skip_whitespace();

        if self.is_at_end() {
            return Ok(String::new());
        }

        if self.peek() == Some('"') {
            self.advance(); // Skip opening quote
            let mut result = String::new();
            while let Some(c) = self.advance() {
                if c == '"' {
                    return Ok(result);
                }
                result.push(c);
            }
            Err(ParseError::UnexpectedEof)
        } else {
            Ok(self.parse_filename())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ========== EMPTY INPUT TESTS ==========

    #[test]
    fn parse_empty_input() {
        let mut parser = Parser::new("");
        let cmd = parser.parse().unwrap();
        assert_eq!(cmd, Command::Empty);
    }

    #[test]
    fn parse_whitespace_only() {
        let mut parser = Parser::new("   \t\n  ");
        let cmd = parser.parse().unwrap();
        assert_eq!(cmd, Command::Empty);
    }

    // ========== QUERY TESTS ==========

    #[test]
    fn parse_query() {
        let mut parser = Parser::new("?- parent(tom, X)");
        let cmd = parser.parse().unwrap();
        assert_eq!(
            cmd,
            Command::Query {
                goal: "parent(tom, X)".to_string()
            }
        );
    }

    #[test]
    fn parse_query_with_whitespace() {
        let mut parser = Parser::new("  ?-   test(X, Y)  ");
        let cmd = parser.parse().unwrap();
        assert_eq!(
            cmd,
            Command::Query {
                goal: "test(X, Y)".to_string()
            }
        );
    }

    #[test]
    fn parse_query_missing_goal() {
        let mut parser = Parser::new("?-");
        let result = parser.parse();
        assert!(matches!(result, Err(ParseError::MissingArgument(_))));
    }

    // ========== DEFINE TESTS ==========

    #[test]
    fn parse_define() {
        let mut parser = Parser::new("def parent(X, Y) = rule_body");
        let cmd = parser.parse().unwrap();
        assert_eq!(
            cmd,
            Command::Define {
                name: "parent(X, Y)".to_string(),
                body: "rule_body".to_string()
            }
        );
    }

    #[test]
    fn parse_define_keyword() {
        let mut parser = Parser::new("define foo = bar");
        let cmd = parser.parse().unwrap();
        assert_eq!(
            cmd,
            Command::Define {
                name: "foo".to_string(),
                body: "bar".to_string()
            }
        );
    }

    #[test]
    fn parse_define_missing_body() {
        let mut parser = Parser::new("def test");
        let result = parser.parse();
        assert!(matches!(result, Err(ParseError::MissingArgument(_))));
    }

    // ========== LOAD TESTS ==========

    #[test]
    fn parse_load_quoted() {
        let mut parser = Parser::new("load \"test.rwl\"");
        let cmd = parser.parse().unwrap();
        assert_eq!(
            cmd,
            Command::Load {
                filename: "test.rwl".to_string()
            }
        );
    }

    #[test]
    fn parse_load_unquoted() {
        let mut parser = Parser::new("load testfile");
        let cmd = parser.parse().unwrap();
        assert_eq!(
            cmd,
            Command::Load {
                filename: "testfile".to_string()
            }
        );
    }

    #[test]
    fn parse_load_missing_filename() {
        let mut parser = Parser::new("load");
        let result = parser.parse();
        assert!(matches!(result, Err(ParseError::MissingArgument(_))));
    }

    // ========== HELP TESTS ==========

    #[test]
    fn parse_help() {
        let mut parser = Parser::new("help");
        let cmd = parser.parse().unwrap();
        assert_eq!(cmd, Command::Help);
    }

    #[test]
    fn parse_help_short() {
        let mut parser = Parser::new("h");
        let cmd = parser.parse().unwrap();
        assert_eq!(cmd, Command::Help);
    }

    #[test]
    fn parse_help_question() {
        let mut parser = Parser::new("?");
        let result = parser.parse();
        // '?' alone is not a valid query (needs ?-)
        assert!(result.is_err());
    }

    // ========== QUIT TESTS ==========

    #[test]
    fn parse_quit() {
        let mut parser = Parser::new("quit");
        let cmd = parser.parse().unwrap();
        assert_eq!(cmd, Command::Quit);
    }

    #[test]
    fn parse_exit() {
        let mut parser = Parser::new("exit");
        let cmd = parser.parse().unwrap();
        assert_eq!(cmd, Command::Quit);
    }

    #[test]
    fn parse_q() {
        let mut parser = Parser::new("q");
        let cmd = parser.parse().unwrap();
        assert_eq!(cmd, Command::Quit);
    }

    // ========== LIST TESTS ==========

    #[test]
    fn parse_list() {
        let mut parser = Parser::new("list");
        let cmd = parser.parse().unwrap();
        assert_eq!(cmd, Command::List);
    }

    #[test]
    fn parse_ls() {
        let mut parser = Parser::new("ls");
        let cmd = parser.parse().unwrap();
        assert_eq!(cmd, Command::List);
    }

    // ========== ERROR TESTS ==========

    #[test]
    fn parse_invalid_command() {
        let mut parser = Parser::new("foobar");
        let result = parser.parse();
        assert!(matches!(result, Err(ParseError::InvalidCommand(_))));
    }

    #[test]
    fn parse_incomplete_query_prefix() {
        let mut parser = Parser::new("?x");
        let result = parser.parse();
        assert!(matches!(result, Err(ParseError::UnexpectedChar(_))));
    }

    // ========== PARSE ERROR DISPLAY TESTS ==========

    #[test]
    fn parse_error_display_unexpected_eof() {
        let err = ParseError::UnexpectedEof;
        assert_eq!(err.to_string(), "Unexpected end of input");
    }

    #[test]
    fn parse_error_display_unexpected_char() {
        let err = ParseError::UnexpectedChar('x');
        assert_eq!(err.to_string(), "Unexpected character: 'x'");
    }

    #[test]
    fn parse_error_display_invalid_command() {
        let err = ParseError::InvalidCommand("foo".to_string());
        assert_eq!(err.to_string(), "Invalid command: 'foo'");
    }

    #[test]
    fn parse_error_display_missing_argument() {
        let err = ParseError::MissingArgument("filename".to_string());
        assert_eq!(err.to_string(), "Missing argument: filename");
    }
}
