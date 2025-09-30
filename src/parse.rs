use std::{fmt::Display, iter::Peekable, u32};

use log::debug;

use crate::{
    Regex,
    fsa::{Dfa, StateMachine, TransitionCondition},
};

// LL(1) grammar for our supported regular expressions:
//
// Pattern -> Atom Pattern | ε
//
// Atom -> char | .

pub struct Parser<I: Iterator<Item = char>> {
    pattern: Peekable<I>,
}

type ParseResult = Result<StateMachine, PatternParseError>;

impl<I: Iterator<Item = char>> Parser<I> {
    pub fn new(chars: I) -> Self {
        Parser {
            pattern: chars.peekable(),
        }
    }

    /// Parses a regular expression pattern
    ///
    /// # Errors
    ///
    /// Returns a [`PatternParseError`] if the given pattern is invalid.
    pub fn parse(mut self) -> Result<Regex, PatternParseError> {
        let fsa = self.parse_pattern()?;
        debug!("Parsed pattern to NFA: {}", fsa.visualize());
        Ok(Regex {
            dfa: Dfa::from(&fsa),
        })
    }

    /// Parses the `Pattern` non-terminal in the grammar.
    ///
    /// For efficiency, recursion is replaced with iteration in this implementation.
    fn parse_pattern(&mut self) -> ParseResult {
        let mut fsa = StateMachine::new();
        fsa.set_accepting(fsa.start(), true);
        while self.pattern.peek().is_some() {
            // Parse atom and embed fragment
            let sub = self.parse_atom()?;
            let (sub_start, sub_accept) = fsa.embed(sub);
            for &state in &fsa.accepting_states().clone() {
                fsa.link(state, sub_start, TransitionCondition::None);
            }
            fsa.clear_accepting();
            for &state in &sub_accept {
                fsa.set_accepting(state, true);
            }
        }
        Ok(fsa)
    }

    /// Parses the `Atom` non-terminal in the grammar.
    fn parse_atom(&mut self) -> ParseResult {
        let Some(c) = self.pattern.next() else {
            return Err(PatternParseError::ExpectedCharFoundEOF(None));
        };

        let mut fsa = StateMachine::new();
        let next = fsa.add_state();
        let condition = match c {
            '.' => TransitionCondition::InRange(u32::MIN, u32::MAX),
            c => TransitionCondition::from(c),
        };
        fsa.link(fsa.start(), next, condition);
        fsa.set_accepting(next, true);
        Ok(fsa)
    }
}

#[derive(Debug, Copy, Clone)]
pub enum PatternParseError {
    ExpectedCharFoundEOF(Option<char>),
}

impl Display for PatternParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ExpectedCharFoundEOF(None) => write!(f, "expected character, found end of input"),
            Self::ExpectedCharFoundEOF(Some(c)) => write!(f, "expected '{c}', found end of input"),
        }
    }
}
