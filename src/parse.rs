use std::{error::Error, fmt::Display, iter::Peekable, u32};

use log::debug;

use crate::{
    Regex,
    fsa::{Dfa, StateMachine, TransitionCondition},
};

// LL(1) grammar for our supported regular expressions:
//
// Pattern -> Atom Pattern | ε
//
// Atom -> char | '.' | Group
//
// Group -> '(' Pattern ')'

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
        while let Some(&c) = self.pattern.peek() {
            // Stop if we reached the end of the sub-pattern
            if c == ')' {
                break;
            }
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
        let Some(&c) = self.pattern.peek() else {
            return Err(PatternParseError::ExpectedButFound(None, None));
        };

        if c == '(' {
            return self.parse_group();
        }

        self.pattern.next().unwrap(); // consume peeked character
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

    fn parse_group(&mut self) -> ParseResult {
        let found = self.pattern.next();
        if found != Some('(') {
            return Err(PatternParseError::ExpectedButFound(Some('('), found));
        };
        let fsa = self.parse_pattern()?;
        let found = self.pattern.next();
        if found != Some(')') {
            return Err(PatternParseError::ExpectedButFound(Some(')'), found));
        };
        Ok(fsa)
    }
}

#[derive(Debug, Copy, Clone)]
pub enum PatternParseError {
    /// Expected a character but found either EOF or a different character.
    ///
    /// The first tuple element is the expected character or `None` if any character is expected.
    /// The second tuple element is the found character or `None` if EOF was found.
    ExpectedButFound(Option<char>, Option<char>),
}

impl Display for PatternParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ExpectedButFound(None, None) => {
                write!(f, "expected character, found end of input")
            }
            Self::ExpectedButFound(Some(c), None) => {
                write!(f, "expected '{c}', found end of input")
            }
            Self::ExpectedButFound(Some(expected), Some(found)) => {
                write!(f, "expected '{expected}', found '{found}'")
            }
            Self::ExpectedButFound(None, Some(found)) => {
                write!(f, "found '{found}', expected something else")
            }
        }
    }
}

impl Error for PatternParseError {}
