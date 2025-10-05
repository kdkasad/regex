use std::{error::Error, fmt::Display, iter::Peekable, u32};

use crate::{
    Regex,
    fsa::{Dfa, StateMachine, TransitionCondition},
};

// LL(1) grammar for our supported regular expressions:
//
// Pattern -> Alternation Pattern | ε
//
// Alternation -> String | String '|' Pattern
//
// String -> QuantifiedAtom | QuantifiedAtom String
//
// QuantifiedAtom -> Atom OptionalQuantifier
//
// OptionalQuantifier -> ε | '?' | '*' | '+'
//
// Atom -> char | '.' | Group
//
// Group -> '(' Pattern ')'
//
// char is any single character other than the following:
// ( ) | . ? * +

pub struct Parser<I: Iterator<Item = char>> {
    pattern: Peekable<I>,
}

type ParseResult = Result<StateMachine, PatternParseError>;
type OptionalParseResult = Result<Option<StateMachine>, PatternParseError>;

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
        while let Some(sub) = self.parse_alternation()? {
            // Parse next construct and embed fragment
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

    /// Parses the `Alternation` non-terminal in the grammar.
    fn parse_alternation(&mut self) -> OptionalParseResult {
        let Some(left) = self.parse_string()? else {
            return Ok(None);
        };
        if let Some('|') = self.pattern.peek() {
            self.pattern.next().unwrap(); // consume '|'
            let right = self.parse_pattern()?;
            let mut fsa = StateMachine::new();
            let (left_start, left_accept) = fsa.embed(left);
            let (right_start, right_accept) = fsa.embed(right);
            fsa.link(fsa.start(), left_start, TransitionCondition::None);
            fsa.link(fsa.start(), right_start, TransitionCondition::None);
            for state in left_accept {
                fsa.set_accepting(state, true);
            }
            for state in right_accept {
                fsa.set_accepting(state, true);
            }
            Ok(Some(fsa))
        } else {
            Ok(Some(left))
        }
    }

    /// Parses the `String` non-terminal in the grammar.
    ///
    /// Replaces recursion with iteration.
    fn parse_string(&mut self) -> OptionalParseResult {
        let Some(mut fsa) = self.parse_quantified_atom()? else {
            return Ok(None);
        };
        while let Some(next) = self.parse_quantified_atom()? {
            let (next_start, next_accept) = fsa.embed(next);
            for state in fsa.accepting_states().clone() {
                fsa.link(state, next_start, TransitionCondition::None);
            }
            fsa.clear_accepting();
            for state in next_accept {
                fsa.set_accepting(state, true);
            }
        }
        Ok(Some(fsa))
    }

    /// Parses the `QuantifiedAtom` non-terminal in the grammar.
    fn parse_quantified_atom(&mut self) -> OptionalParseResult {
        let Some(mut atom) = self.parse_atom()? else {
            return Ok(None);
        };

        match self.pattern.peek() {
            None => (),
            Some('?') => {
                self.pattern.next().unwrap();
                atom.set_accepting(atom.start(), true);
            }
            Some('*') => {
                self.pattern.next().unwrap();
                // Edge from end to start to allow repetition
                for state in atom.accepting_states().clone() {
                    atom.link(state, atom.start(), TransitionCondition::None);
                }
                // Accept start state to allow empty string
                atom.set_accepting(atom.start(), true);
            }
            Some('+') => {
                self.pattern.next().unwrap();
                // Edge from end to start to allow repetition
                for state in atom.accepting_states().clone() {
                    atom.link(state, atom.start(), TransitionCondition::None);
                }
            }
            _ => (),
        }

        Ok(Some(atom))
    }

    /// Parses the `Atom` non-terminal in the grammar.
    fn parse_atom(&mut self) -> OptionalParseResult {
        let c = match self.pattern.peek() {
            // End of input
            None => return Ok(None),
            // Special characters that don't start an atom
            Some('|' | ')' | '?') => return Ok(None),
            Some(c) => *c,
        };

        // Attempt to parse a group
        if let Some(group) = self.parse_group()? {
            return Ok(Some(group));
        }

        // Parse a literal character or wildcard
        self.pattern.next().unwrap(); // consume peeked character
        let mut fsa = StateMachine::new();
        let next = fsa.add_state();
        let condition = match c {
            '.' => TransitionCondition::InRange(u32::MIN, u32::MAX),
            c => TransitionCondition::from(c),
        };
        fsa.link(fsa.start(), next, condition);
        fsa.set_accepting(next, true);
        Ok(Some(fsa))
    }

    fn parse_group(&mut self) -> OptionalParseResult {
        if self.pattern.peek().copied() != Some('(') {
            return Ok(None);
        };
        self.pattern.next(); // consume '('
        let fsa = self.parse_pattern()?;
        let found = self.pattern.next();
        if found != Some(')') {
            return Err(PatternParseError::ExpectedButFound(Some(')'), found));
        };
        Ok(Some(fsa))
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
