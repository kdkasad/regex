#![warn(clippy::pedantic)]

use crate::{
    fsa::{Dfa, StateMachine},
    parse::Parser,
};

pub mod fsa;
pub mod parse;

pub use parse::PatternParseError;

#[derive(Debug, Clone)]
pub struct Regex {
    dfa: Dfa,
}

impl Regex {
    /// Creates a [`Regex`] which matches the given pattern.
    ///
    /// # Errors
    ///
    /// Returns [`PatternParseError`] if there is an error parsing the pattern.
    pub fn new(pattern: &str) -> Result<Regex, PatternParseError> {
        Parser::new(pattern.chars()).parse()
    }

    /// Returns a reference to the [`Dfa`] representing this regular expression.
    #[must_use]
    pub fn as_fsa(&self) -> &Dfa {
        &self.dfa
    }

    #[must_use]
    pub fn matches(&self, input: &str) -> bool {
        let fsa = self.dfa.as_fsa();
        let mut chars = input.chars();
        let mut cur_state = fsa.start();
        while let Some(c) = chars.next() {
            if fsa.is_accepting(cur_state) {
                return true;
            }

            let next_state = self.dfa.advance(cur_state, c);
            match next_state {
                Some(next_state) => cur_state = next_state,
                None => return false,
            }
        }
        fsa.is_accepting(cur_state)
    }
}

#[cfg(test)]
mod tests {}
