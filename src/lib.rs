#![warn(clippy::pedantic)]

use crate::{
    fsa::StateMachine,
    parse::{Parser, PatternParseError},
};

mod fsa;
mod parse;

#[derive(Debug, Clone)]
pub struct Regex {
    fsa: StateMachine,
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
}

#[cfg(test)]
mod tests {}
