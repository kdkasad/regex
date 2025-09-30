#![warn(clippy::pedantic)]

use crate::{
    fsa::Dfa,
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
mod tests {
    macro_rules! gen_tests {
        [ $($name:ident: $pattern:literal $op:tt $input:literal),+ $(,)? ] => {
            $( gen_tests! { single; $name: $pattern $op $input } )+
        };

        (single; $name:ident: $pattern:literal = $input:literal) => {
            ::paste::paste! {
                #[test]
                fn [< test_matches_ $name >]() {
                    let regex = super::Regex::new($pattern).unwrap();
                    assert!(regex.matches($input));
                }
            }
        };

        (single; $name:ident: $pattern:literal != $input:literal) => {
            ::paste::paste! {
                #[test]
                fn [< test_matches_ $name >]() {
                    let regex = super::Regex::new($pattern).unwrap();
                    assert!(!regex.matches($input));
                }
            }
        };
    }

    // <pattern> = <input> means the pattern matches the input
    // <pattern> != <input> means the pattern does not match the input
    gen_tests![
        literal1: "a" = "a",
        literal2: "abc" = "abc",
        literal_ne1: "a" != "b",
        literal_ne2: "abc" != "cba",
        dot1: "." = "a",
        dot2: "." = "b",
        dot3: "..." = "abc",
        dot4: "..." = "def",
        dot5: "a.b" = "a_b",
        group1: "(a)" = "a",
        group2: "(a)b" = "ab",
        group3: "(abc)(.(ef))" = "abcdef",
    ];
}
