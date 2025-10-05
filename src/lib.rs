#![warn(clippy::pedantic)]

use crate::{fsa::Dfa, parse::Parser};

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
            match self.dfa.advance(cur_state, c) {
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
                    assert!(regex.matches($input), "Expected pattern '{}' to match input '{}'", $pattern, $input);
                }
            }
        };

        (single; $name:ident: $pattern:literal != $input:literal) => {
            ::paste::paste! {
                #[test]
                fn [< test_matches_ $name >]() {
                    let regex = super::Regex::new($pattern).unwrap();
                    assert!(!regex.matches($input), "Expected pattern '{}' to not match input '{}'", $pattern, $input);
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
        or1: "a|b" = "a",
        or2: "a|b" = "b",
        or3: "a|b" != "c",
        or4: "ab|cd" = "ab",
        or5: "ab|cd" != "acd",
        or_group1: "a|(cd)" = "a",
        or_group2: "a|(cd)" = "cd",
        optional1: "a?" = "",
        optional2: "a?" = "a",
        optional3: "a(bc|yz)?" = "abc",
        optional4: "a(bc|yz)?def" = "adef",
        optional5: "a(bc|yz)?def" = "ayzdef",
        kleene1: "ab*c" = "ac",
        kleene2: "ab*c" = "abc",
        kleene3: "ab*c" = "abbbbbbbc",
        kleene4: "ab*c" != "bbbbbbc",
        plus1: "ab+c" != "ac",
        plus2: "ab+c" = "abc",
        plus3: "ab+c" = "abbbbbbbc",
        plus4: "ab+c" != "bbbbbbc",
        kleene_group1: "a(xyz)*c" = "axyzxyzc",
        kleene_group2: "a(xyz)*c" = "ac",
        plus_group1: "a(xyz)+c" = "axyzxyzc",
        plus_group2: "a(xyz)+c" != "ac",
        emoji1: "(😄|😁)+" = "😁😁😄😁",
        emoji2: "(😄|😁)+" != "😢",
        charset1: "[a]" = "a",
        charset2: "[abc]" = "b",
        charset3: "_[abc]+_" = "_abcbcabcbacbacbabc_",
        charset4: "_[abc]+_" != "_abcbcabcbazbacbabc_",
        charset5: "_[a-z]+_" = "_aklkdsafmacisurlskc_",
        charset6: "_[a-z]+_" != "_aklkds0fmacisurlskc_",
        whole_string: "abc" != "xabcy",
    ];
}
