use std::ops::RangeInclusive;

/// Newtype wrapper around a state index
///
/// Used to guarantee validity of states used as inputs to functions without having to perform
/// runtime bounds checks. Since a [`State`] can only be constructed from within this module, any
/// consumers will only be able to hold states with valid indices, **as long as they are used in
/// the same machine they were returned from**.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct State(usize);

impl From<State> for usize {
    fn from(value: State) -> Self {
        value.0
    }
}

/// Finite state automaton
///
/// # Internal representation
///
/// The state graph is represented using an adjacency list. `transitions[i]` is a list of possible
/// [transitions][Transition] from state `i` to other states.
#[derive(Debug, Clone)]
pub struct StateMachine {
    adj_list: Vec<Vec<Transition>>,
    /// Starting state.
    pub start: State,
    /// Accepting state.
    pub accept: State,
}

impl StateMachine {
    /// Creates a new [`StateMachine`] with one state. This one state is both the starting and
    /// accepting state.
    pub fn new() -> StateMachine {
        StateMachine {
            adj_list: vec![Vec::new()],
            start: State(0),
            accept: State(0),
        }
    }

    /// Adds a new unconnected state to the machine.
    /// Returns the index of the new state.
    pub fn add_state(&mut self) -> State {
        let new = self.adj_list.len();
        self.adj_list.push(Vec::new());
        State(new)
    }

    /// Links the given states by creating a [`Transition`] between them.
    pub fn link(&mut self, from: State, to: State, condition: TransitionCondition) {
        self.adj_list[from.0].push(Transition { condition, to });
    }

    /// Embeds a given [`StateMachine`] into this state machine by copying all of its
    /// states and transitions, adjusting indices accordingly. Returns a tuple containing the
    /// states corresponding to the fragment's starting and accepting states, respectively.
    pub fn embed(&mut self, sub: StateMachine) -> (State, State) {
        let n = self.adj_list.len();
        for mut edge_list in sub.adj_list {
            for transition in &mut edge_list {
                transition.to.0 += n;
            }
            self.adj_list.push(edge_list);
        }
        let start = State(sub.start.0 + n);
        let accept = State(sub.accept.0 + n);
        (start, accept)
    }
}

/// Describes a state transition in a [`StateMachine`].
#[derive(Debug, Copy, Clone)]
pub struct Transition {
    /// Condition the next input character must satisfy to take this transition
    pub condition: TransitionCondition,
    /// Index of the state this transition leads to
    pub to: State,
}

/// A condition that must be satisfied for a [`Transition`] to be taken.
#[derive(Debug, Copy, Clone)]
pub enum TransitionCondition {
    /// No condition; always satisfied
    None,
    /// The next character must be between these two characters, inclusive
    InRange(u32, u32),
}

impl TransitionCondition {
    /// Returns `true` if the given condition is satisfied by the input character `c`, or `false`
    /// otherwise.
    pub fn test(self, c: char) -> bool {
        let c = c as u32;
        match self {
            TransitionCondition::None => true,
            TransitionCondition::InRange(x, y) => x <= c && c <= y,
        }
    }
}

impl From<RangeInclusive<char>> for TransitionCondition {
    fn from(value: RangeInclusive<char>) -> Self {
        TransitionCondition::InRange(*value.start() as u32, *value.end() as u32)
    }
}

impl From<char> for TransitionCondition {
    fn from(value: char) -> Self {
        TransitionCondition::InRange(value as u32, value as u32)
    }
}

/// Deterministic finite automaton
///
/// This is a wrapper type around [`StateMachine`] that can only be constructed by converting
/// a possibly non-deterministic [`StateMachine`] to a deterministic one using [`DFA::from()`].
#[derive(Debug, Clone)]
pub struct Dfa(StateMachine);

mod nfa2dfa {
    use std::collections::HashSet;

    use super::{Dfa, State, StateMachine, TransitionCondition};

    impl From<&StateMachine> for Dfa {
        /// Converts a possibly non-deterministic [`StateMachine`] into a deterministic one.
        fn from(nfa: &StateMachine) -> Dfa {
            todo!()
        }
    }

    /// Computes _ε-closure(`src`)_ on `nfa`, i.e. the set of states reachable from `src` by traversing
    /// only edges with [`TransitionCondition::None`].
    pub fn epsilon_closure(nfa: &StateMachine, src: &HashSet<State>) -> HashSet<State> {
        let mut result: HashSet<State> = src.clone();
        let mut stack: Vec<State> = Vec::new();
        for s in src {
            stack.push(*s);
        }
        while let Some(s) = stack.pop() {
            let transitions_from_s = &nfa.adj_list[usize::from(s)];
            for t in transitions_from_s {
                if let TransitionCondition::None = t.condition {
                    let next = t.to;
                    result.insert(next);
                    stack.push(next);
                }
            }
        }
        result
    }

    /// Splits a list of possibly overlapping ranges into a list of disjoint ranges.
    ///
    /// The input is a mapping (as a list of tuples) from ranges to states. These represent
    /// transitions that can be taken if an input character is in the given range.
    ///
    /// The output is a similar mapping (as a list of tuples) from ranges to sets of states.
    /// Instead of having multiple transitions with overlapping ranges, all output transitions have
    /// disjoint ranges, but may have multiple destination states.
    ///
    /// # Example
    ///
    /// E.g. an input might be:
    /// ```ignore
    /// # // test ignored because State is private
    /// let input = vec![
    ///     ( (10, 50), State(2) ),
    ///     ( (20, 70), State(4) ),
    /// ];
    /// ```
    /// This means there are two possible transitions, one to state 2 and one to state 4, each with
    /// the condition that the next input character must be in the given range. However, this is
    /// non-deterministic, since if we have a character in the range 20–50, we can take both
    /// transitions.
    ///
    /// This function would produce the following output:
    /// ```ignore
    /// # // test ignored because State is private
    /// # use regex::fsa::State;
    /// # let input = vec![
    /// #     ( (10, 50), State(2) ),
    /// #     ( (20, 70), State(4) ),
    /// # ];
    /// # fn set(it: impl IntoIterator<Item = u32>) -> HashSet<u32> { it.into_iter().collect() }
    /// let output = vec![
    ///     ( (10, 19), set([State(2)]) ),
    ///     ( (20, 50), set([State(2), State(4)]) ),
    ///     ( (51, 70), set([State(4)]) ),
    /// ];
    /// assert_eq!(output, disjoint_transitions(&input));
    /// ```
    /// As we can see, the overlapping transitions in the input are transformed into
    /// non-overlapping transitions in the output, with the proper set of possible states derived
    /// from the overlapping transitions.
    fn disjoint_transitions(
        transitions: &[((u32, u32), State)],
    ) -> Vec<((u32, u32), HashSet<State>)> {
        #[derive(Debug, Clone, Copy, PartialOrd, Ord, PartialEq, Eq)]
        enum Event {
            Start = 0,
            End = 1,
        }

        // Convert ranges into a single list of start/end events
        let mut events: Vec<(u32, Event, State)> = Vec::new();
        for &((start, end), state) in transitions {
            events.push((start, Event::Start, state));
            events.push((end, Event::End, state));
        }
        // Sort the list so we now have all events in order
        events.sort_unstable();

        let mut result: Vec<((u32, u32), HashSet<State>)> = Vec::new();
        let mut last_start: Option<u32> = None;
        let mut states: HashSet<State> = HashSet::new();
        let mut depth = 0;
        for (pos, event, state) in events {
            dbg!((pos, event));
            dbg!(depth);
            dbg!(last_start);
            match (event, last_start) {
                (Event::Start, None) => {
                    last_start = Some(pos);
                    states.insert(state);
                    depth += 1;
                }
                (Event::Start, Some(start)) => {
                    if start < pos {
                        // Emit a range that ends right before the current position.
                        result.push(((start, pos - 1), states.clone()));
                    }
                    states.insert(state);
                    last_start = Some(pos);
                    depth += 1;
                }
                (Event::End, Some(start)) => {
                    // Since start events will come before end events for the same position, we
                    // will only hit this branch if there is no range that starts from this
                    // position as well.
                    if start <= pos {
                        // Don't end a range that hasn't started yet
                        result.push(((start, pos), states.clone()));
                    }
                    states.remove(&state);
                    depth -= 1;
                    if depth > 0 {
                        last_start = Some(pos + 1);
                    } else {
                        last_start = None;
                    }
                }
                (Event::End, None) => panic!("found end with no currently-open range"),
            }
        }
        result
    }

    #[cfg(test)]
    mod tests {
        use std::collections::{BTreeSet, HashSet};

        use super::epsilon_closure;
        use crate::fsa::{State, StateMachine, Transition, TransitionCondition};

        fn set<I>(it: I) -> HashSet<State>
        where
            I: IntoIterator<Item = usize>,
        {
            it.into_iter().map(State).collect()
        }

        #[test]
        fn test_epsilon_closure_no_op() {
            let fsa = StateMachine {
                adj_list: vec![vec![]],
                start: State(0),
                accept: State(0),
            };
            let actual = epsilon_closure(&fsa, &set([0]));
            assert_eq!(set([0]), actual);
        }

        #[test]
        fn test_epsilon_closure_single_jump() {
            let fsa = StateMachine {
                adj_list: vec![
                    vec![Transition {
                        condition: TransitionCondition::None,
                        to: State(1),
                    }],
                    vec![],
                ],
                start: State(0),
                accept: State(1),
            };
            let actual = epsilon_closure(&fsa, &set([0]));
            assert_eq!(set([0, 1]), actual);
        }

        #[test]
        fn test_epsilon_closure_several_jumps() {
            let fsa = StateMachine {
                adj_list: vec![
                    vec![
                        Transition {
                            condition: TransitionCondition::None,
                            to: State(1),
                        },
                        Transition {
                            condition: TransitionCondition::None,
                            to: State(3),
                        },
                    ],
                    vec![Transition {
                        condition: TransitionCondition::None,
                        to: State(2),
                    }],
                    vec![],
                    vec![],
                ],
                start: State(0),
                accept: State(2),
            };
            let actual = epsilon_closure(&fsa, &set([0]));
            assert_eq!(set([0, 1, 2, 3]), actual);
        }

        #[test]
        fn test_disjoint_transitions() {
            // -----
            //    -----
            let input = vec![((0, 5), State(0)), ((3, 10), State(1))];
            let expected: Vec<((u32, u32), HashSet<State>)> = vec![
                ((0, 2), set([0])),
                ((3, 5), set([0, 1])),
                ((6, 10), set([1])),
            ];
            let actual = super::disjoint_transitions(&input);
            assert_eq!(expected, actual);

            // -----
            //     .
            let input = vec![((0, 5), State(0)), ((5, 5), State(1))];
            let expected: Vec<((u32, u32), HashSet<State>)> =
                vec![((0, 4), set([0])), ((5, 5), set([0, 1]))];
            let actual = super::disjoint_transitions(&input);
            assert_eq!(expected, actual);

            // -----
            //   .
            let input = vec![((0, 5), State(0)), ((3, 3), State(1))];
            let expected: Vec<((u32, u32), HashSet<State>)> = vec![
                ((0, 2), set([0])),
                ((3, 3), set([0, 1])),
                ((4, 5), set([0])),
            ];
            let actual = super::disjoint_transitions(&input);
            assert_eq!(expected, actual);

            // ---
            //    ---
            let input = vec![((0, 5), State(0)), ((5, 10), State(1))];
            let expected: Vec<((u32, u32), HashSet<State>)> = vec![
                ((0, 4), set([0])),
                ((5, 5), set([0, 1])),
                ((6, 10), set([1])),
            ];
            let actual = super::disjoint_transitions(&input);
            assert_eq!(expected, actual);

            // ------
            // ---
            let input = vec![((0, 5), State(0)), ((0, 2), State(1))];
            let expected: Vec<((u32, u32), HashSet<State>)> =
                vec![((0, 2), set([0, 1])), ((3, 5), set([0]))];
            let actual = super::disjoint_transitions(&input);
            assert_eq!(expected, actual);

            // ------  ------
            //    ---
            let input = vec![((0, 5), State(0)), ((3, 5), State(1)), ((7, 10), State(2))];
            let expected: Vec<((u32, u32), HashSet<State>)> = vec![
                ((0, 2), set([0])),
                ((3, 5), set([0, 1])),
                ((7, 10), set([2])),
            ];
            let actual = super::disjoint_transitions(&input);
            assert_eq!(expected, actual);

            // ------  ------
            //     ------
            let input = vec![((0, 5), State(0)), ((3, 7), State(1)), ((6, 10), State(2))];
            let expected: Vec<((u32, u32), HashSet<State>)> = vec![
                ((0, 2), set([0])),
                ((3, 5), set([0, 1])),
                ((6, 7), set([1, 2])),
                ((8, 10), set([2])),
            ];
            let actual = super::disjoint_transitions(&input);
            assert_eq!(expected, actual);
        }
    }
}
