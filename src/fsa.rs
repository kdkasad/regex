use std::{fmt::Write as _, ops::RangeInclusive};

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
/// The state graph is represented using an adjacency list. `adj_list[i]` is a list of possible
/// [transitions][Transition] from state `i` to other states.
#[derive(Debug, Clone)]
pub struct StateMachine {
    /// Adjacency list of state graph
    adj_list: Vec<Vec<Transition>>,
    /// `is_accepting[i]` is `true` iff state `i` is an accepting state
    is_accepting: Vec<bool>, // TODO: replace with bit vector
}

impl Default for StateMachine {
    fn default() -> StateMachine {
        StateMachine {
            adj_list: vec![Vec::new()],
            is_accepting: vec![false],
        }
    }
}

impl StateMachine {
    /// Creates a new [`StateMachine`] with one state. This one state is the starting state,
    /// and there are no accepting states.
    #[must_use]
    #[inline]
    pub fn new() -> StateMachine {
        StateMachine::default()
    }

    /// Returns the set of accepting states.
    ///
    /// This is a slow operation, as it requires iterating over all states.
    #[must_use]
    pub fn accepting_states(&self) -> Vec<State> {
        self.is_accepting
            .iter()
            .copied()
            .enumerate()
            .filter(|&(_, accepting)| accepting)
            .map(|(i, _)| State(i))
            .collect()
    }

    #[must_use]
    #[inline]
    pub fn is_accepting(&self, state: State) -> bool {
        self.is_accepting[state.0]
    }

    /// Marks `state` as either accepting or non-accepting, as determined by `accept`.
    #[inline]
    pub fn set_accepting(&mut self, state: State, accept: bool) {
        self.is_accepting[state.0] = accept;
    }

    /// Clears all accepting states.
    ///
    /// This is a slow operation; prefer calling [`set_accepting(false)`] if you
    /// know the accepting states.
    #[inline]
    pub fn clear_accepting(&mut self) {
        self.is_accepting.fill(false);
    }

    /// Returns the starting state.
    #[must_use]
    #[inline]
    pub const fn start(&self) -> State {
        State(0)
    }

    /// Adds a new unconnected state to the machine.
    /// Returns the index of the new state.
    #[inline]
    pub fn add_state(&mut self) -> State {
        let new = self.adj_list.len();
        self.adj_list.push(Vec::new());
        self.is_accepting.push(false);
        State(new)
    }

    /// Links the given states by creating a [`Transition`] between them.
    #[inline]
    pub fn link(&mut self, from: State, to: State, condition: TransitionCondition) {
        self.adj_list[from.0].push(Transition { condition, to });
    }

    /// Embeds a given [`StateMachine`] into this state machine by copying all of its
    /// states and transitions, adjusting indices accordingly. Returns a tuple containing the
    /// states corresponding to the fragment's starting and accepting states, respectively.
    pub fn embed(&mut self, mut sub: StateMachine) -> (State, Vec<State>) {
        let n = self.adj_list.len();
        for mut edge_list in std::mem::take(&mut sub.adj_list) {
            for transition in &mut edge_list {
                transition.to.0 += n;
            }
            self.adj_list.push(edge_list);
            self.is_accepting.push(false);
        }
        let start = State(sub.start().0 + n);
        let mut accept_set = sub.accepting_states();
        for state in &mut accept_set {
            state.0 += n;
        }
        (start, accept_set)
    }

    /// Returns a [GraphViz format][1] representation of the FSA graph.
    ///
    /// This operation takes `O(n + m)` time, where `n` is the number of states and `m` is the
    /// number of transitions.
    ///
    /// [1]: https://www.graphviz.org/about/
    #[must_use]
    pub fn visualize<'a>(&self, title: impl Into<Option<&'a str>>) -> String {
        let mut s = String::new();
        s.push_str("strict digraph FSA {\n");
        if let Some(title) = title.into() {
            writeln!(&mut s, "label=\"{title}\"").unwrap();
        }
        s.push_str("graph[rankdir=LR]\n");
        s.push_str("node[shape=circle]\n");
        s.push_str("start_state [shape=point; style=invis]\n");
        for i in 0..self.adj_list.len() {
            write!(&mut s, "s{i}").unwrap();
            if self.is_accepting[i] {
                s.push_str(" [shape=doublecircle]");
            }
            s.push('\n');
        }
        writeln!(&mut s, "start_state -> s{}", self.start().0).unwrap();
        for (src, transitions) in self.adj_list.iter().enumerate() {
            for transition in transitions {
                write!(&mut s, "s{} -> s{} [label=\"", src, transition.to.0).unwrap();
                Self::write_graphviz_label(&mut s, &transition.condition);
                writeln!(&mut s, "\"]").unwrap();
            }
        }
        s.push('}');
        s
    }

    /// Writes text representing the given [`TransitionCondition`] to the string, for use in the
    /// `label` graphviz attribute.
    fn write_graphviz_label(s: &mut String, condition: &TransitionCondition) {
        match condition {
            TransitionCondition::InRange(start, end) => {
                write!(s, "{start}").unwrap();
                if let Some(start_char) = char::from_u32(*start)
                    && start_char.is_ascii_graphic()
                {
                    let esc = if start_char == '"' { "/" } else { "" };
                    write!(s, " ('{esc}{start_char}')").unwrap();
                }
                write!(s, " - {end}").unwrap();
                if let Some(end_char) = char::from_u32(*end)
                    && end_char.is_ascii_graphic()
                {
                    let esc = if end_char == '"' { "/" } else { "" };
                    write!(s, " ('{esc}{end_char}')").unwrap();
                }
            }
            TransitionCondition::None => {
                write!(s, "ε").unwrap();
            }
        }
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

impl Dfa {
    /// Returns a reference to the underlying [`StateMachine`].
    #[must_use]
    #[inline]
    pub fn as_fsa(&self) -> &StateMachine {
        &self.0
    }

    #[must_use]
    pub fn advance(&self, cur_state: State, input: char) -> Option<State> {
        let outgoing_edges = &self.0.adj_list[cur_state.0];
        for edge in outgoing_edges {
            match edge.condition {
                TransitionCondition::InRange(start, end) => {
                    if start <= input as u32 && input as u32 <= end {
                        return Some(edge.to);
                    }
                }
                TransitionCondition::None => {
                    unreachable!("A DFA must not have epsilon-labeled edges")
                }
            }
        }
        None
    }
}

mod nfa2dfa {
    use std::{
        collections::{BTreeSet, HashMap},
        rc::Rc,
    };

    use log::trace;

    use crate::fsa::Transition;

    use super::{Dfa, State, StateMachine, TransitionCondition};

    type StateSet = BTreeSet<State>;

    impl From<&StateMachine> for Dfa {
        /// Converts a possibly non-deterministic [`StateMachine`] into a deterministic one.
        fn from(nfa: &StateMachine) -> Dfa {
            // New automaton which will be a DFA
            let mut dfa = StateMachine::new();
            // Mapping from a set of states in the input NFA to a state in the output DFA
            let mut set_to_state: HashMap<Rc<StateSet>, State> = HashMap::new();
            // Stack of NFA state sets that have an associated state in the DFA but have not yet
            // been connected
            let mut stack: Vec<Rc<StateSet>> = Vec::new();
            let mut marked_states: BTreeSet<Rc<StateSet>> = BTreeSet::new();

            // Add start state set to stack
            let start_state_set = Rc::new(epsilon_closure(nfa, &StateSet::from([nfa.start()])));
            let start_state = dfa.start();
            set_to_state.insert(Rc::clone(&start_state_set), start_state);
            stack.push(start_state_set);

            // while there are states in the stack
            while let Some(set) = stack.pop() {
                trace!("popped {set:?}");
                // skip marked ones
                if marked_states.contains(&set) {
                    trace!("skipping {set:?}");
                    continue;
                }
                // mark this state set
                marked_states.insert(Rc::clone(&set));

                // find each non-epsilon outgoing transition from this state set
                let outgoing: Vec<((u32, u32), State)> = set
                    .iter()
                    .copied()
                    .flat_map(|state| nfa.adj_list[state.0].iter())
                    .filter_map(|transition| {
                        if let TransitionCondition::InRange(start, end) = transition.condition {
                            Some(((start, end), transition.to))
                        } else {
                            None
                        }
                    })
                    .collect();
                trace!("found outgoing transitions: {outgoing:#?}");

                // make outgoing transitions disjoint
                let disjoint = disjoint_transitions(&outgoing);
                trace!("condensed outgoing transitions: {outgoing:#?}");

                // add disjoint transitions to the DFA, pushing new states onto the stack for
                // processing
                let src = *set_to_state
                    .get(&set)
                    .expect("source state set has no DFA state mapped");
                for (range, dst_set) in disjoint {
                    let closed = epsilon_closure(nfa, &dst_set);
                    trace!("closed {dst_set:?} into {closed:?}");
                    let dst_set = Rc::new(closed);
                    // Get DFA state corresponding to dst_set if exists, or create a new one if
                    // not.
                    let dst = *set_to_state.entry(Rc::clone(&dst_set)).or_insert_with(|| {
                        let new = dfa.add_state();
                        trace!("adding mapping {dst_set:?} -> {}", new.0);
                        new
                    });
                    trace!("found {dst_set:?} -> {}", dst.0);

                    // Create a transition from src to dst in the DFA
                    dfa.adj_list[src.0].push(Transition {
                        condition: TransitionCondition::InRange(range.0, range.1),
                        to: dst,
                    });
                    trace!(
                        "adding transition {} -> {} via ({}, {})",
                        src.0, dst.0, range.0, range.1
                    );
                    // Add the destination set to the stack to be processed
                    trace!("pushing to stack: {dst_set:?}");
                    stack.push(dst_set);
                }
            }

            // Mark NFA state sets which contain accepting states as accepting in the DFA
            for (set, state) in &set_to_state {
                if set.iter().any(|&nfa_state| nfa.is_accepting[nfa_state.0]) {
                    dfa.is_accepting[state.0] = true;
                }
            }

            trace!("final set -> state mapping: {set_to_state:#?}");
            Dfa(dfa)
        }
    }

    /// Computes _ε-closure(`src`)_ on `nfa`, i.e. the set of states reachable from `src` by traversing
    /// only edges with [`TransitionCondition::None`].
    fn epsilon_closure(nfa: &StateMachine, src: &StateSet) -> StateSet {
        let mut result: StateSet = src.clone();
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
    /// # fn set(it: impl IntoIterator<Item = u32>) -> BTreeSet<u32> { it.into_iter().collect() }
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
    ) -> Vec<((u32, u32), BTreeSet<State>)> {
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

        let mut result: Vec<((u32, u32), BTreeSet<State>)> = Vec::new();
        let mut last_start: Option<u32> = None;
        let mut states: BTreeSet<State> = BTreeSet::new();
        let mut depth = 0;
        for (pos, event, state) in events {
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
        use std::collections::BTreeSet;

        use super::epsilon_closure;
        use crate::fsa::{State, StateMachine, Transition, TransitionCondition};

        fn set<I>(it: I) -> BTreeSet<State>
        where
            I: IntoIterator<Item = usize>,
        {
            it.into_iter().map(State).collect()
        }

        #[test]
        fn test_epsilon_closure_no_op() {
            let fsa = StateMachine::new();
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
                is_accepting: vec![false, true],
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
                is_accepting: vec![false, false, true],
            };
            let actual = epsilon_closure(&fsa, &set([0]));
            assert_eq!(set([0, 1, 2, 3]), actual);
        }

        #[test]
        fn test_disjoint_transitions() {
            // -----
            //    -----
            let input = vec![((0, 5), State(0)), ((3, 10), State(1))];
            let expected: Vec<((u32, u32), BTreeSet<State>)> = vec![
                ((0, 2), set([0])),
                ((3, 5), set([0, 1])),
                ((6, 10), set([1])),
            ];
            let actual = super::disjoint_transitions(&input);
            assert_eq!(expected, actual);

            // -----
            //     .
            let input = vec![((0, 5), State(0)), ((5, 5), State(1))];
            let expected: Vec<((u32, u32), BTreeSet<State>)> =
                vec![((0, 4), set([0])), ((5, 5), set([0, 1]))];
            let actual = super::disjoint_transitions(&input);
            assert_eq!(expected, actual);

            // -----
            //   .
            let input = vec![((0, 5), State(0)), ((3, 3), State(1))];
            let expected: Vec<((u32, u32), BTreeSet<State>)> = vec![
                ((0, 2), set([0])),
                ((3, 3), set([0, 1])),
                ((4, 5), set([0])),
            ];
            let actual = super::disjoint_transitions(&input);
            assert_eq!(expected, actual);

            // ---
            //    ---
            let input = vec![((0, 5), State(0)), ((5, 10), State(1))];
            let expected: Vec<((u32, u32), BTreeSet<State>)> = vec![
                ((0, 4), set([0])),
                ((5, 5), set([0, 1])),
                ((6, 10), set([1])),
            ];
            let actual = super::disjoint_transitions(&input);
            assert_eq!(expected, actual);

            // ------
            // ---
            let input = vec![((0, 5), State(0)), ((0, 2), State(1))];
            let expected: Vec<((u32, u32), BTreeSet<State>)> =
                vec![((0, 2), set([0, 1])), ((3, 5), set([0]))];
            let actual = super::disjoint_transitions(&input);
            assert_eq!(expected, actual);

            // ------  ------
            //    ---
            let input = vec![((0, 5), State(0)), ((3, 5), State(1)), ((7, 10), State(2))];
            let expected: Vec<((u32, u32), BTreeSet<State>)> = vec![
                ((0, 2), set([0])),
                ((3, 5), set([0, 1])),
                ((7, 10), set([2])),
            ];
            let actual = super::disjoint_transitions(&input);
            assert_eq!(expected, actual);

            // ------  ------
            //     ------
            let input = vec![((0, 5), State(0)), ((3, 7), State(1)), ((6, 10), State(2))];
            let expected: Vec<((u32, u32), BTreeSet<State>)> = vec![
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
