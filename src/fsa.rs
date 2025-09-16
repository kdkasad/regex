use std::ops::RangeInclusive;

/// Newtype wrapper around a state index
///
/// Used to guarantee validity of states used as inputs to functions without having to perform
/// runtime bounds checks. Since a [`State`] can only be constructed from within this module, any
/// consumers will only be able to hold states with valid indices, **as long as they are used in
/// the same machine they were returned from**.
#[derive(Debug, Copy, Clone)]
#[repr(transparent)]
pub struct State(usize);

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
            edge_list
                .iter_mut()
                .for_each(|transition| transition.to.0 += n);
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
    condition: TransitionCondition,
    /// Index of the state this transition leads to
    to: State,
}

/// A condition that must be satisfied for a [`Transition`] to be taken.
#[derive(Debug, Copy, Clone)]
pub enum TransitionCondition {
    /// No condition; always satisfied
    None,
    /// The next character must be between these two characters, inclusive
    InRange(char, char),
}

impl TransitionCondition {
    /// Returns `true` if the given condition is satisfied by the input character `c`, or `false`
    /// otherwise.
    pub fn test(&self, c: char) -> bool {
        match self {
            TransitionCondition::None => true,
            TransitionCondition::InRange(x, y) => *x <= c && c <= *y,
        }
    }
}

impl From<RangeInclusive<char>> for TransitionCondition {
    fn from(value: RangeInclusive<char>) -> Self {
        TransitionCondition::InRange(*value.start(), *value.end())
    }
}

impl From<char> for TransitionCondition {
    fn from(value: char) -> Self {
        TransitionCondition::InRange(value, value)
    }
}
