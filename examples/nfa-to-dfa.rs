use env_logger::Env;
use regex::fsa::{Dfa, StateMachine, TransitionCondition};

fn main() {
    env_logger::Builder::from_env(Env::default().default_filter_or("info")).init();

    let mut nfa = StateMachine::new();
    let s0 = nfa.start();
    let s1 = nfa.add_state();
    let s2 = nfa.add_state();
    let s3 = nfa.add_state();
    let s4 = nfa.add_state();
    let s5 = nfa.add_state();
    nfa.link(s0, s1, TransitionCondition::None);
    nfa.link(s1, s4, TransitionCondition::InRange('a' as u32, 'f' as u32));
    nfa.link(s4, s5, TransitionCondition::InRange('a' as u32, 'z' as u32));
    nfa.link(s0, s2, TransitionCondition::InRange('a' as u32, 'z' as u32));
    nfa.link(s2, s3, TransitionCondition::InRange('0' as u32, '9' as u32));
    nfa.link(s3, s5, TransitionCondition::None);
    nfa.set_accepting(s5, true);

    let dfa = Dfa::from(&nfa);

    println!("{}", nfa.visualize("Non-deterministic"));
    println!("{}", dfa.as_fsa().visualize("Deterministic"));
}
