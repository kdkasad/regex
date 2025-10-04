use std::{
    io::Write,
    process::{Command, Stdio},
};

use env_logger::Env;
use log::{error, info};
use regex::fsa::{Dfa, StateMachine, TransitionCondition};

fn main() {
    env_logger::Builder::from_env(Env::default().default_filter_or("info")).init();

    info!("this program requires your terminal to support the Kitty graphics protocol.");
    info!("this program requires the dot(1) utility to be installed.");

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

    println!("Non-deterministic:");
    if let Err(err) = render(&nfa.visualize()) {
        error!("running dot(1) command: {err}");
    }
    println!("Deterministic:");
    let dfa = Dfa::from(&nfa);
    if let Err(err) = render(&dfa.as_fsa().visualize()) {
        error!("running dot(1) command: {err}");
    }
}

/// Renders a GraphViz graph to the terminal using Kitty graphics protocol
fn render(gv: &str) -> std::io::Result<()> {
    let mut proc = Command::new("dot")
        .arg("-Gdpi=200")
        .arg("-Tkittyz")
        .stdin(Stdio::piped())
        .spawn()?;
    proc.stdin.as_mut().unwrap().write_all(gv.as_bytes())?;
    proc.wait()?;
    Ok(())
}
