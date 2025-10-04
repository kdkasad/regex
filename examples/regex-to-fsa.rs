use std::process::ExitCode;

use env_logger::Env;
use regex::Regex;

fn main() -> ExitCode {
    env_logger::Builder::from_env(Env::default().default_filter_or("info")).init();

    let Some(pattern) = std::env::args().nth(1) else {
        println!("Usage: {} <pattern>", std::env::args().nth(0).unwrap());
        return ExitCode::FAILURE;
    };
    let regex = match Regex::new(&pattern) {
        Ok(v) => v,
        Err(err) => {
            eprintln!("Error parsing regex: {}", err);
            return ExitCode::FAILURE;
        }
    };
    let gv = regex.as_fsa().as_fsa().visualize(None);
    println!("{gv}");

    ExitCode::SUCCESS
}
