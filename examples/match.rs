use env_logger::Env;
use regex::Regex;

fn main() {
    env_logger::Builder::from_env(Env::default().default_filter_or("info")).init();

    let mut args = std::env::args();
    let progname = args.next().unwrap();
    let (Some(pattern), Some(input)) = (args.next(), args.next()) else {
        println!("Usage: {progname} <pattern> <input>");
        return;
    };

    let regex = match Regex::new(&pattern) {
        Ok(v) => v,
        Err(err) => {
            eprintln!("Invalid pattern: {err}");
            return;
        }
    };

    let matches = regex.matches(&input);
    println!("{matches:?}");
}
