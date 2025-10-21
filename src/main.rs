mod eval;
mod lexer;
mod parser;

use eval::Environment;
use std::io::{self, Write};

fn run<'a>() -> Result<(), io::Error> {
    let args = std::env::args().collect::<Vec<_>>();
    let mut env = Environment::default();

    if args.len() == 2 {
        let input = std::fs::read_to_string(&args[1])?;
        match env.eval(&input) {
            Ok(ast) => println!("{ast}"),
            Err(e) => println!("{e}"),
        }
    } else if args.len() == 1 {
        let (stdin, mut stdout) = (io::stdin(), io::stdout());
        loop {
            print!("> ");
            stdout.flush()?;

            let mut input = String::new();
            if stdin.read_line(&mut input)? == 0 {
                // Quit if we receive EOF
                println!();
                break;
            }

            // Leak the input string in order to extend its lifetime
            match env.eval(input.leak()) {
                Ok(ast) => println!("{ast}"),
                Err(e) => println!("{e}"),
            }
        }
    } else {
        println!("Provide at most 1 argument.")
    }

    Ok(())
}

fn main() {
    if let Err(e) = run() {
        println!("{e}");
    }
}
