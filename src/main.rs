mod lexer;
mod parser;

use std::io::{self, Read};

fn main() {
    let mut input = String::new();

    io::stdin().read_to_string(&mut input).unwrap();

    match parser::parse(&input) {
        Ok(ast) => println!("{ast:?}"),
        Err(e) => println!("{e}"),
    }
}
