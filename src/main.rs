#![allow(dead_code)]

use std::io::{self, Write};

pub mod analysis;
pub mod ast;
pub mod codegen;
pub mod lexer;
pub mod new_analysis;
pub mod parser;
pub mod tokens;

fn main() {
    loop {
        let mut input = String::new();
        print!(">>> ");
        io::stdout().flush().unwrap();
        io::stdin().read_line(&mut input).unwrap();
        match lexer::lex_tokens(input) {
            Ok(tokens) => match parser::parse(tokens) {
                Ok(ast) => match new_analysis::typecheck_ast(ast) {
                    Ok(ty_ast) => println!("{:#?}", ty_ast),
                    Err(ty_err) => println!("Type error: {:?}", ty_err)
                },
                Err(parse_err) => println!("Parse error: {:?}", parse_err)
            },
            Err(lex_err) => println!("Lex error: {:?}", lex_err)
        }
    }
    
}
