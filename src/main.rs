#![allow(unused, unreachable_code)]

mod interpreter;
mod lex;
use lex::Lexer;
pub mod parse;

use clap::Parser;
use derive_more::derive::From;
use parse::{Atom, TokenTree};
use std::fs;
use std::path::PathBuf;

type Result<T> = std::result::Result<T, Error>;

fn main() -> Result<()> {
    let args = Args::parse();
    let command = args.command;

    let mut err = false;

    match command {
        Command::Tokenize { path } => {
            let file_contents = fs::read_to_string(&path)?;
            for token in Lexer::new(&file_contents) {
                match token {
                    Ok(x) => println!("{x}"),
                    Err(e) => {
                        err = true;
                        eprintln!("{e}");
                    }
                }
            }
            println!("EOF  null")
        }
        Command::Parse { path } => {
            let file_contents = fs::read_to_string(&path)?;
            // We should print a token tree here

            let mut parser = parse::Parser::new(&file_contents);

            loop {
                match parser.parse() {
                    Ok(TokenTree::Atom(Atom::Nil)) => break,
                    Ok(tt) => println!("{tt}"),
                    Err(e) => {
                       eprintln!("Error when parsing: {e}");
                        std::process::exit(65)
                    }
                }
            }
        }
        // TODO: Run should have an interpreter that lazely interprets the AST.
        // Dont mix the parsing and the interpretation.
        // Parse statement by statement and construct the results, maybe the interpreter holds
        // The state necesary for the program to function. like variables, functions etc
        Command::Run { path } => {
            let file_contents = fs::read_to_string(&path)?;

            let mut interpreter = interpreter::Interpreter::new(&file_contents);
            if let Err(errors) = interpreter.run_program() {
                for error in errors {
                    eprintln!("Error from interpreter: {error}");
                }
                std::process::exit(65);
            }
        }
    }

    if err {
        std::process::exit(65);
    }

    Ok(())
}

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    /// Command to apply to a given file
    #[command(subcommand)]
    command: Command,
}

#[derive(Debug, Clone, Parser)]
#[command(long_about = None)]
enum Command {
    /// Takes a file and tokenizes into an iterator of tokens.
    Tokenize {
        /// Path of the file to run command on
        path: PathBuf,
    },
    /// Takes a `PathBuf` and tokenizes and parse the input into a `TokenTree`.
    Parse {
        path: PathBuf,
    },
    Run {
        path: PathBuf,
    },
}

#[derive(Debug, From)]
enum Error {
    Lexer(lex::Error),
    Parser(parse::Error),
    Io(std::io::Error),
}

impl std::error::Error for Error {}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Lexer(e) => write!(f, "{e:?}"),
            Error::Io(e) => write!(f, "{e:?}"),
            Error::Parser(e) => write!(f, "{e:?}"),
        }
    }
}

fn line_error(line: usize) -> String {
    format!("[Line {line}] ")
}
