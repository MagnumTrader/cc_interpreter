// TODO: Implement runtime Errors
// TODO: Implement Exit codes for the programs error types
// TODO: implement better interface for getting variables
use std::collections::HashMap;

use crate::parse::{self, Atom, Op, Parser, TokenTree};

/// Takes a parser and interprets each statement
/// Can we take all definitions first?
#[derive(Debug)]
pub struct Interpreter<'de> {
    whole: &'de str,
    parser: Parser<'de>,
    variables: HashMap<&'de str, Atom<'de>>, // i think this is where we should hold all our state
}
impl<'de> Interpreter<'de> {
    pub fn new(input: &'de str) -> Self {
        Interpreter {
            whole: input,
            parser: Parser::new(input),
            variables: HashMap::new(),
        }
    }

    pub fn run_program(&mut self) -> Result<(), Vec<parse::Error>> {
        // run all the statements
        // return a vector of all the errors that occured?
        let mut contain_errors = false;

        loop {
            match self.parser.next() {
                Some(Ok(tt)) => self.interpret_statement(tt),
                // break, and containts error true
                Some(Err(e)) => {
                    contain_errors = true;
                    break;
                }
                None => break,
            };
        }

        if contain_errors {
            let parser = Parser::new(self.whole);
            let errors: Vec<parse::Error> = parser
                .into_iter()
                .filter(Result::is_err)
                .map(Result::unwrap_err)
                .collect();
            return Err(errors);
        }

        Ok(())
    }

    fn interpret_statement(&mut self, tt: TokenTree<'de>) -> Atom<'de> {
        let (op, mut parts) = match tt {
            /// Somehow, this can be lazily evaluated, if we store tokentrees and expressions
            /// in the hashmap instead
            TokenTree::Atom(Atom::Ident(ident)) => {
                return match self.variables.get(ident) {
                    Some(atom) => atom.clone(),
                    None => {
                        eprintln!("Undefined variable {ident}");
                        std::process::exit(70)
                    }
                };
            }
            TokenTree::Atom(atom) => return atom,
            TokenTree::Cons(op, vec) => (op, vec.into_iter()),
        };

        match op {
            Op::Plus => {
                let lhs = parts.next().expect("we expect first item for addition");
                let lhs = self.interpret_statement(lhs);

                let rhs = parts.next().expect("we expect second item for addition");
                let rhs = self.interpret_statement(rhs);
                maths(op, lhs, rhs)
            }
            Op::Star => {
                let lhs = parts
                    .next()
                    .expect("we expect first item for multiplication.");
                let lhs = self.interpret_statement(lhs);

                let rhs = parts
                    .next()
                    .expect("we expect second item for multiplication.");

                let rhs = self.interpret_statement(rhs);
                maths(op, lhs, rhs)
            }
            Op::Minus => {
                let lhs = parts
                    .next()
                    .expect("we expect first item for subtraction/negation");
                let lhs = self.interpret_statement(lhs);

                let Some(rhs) = parts.next() else {
                    // Negate the number if no rhs
                    if let Atom::Number(n) = lhs {
                        return Atom::Number(-n);
                    }
                    eprintln!("expected lhs of minus to mean negate");
                    std::process::exit(70);
                };
                let rhs = self.interpret_statement(rhs);
                maths(op, lhs, rhs)
            }
            Op::Slash => {
                let lhs = parts.next().expect("we expect first item for division.");
                let lhs = self.interpret_statement(lhs);

                let rhs = parts.next().expect("we expect second item for division.");
                let rhs = self.interpret_statement(rhs);
                maths(op, lhs, rhs)
            }
            Op::Print => {
                let first = parts.next().expect("Expecting something to print");
                let atom = self.interpret_statement(first);

                let atom = match atom {
                    Atom::Ident(ident) => self
                        .variables
                        .get(ident)
                        .expect("we expect the ident to be present"),
                    _ => &atom,
                };

                let s = self.atom_to_string(&atom);
                println!("{}", s);

                Atom::Nil
            }
            Op::Group => {
                self.interpret_statement(parts.next().expect("Expect a grouped token tree"))
            }
            Op::Bang => {
                let lhs =
                    self.interpret_statement(parts.next().expect("Expect lhs in equal equal"));
                match lhs {
                    Atom::Bool(b) => Atom::Bool(!b),
                    _ => {
                        eprintln!("Can only inverse boolean types using '!'");
                        std::process::exit(70);
                    }
                }
            }
            Op::Field => todo!(),
            Op::Less => {
                let (lhs, rhs) = (
                    self.interpret_statement(parts.next().expect("Expect lhs in equal equal")),
                    self.interpret_statement(parts.next().expect("Expect rhs in equal equal")),
                );
                match (lhs, rhs) {
                    (Atom::String(c1), Atom::String(c2)) => Atom::Bool(c1 < c2),
                    (Atom::Number(x), Atom::Number(y)) => Atom::Bool(x < y),
                    (Atom::Ident(s1), Atom::Ident(s2)) => Atom::Bool(s1 < s2),
                    (Atom::Bool(b1), Atom::Bool(b2)) => Atom::Bool(b1 < b2),
                    (Atom::Nil, Atom::Nil) => Atom::Bool(true),
                    (lhs, rhs) => {
                        eprintln!("Cannot compare lhs: {} with rhs: {}", lhs, rhs);
                        std::process::exit(70);
                    }
                }
            }
            Op::Greater => {
                let (lhs, rhs) = (
                    self.interpret_statement(parts.next().expect("Expect lhs in equal equal")),
                    self.interpret_statement(parts.next().expect("Expect rhs in equal equal")),
                );
                match (lhs, rhs) {
                    (Atom::String(c1), Atom::String(c2)) => Atom::Bool(c1 > c2),
                    (Atom::Number(x), Atom::Number(y)) => Atom::Bool(x > y),
                    (Atom::Ident(s1), Atom::Ident(s2)) => Atom::Bool(s1 > s2),
                    (Atom::Bool(b1), Atom::Bool(b2)) => Atom::Bool(b1 > b2),
                    (Atom::Nil, Atom::Nil) => Atom::Bool(true),
                    (lhs, rhs) => {
                        eprintln!("Cannot compare lhs: {} with rhs: {}", lhs, rhs);
                        std::process::exit(70);
                    }
                }
            }
            Op::LessEqual => {
                let (lhs, rhs) = (
                    self.interpret_statement(parts.next().expect("Expect lhs in equal equal")),
                    self.interpret_statement(parts.next().expect("Expect rhs in equal equal")),
                );
                match (lhs, rhs) {
                    (Atom::String(c1), Atom::String(c2)) => Atom::Bool(c1 <= c2),
                    (Atom::Number(x), Atom::Number(y)) => Atom::Bool(x <= y),
                    (Atom::Ident(s1), Atom::Ident(s2)) => Atom::Bool(s1 <= s2),
                    (Atom::Bool(b1), Atom::Bool(b2)) => Atom::Bool(b1 <= b2),
                    (Atom::Nil, Atom::Nil) => Atom::Bool(true),
                    (lhs, rhs) => {
                        eprintln!("Cannot compare lhs: {} with rhs: {}", lhs, rhs);
                        std::process::exit(70);
                    }
                }
            }
            Op::GreaterEqual => {
                let (lhs, rhs) = (
                    self.interpret_statement(parts.next().expect("Expect lhs in equal equal")),
                    self.interpret_statement(parts.next().expect("Expect rhs in equal equal")),
                );
                match (lhs, rhs) {
                    (Atom::String(c1), Atom::String(c2)) => Atom::Bool(c1 >= c2),
                    (Atom::Number(x), Atom::Number(y)) => Atom::Bool(x >= y),
                    (lhs, rhs) => {
                        eprintln!("Cannot compare lhs: {} with rhs: {}", lhs, rhs);
                        std::process::exit(70);
                    }
                }
            }
            Op::BangEqual => {
                let (lhs, rhs) = (
                    self.interpret_statement(parts.next().expect("Expect lhs in equal equal")),
                    self.interpret_statement(parts.next().expect("Expect rhs in equal equal")),
                );
                match (lhs, rhs) {
                    (Atom::String(c1), Atom::String(c2)) => Atom::Bool(c1 != c2),
                    (Atom::Number(x), Atom::Number(y)) => Atom::Bool(x != y),
                    (Atom::Bool(b1), Atom::Bool(b2)) => Atom::Bool(b1 != b2),
                    // idents are equal? shouldnt that actually be the value of that idents?
                    (Atom::Ident(s1), Atom::Ident(s2)) => Atom::Bool(s1 != s2),
                    (lhs, rhs) => {
                        eprintln!("Cannot compare lhs: {} with rhs: {}", lhs, rhs);
                        std::process::exit(70);
                    }
                }
            }
            Op::EqualEqual => {
                let (lhs, rhs) = (
                    self.interpret_statement(parts.next().expect("Expect lhs in equal equal")),
                    self.interpret_statement(parts.next().expect("Expect rhs in equal equal")),
                );
                match (lhs, rhs) {
                    (Atom::String(c1), Atom::String(c2)) => Atom::Bool(c1 == c2),
                    (Atom::Number(x), Atom::Number(y)) => Atom::Bool(x == y),
                    (Atom::Ident(s1), Atom::Ident(s2)) => Atom::Bool(s1 == s2),
                    (Atom::Bool(b1), Atom::Bool(b2)) => Atom::Bool(b1 == b2),
                    (Atom::Nil, Atom::Nil) => Atom::Bool(true),
                    (Atom::Ident(i1), Atom::Ident(i2)) => {
                        todo!()
                    }
                    // check if the Atom that we get from
                    // the Ident lookup is the same type
                    (Atom::Ident(i), other_atom) => {
                        todo!()
                    }
                    (other_atom, Atom::Ident(i)) => {
                        todo!()
                    }
                    (lhs, rhs) => {
                        eprintln!("Cannot compare lhs: {} with rhs: {}", lhs, rhs);
                        std::process::exit(70);
                    }
                }
            }
            Op::Declare => {
                let part = parts.next().expect("we expect an ident to be present");
                let TokenTree::Atom(Atom::Ident(ident)) = part else {
                    panic!("expected a identfier not {part:?}")
                };

                let value = if let Some(value) = parts.next() {
                    self.interpret_statement(value)
                } else {
                    Atom::Nil
                };
                // if Variable is only declared and not assigned, this value will be nil.
                self.variables.insert(ident, value);
                Atom::Nil
            }
            Op::Assign => {
                let should_be_ident = parts.next().expect("we expect an ident to be present");
                let TokenTree::Atom(Atom::Ident(ident)) = should_be_ident else {
                    panic!("expected a identfier not {should_be_ident:?}")
                };

                let value = self
                    .interpret_statement(parts.next().expect("we expect a value when assigning"));

                self.variables.insert(ident, value);

                // Possible  HACK: this might just be a hack, dont know yet.
                //
                // We return an ident here because print needs the accces the variable,
                // when we are assigning in a print statement
                //      let x;
                //      print x = 2;
                Atom::Ident(ident)
            }
            Op::Return => todo!(),
            Op::Call => todo!(),
        }
    }

    /// returns the evaluated
    fn atom_to_string(&self, atom: &Atom<'de>) -> String {
        match atom {
            Atom::Number(n) => format!("{n}"),
            Atom::Ident(ident) => panic!("should evaluate variable first"),
            _ => atom.to_string(),
        }
    }
}

fn maths<'de>(op: Op, lhs: Atom<'de>, rhs: Atom<'de>) -> Atom<'de> {
    match op {
        Op::Plus => match (lhs, rhs) {
            (Atom::String(s1), Atom::String(s2)) => Atom::String(s1 + s2),
            (Atom::Number(x), Atom::Number(y)) => Atom::Number(x + y),
            (a1, a2) => {
                eprintln!("cannot add {} to {}", a1, a2);
                std::process::exit(70);
            }
        },
        Op::Minus => match (lhs, rhs) {
            (Atom::Number(x), Atom::Number(y)) => Atom::Number(x - y),
            (a1, a2) => {
                eprintln!("cannot subtract {} to {}", a1, a2);
                std::process::exit(70);
            }
        },
        Op::Star => match (lhs, rhs) {
            (Atom::Number(x), Atom::Number(y)) => Atom::Number(x * y),
            (a1, a2) => {
                eprintln!("cannot multiply {} with {}", a1, a2);
                std::process::exit(70);
            }
        },
        Op::Slash => match (lhs, rhs) {
            (Atom::Number(x), Atom::Number(y)) => Atom::Number(x / y),
            (a1, a2) => {
                eprintln!("cannot divide {} to {}", a1, a2);
                std::process::exit(70);
            }
        },
        _ => panic!("invalid op for math"),
    }
}

// Helper trait for working with atoms in interpreter
trait AtomHelper {
    fn expect_atom(&self, other: Self) -> bool;
}

impl<'de: 'other, 'other> AtomHelper for Atom<'de> {
    fn expect_atom(&self, other: Atom<'other>) -> bool {
        match (self, other) {
            (Atom::String(_), Atom::String(_)) => true,
            (Atom::Number(_), Atom::Number(_)) => true,
            (Atom::Ident(_), Atom::Ident(_)) => true,
            (Atom::Bool(_), Atom::Bool(_)) => true,
            (Atom::Nil, Atom::Nil) => true,
            (Atom::Super, Atom::Super) => true,
            (Atom::This, Atom::This) => true,
            _ => false,
        }
    }
}
