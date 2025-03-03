//! # The Parser
//! Handles parsing a sequence of tokens into statements.
//! The consumer iterates over the parser to get the statments in order that they are defined.
//!```rust
//!//create a new parser
//!let parser = Parser::new("input string goes here");
//!
//!for statement in parser {
//!     //handle statement result
//!}
//!```
#![allow(unused, unreachable_code)]

use derive_more::derive::{Error, From};

use crate::lex::{self, Lexer, Token, TokenKind};

use std::{borrow::Cow, rc::Rc};

pub type Result<T> = std::result::Result<T, Error>;


#[derive(Debug)]
pub struct Parser<'de> {
    whole: &'de str,
    lexer: Lexer<'de>,
}

impl<'de> Iterator for Parser<'de> {
    type Item = Result<TokenTree<'de>>;
    /// This is parsing one statement at the time, consumes the semicolon afterwards
    fn next(&mut self) -> Option<Self::Item> {
        match self.parse_statement_within(0) {
            Ok(TokenTree::Atom(Atom::Nil)) => return None,
            Ok(tt) => Some(Ok(tt)),
            Err(e) => Some(Err(e)),
        }
    }
}

impl<'de> Parser<'de> {
    pub fn new(input: &'de str) -> Parser<'de> {
        Parser {
            whole: input,
            lexer: Lexer::new(input),
        }
    }
    pub fn reset(&mut self) {
        self.lexer = Lexer::new(self.whole)
    }
    pub fn parse(&mut self) -> Result<TokenTree<'de>> {
        // loop and get the vec of tokens, or implement iterator for parser
        self.parse_statement_within(0)
    }

   #[rustfmt::skip]
    pub fn parse_statement_within(&mut self, min_bp: u8) -> Result<TokenTree<'de>> {
        let curr_token: Token<'de> = match self.lexer.next() {
            Some(Ok(token)) => token,
            Some(Err(e)) => return Err(e.into()),
            None => return Ok(TokenTree::Atom(Atom::Nil)),
        };

        let mut lhs: TokenTree = match curr_token.kind {
            // should this be handled with special function?
            // i need to know if this is an expression or a 
            TokenKind::Ident => Atom::Ident(curr_token.origin).into(),
            TokenKind::Var => return self.var_stmt(),
            TokenKind::Print | TokenKind::Return => {
                let op = match curr_token.kind {
                    TokenKind::Print => Op::Print,
                    TokenKind::Return => Op::Return,
                    _ => unreachable!("Checked variants in previous match"),
                };
                let ((), r_bp) = prefix_bp(op);

                // statement takes care of semicolon
                let rhs = self.parse_statement_within(r_bp)?;

                return Ok(TokenTree::Cons(op, vec![rhs]));
            }
            token => {
                let expr = self.parse_expression_within(min_bp, Some(curr_token))?;
                return Ok(expr);
            }
        };

        loop {

            let op = self.lexer.peek();

            let op = match op {
                Some(Ok(op)) => op,
                Some(Err(e)) => return Err(e.clone().into()),
                None => break,
            };

            let op = match op.kind {
                TokenKind::RightBrace | TokenKind::RightParen | TokenKind::Comma | TokenKind::Semicolon => break,
                TokenKind::Dot => Op::Field,
                TokenKind::LeftParen=> Op::Call,
                TokenKind::Equal => Op::Assign, 
                _ => {
                    // this is an ident that is not a function, method/field call
                    let TokenTree::Atom(Atom::Ident(s)) = lhs else { 
                        panic!("Unexpected operator in statement parsing: {:?} {}", 
                            curr_token.kind, 
                            curr_token.origin,
                        );
                    };
                    lhs = self.parse_statement_within(0)?;
                    // should it break?
                    break;
                }
            };

            if let Some((l_bp, r_bp)) = infix_bp(op) {
                if l_bp < min_bp {
                    break;
                }

                let _ = self.lexer.next();
                let rhs = self.parse_expression_within(r_bp, None)?;
                lhs = TokenTree::Cons(op, vec![lhs, rhs]);

                continue;
            }
            break;
        }

        self.lexer.expect_token(TokenKind::Semicolon)?;
        Ok(lhs)
    }

    fn parse_expression_within(
        &mut self,
        min_bp: u8,
        lhs: Option<Token<'de>>,
    ) -> Result<TokenTree<'de>> {
        let curr_token = match lhs {
            // This is used when a statement already popped the left hand side,
            // and identified that it is an expression
            Some(lhs) => lhs,
            None => match self.lexer.next() {
                Some(Ok(token)) => token,
                Some(Err(e)) => return Err(e.into()),
                None => return Ok(TokenTree::Atom(Atom::Nil)),
            },
        };

        let mut lhs = match curr_token.kind {
            // Atoms
            TokenKind::True => TokenTree::Atom(Atom::Bool(true)),
            TokenKind::False => TokenTree::Atom(Atom::Bool(false)),
            TokenKind::Nil => TokenTree::Atom(Atom::Nil),
            TokenKind::Ident => TokenTree::Atom(Atom::Ident(curr_token.origin)),
            TokenKind::Number(n) => TokenTree::Atom(Atom::Number(n)),
            TokenKind::String => TokenTree::Atom(Atom::String(Cow::Borrowed(curr_token.origin))),
            TokenKind::Bang | TokenKind::Minus => {
                let op = match curr_token.kind {
                    TokenKind::Bang => Op::Bang,
                    TokenKind::Minus => Op::Minus,
                    _ => unreachable!("checked variant above"),
                };

                let ((), r_bp) = prefix_bp(op);
                let rhs = self.parse_expression_within(r_bp, None)?;

                TokenTree::Cons(op, vec![rhs])
            }
            TokenKind::LeftParen => {
                let lhs = self.parse_expression_within(0, None)?;
                let _ = self.lexer.expect_token(TokenKind::RightParen)?;

                TokenTree::Cons(Op::Group, vec![lhs])
            }
            token => {
                return Err(Error::ExpectedExpression {
                    line: self.lexer.current_line(),
                    at: curr_token.origin.to_string(),
                });
            }
        };

        loop {
            let op = self.lexer.peek();

            let op = match op {
                Some(Ok(op)) => op,
                Some(Err(e)) => return Err(e.clone().into()),
                None => break,
            };

            let op = match op.kind {
                TokenKind::RightBrace | TokenKind::RightParen | TokenKind::Comma | TokenKind::Semicolon => break,
                TokenKind::Minus=> Op::Minus,
                TokenKind::Plus => Op::Plus,
                TokenKind::Star => Op::Star,
                TokenKind::Slash => Op::Slash,
                TokenKind::Less => Op::Less,
                TokenKind::Greater => Op::Greater,
                TokenKind::LessEqual => Op::LessEqual,
                TokenKind::GreaterEqual => Op::GreaterEqual,
                TokenKind::EqualEqual => Op::EqualEqual,
                TokenKind::BangEqual => Op::BangEqual,
                _ => {
                    panic!("Unexpected operator in expression token: {:?} origin: '{}'", op.kind, op.origin);
                }
            };

            if let Some((l_bp, ())) = postfix_bp(op) {
                todo!()
            }

            if let Some((l_bp, r_bp)) = infix_bp(op) {
                if l_bp < min_bp {
                    break;
                }

                // Consumes the Op
                let _ = self.lexer.next();

                let rhs = self.parse_expression_within(r_bp, None)?;

                lhs = TokenTree::Cons(op, vec![lhs, rhs]);
                continue;
            }
            break;
        }
        Ok(lhs)
    }

    /// We are declaring a variable.
    fn var_stmt(&mut self) -> Result<TokenTree<'de>> {
        let op = Op::Declare;

        // TODO: this is the same as ident = expression;
        let ident = self.lexer.expect_token(TokenKind::Ident)?;
        let ident_token = TokenTree::Atom(Atom::Ident(ident.origin));

        let next_token = self.lexer.expect_token_with(
            |i| matches!(i.kind, TokenKind::Equal | TokenKind::Semicolon),
            "'=' or ';' after Var declaration ",
        )?;

        let rhs = match next_token.kind {
            TokenKind::Equal => vec![ident_token, self.parse_expression_within(0, None)?],
            // returns early since we already consumed the semicolon
            TokenKind::Semicolon => {
                return Ok((op, vec![ident_token]).into())
            },
            _ => unreachable!("checked in prevous expect_token_with"),
        };

        self.lexer.expect_token(TokenKind::Semicolon)?;

        return Ok((op, rhs).into());
    }

    fn handle_ident(&mut self, lhs: Token) -> std::result::Result<TokenTree<'de>, Error> {

        let operator = self.lexer.peek().ok_or(Error::UnexpectedEof)?;

        // an ident can be many things.
        // it can be a function call, 
        // it can be a field access
        // it can be assignment
        // it can be just part of an expresssion
        match operator {
            Ok(Token {
                kind: TokenKind::LeftParen,
                ..
            }) => todo!(),
            Ok(Token {
                kind: TokenKind::Dot,
                ..
            }) => todo!(),
            Ok(Token {
                kind: TokenKind::Equal,
                ..
            }) => todo!(),
            // or try an expression?
            // Here investigate if expression?
            // Thats why i need to peek so we keep the operator intact
            Ok(token) => return Err(Error::UnexpectedToken {  
                at: token.origin.to_string(), 
                line: self.lexer.current_line()
            }),
            Err(e) => return Err(e.clone().into()),
        }
    }
}

fn prefix_bp(op: Op) -> ((), u8) {
    match op {
        Op::Print | Op::Return => ((), 1),
        Op::Bang | Op::Minus => ((), 10),
        _ => panic!("bad op {op}"),
    }
}

fn infix_bp(op: Op) -> Option<(u8, u8)> {
    let res = match op {
        Op::Less
        | Op::Greater
        | Op::GreaterEqual
        | Op::LessEqual
        | Op::EqualEqual
        | Op::BangEqual => (2, 3),
        Op::Assign => (3, 2),
        Op::Plus | Op::Minus => (4, 5),
        Op::Star | Op::Slash => (7, 8),
        Op::Field => (11, 12),
        _ => return None,
    };
    Some(res)
}

fn postfix_bp(op: Op) -> Option<(u8, ())> {
    match op {
        _ => None,
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Atom<'de> {
    String(Cow<'de, str>),
    Number(f64),
    Ident(&'de str),
    Bool(bool),
    Nil,
    Super,
    This,
}

impl<'de> std::fmt::Display for Atom<'de> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Atom::String(s) => write!(f, "{s}"),
            Atom::Number(n) => {
                if *n == n.trunc() {
                    write!(f, "{n}.0")
                } else {
                    write!(f, "{n}")
                }
            }
            Atom::Ident(i) => write!(f, "{i}"),
            Atom::Bool(b) => write!(f, "{b}"),
            Atom::Nil => write!(f, "nil"),
            Atom::Super => write!(f, "super"),
            Atom::This => write!(f, "this"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Op {
    Plus,
    Minus,
    Group,
    Bang,
    Field,
    Star,
    Slash,
    Less,
    Greater,
    LessEqual,
    GreaterEqual,
    EqualEqual,
    BangEqual,
    Print,
    Return,
    /// Declaring a new variable
    Declare,
    /// Assigning to an existing variable
    Assign,
    Call,
}

impl std::fmt::Display for Op {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Op::Plus => write!(f, "+"),
            Op::Minus => write!(f, "-"),
            Op::Group => write!(f, "group"),
            Op::Bang => write!(f, "!"),
            Op::Star => write!(f, "*"),
            Op::Slash => write!(f, "/"),
            Op::Greater => write!(f, ">"),
            Op::GreaterEqual => write!(f, ">="),
            Op::Less => write!(f, "<"),
            Op::LessEqual => write!(f, "<="),
            Op::EqualEqual => write!(f, "=="),
            Op::BangEqual => write!(f, "!="),
            Op::Print => write!(f, "print"),
            Op::Declare => write!(f, "var"),
            Op::Assign => write!(f, "assign"),
            _ => write!(f, "FMT NOT IMPL"),
        }
    }
}

/// calling it a token tree instead of S expression
#[derive(Debug, Clone, PartialEq)]
pub enum TokenTree<'de> {
    Atom(Atom<'de>),
    Cons(Op, Vec<TokenTree<'de>>),
}

impl<'de> std::fmt::Display for TokenTree<'de> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TokenTree::Atom(token) => write!(f, "{}", token),
            TokenTree::Cons(token, tt) => {
                write!(f, "({}", token)?;
                for token in tt {
                    write!(f, " {}", token)?;
                }
                write!(f, ")")?;
                Ok(())
            }
        }
    }
}

impl<'de> From<(Op, Vec<TokenTree<'de>>)> for TokenTree<'de> {
    fn from(value: (Op, Vec<TokenTree<'de>>)) -> Self {
        TokenTree::Cons(value.0, value.1)
    }
}
impl<'de> From<Atom<'de>> for TokenTree<'de> {
    fn from(value: Atom<'de>) -> Self {
        TokenTree::Atom(value)
    }
}

#[derive(Debug, Error, From)]
pub enum Error {
    #[from]
    LexerError(lex::Error),
    ExpectedExpression {
        line: usize,
        at: String,
    },
    ExpectedOperator {
        line: usize,
        at: String,
    },
    UnexpectedToken {
        line: usize,
        at: String,
    },
    EmptyStatement,
    UnexpectedEof,
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::UnexpectedEof => write!(f, "unexpected EOF!"),
            Error::ExpectedExpression { line, at } => write!(
                f,
                "{} Error at '{}': Expected expresssion.",
                crate::line_error(*line),
                at
            ),
            Error::ExpectedOperator { line, at } => write!(
                f,
                "{} Error at '{}': Expected operator.",
                crate::line_error(*line),
                at
            ),
            Error::UnexpectedToken { line, at } => {
                write!(f, "{} Error at '{}'", crate::line_error(*line), at)
            }
            Error::EmptyStatement => write!(f, "{self:?}"),
            Error::LexerError(error) => write!(f, "{error}"),
        }
    }
}
