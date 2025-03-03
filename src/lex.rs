// FIXME: Tokens need to have the line associated with them called.
// Implement so that the lexer keeps track of what the current line is.
// that way we can easily see what line the error occured on.

use derive_more::derive::{Error, From};
use std::fmt::Display;

pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug)]
pub struct Lexer<'de> {
    whole: &'de str,
    rest: &'de str,
    pub byte: usize,
    peeked: Option<Result<Token<'de>>>,
}

impl<'de> Lexer<'de> {
    pub fn new(data: &'de str) -> Self {
        Self {
            whole: data,
            rest: data,
            byte: 0,
            peeked: None,
        }
    }

    pub fn current_line(&self) -> usize {
        // current byte is the next char, 
        // and we dont include it with range ..byte
        self.whole[..self.byte].lines().count()
    }

    /// Peek at the next token.
    pub fn peek(&mut self) -> Option<&Result<Token<'de>>> {
        if self.peeked.is_none() {
            self.peeked = self.next()
        };
        self.peeked.as_ref()
    }

    pub fn expect_token(&mut self, token: TokenKind) -> Result<Token<'de>> {
        self.expect_token_with(|t| t.kind == token, token.to_expected_string())
    }
    pub fn expect_token_with(
        &mut self,
        check: impl Fn(&Token<'de>) -> bool,
        expect_msg: &'static str,
    ) -> Result<Token<'de>> {
        match self.next() {
            Some(Ok(token)) if check(&token) => Ok(token),
            Some(Ok(token)) => {
                let line = self.current_line();
                Err(Error::UnexpectedToken {
                    line,
                    expect_msg,
                    found: token.kind,
                    origin: token.origin.to_string(),
                })
            }
            Some(Err(e)) => Err(e.into()),
            None => Err(Error::Eof),
        }
    }
}

impl<'de> Iterator for Lexer<'de> {
    type Item = Result<Token<'de>>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(next) = self.peeked.take() {
            return Some(next);
        }

        enum Started {
            IfEqualElse(TokenKind, TokenKind),
            Slash,
            String,
            Number,
            Ident,
        }

        loop {
            let original_len = self.rest.len();
            self.rest = self.rest.trim_start();
            self.byte += original_len - self.rest.len();

            let from_c = self.rest;

            let mut chars = self.rest.chars();
            let c = chars.next()?;

            self.rest = chars.as_str();
            self.byte += c.len_utf8();

            let token = |o, t| Some(Ok(Token::new(o, t)));

            let started = match c {
                // NOTE: Safe to use 1 as index since we know the byte lenght of these tokens
                '(' => return token(&from_c[..1], TokenKind::LeftParen),
                ')' => return token(&from_c[..1], TokenKind::RightParen),
                '{' => return token(&from_c[..1], TokenKind::LeftBrace),
                '}' => return token(&from_c[..1], TokenKind::RightBrace),
                ',' => return token(&from_c[..1], TokenKind::Comma),
                '.' => return token(&from_c[..1], TokenKind::Dot),
                '-' => return token(&from_c[..1], TokenKind::Minus),
                '+' => return token(&from_c[..1], TokenKind::Plus),
                ';' => return token(&from_c[..1], TokenKind::Semicolon),
                '*' => return token(&from_c[..1], TokenKind::Star),
                '>' => Started::IfEqualElse(TokenKind::GreaterEqual, TokenKind::Greater),
                '<' => Started::IfEqualElse(TokenKind::LessEqual, TokenKind::Less),
                '=' => Started::IfEqualElse(TokenKind::EqualEqual, TokenKind::Equal),
                '!' => Started::IfEqualElse(TokenKind::BangEqual, TokenKind::Bang),
                '/' => Started::Slash,
                '"' => Started::String,
                '0'..='9' => Started::Number,
                'a'..='z' | 'A'..='Z' | '_' => Started::Ident,
                c => {
                    let line = self.whole[..self.byte].lines().count();
                    return Some(Err(Error::UnexpectedCharacter { line, char: c }));
                }
            };

            break match started {
                Started::Ident => {
                    let end = self
                        .rest
                        .chars()
                        .position(|c| !matches!(c, 'a'..='z' | 'A'..='Z' | '_' | '0'..='9'))
                        .unwrap_or_else(|| self.rest.len());

                    let ident = &from_c[..end + c.len_utf8()];

                    self.byte += end;
                    self.rest = &self.whole[self.byte..];

                    let kind = Token::keyword(ident).unwrap_or(TokenKind::Ident);

                    token(ident, kind)
                }
                Started::Number => {
                    let last = self
                        .rest
                        .chars()
                        .position(|c| !matches!(c, '0'..='9' | '.'))
                        .unwrap_or_else(|| self.rest.len());

                    let mut dot_split = self.rest[..last].splitn(3, '.');

                    let rest_len = match (dot_split.next(), dot_split.next(), dot_split.next()) {
                        (Some(number_before), Some(number_after), _) => {
                            let dot = if number_after.is_empty() { 0 } else { 1 };
                            number_before.len() + dot +  number_after.len()
                        }
                        (Some(single_number), None, None) => single_number.len(),
                        _ => unreachable!( "this should not occur we already found a number so should always be atleast 1 and will return the token on completion"),
                    };

                    self.byte += rest_len;
                    self.rest = &self.whole[self.byte..];

                    let parsed: f64 = from_c[..rest_len + c.len_utf8()]
                        .parse()
                        .expect("we expect this to parse string correctly");
                    token(
                        &from_c[..rest_len + c.len_utf8()],
                        TokenKind::Number(parsed),
                    )
                }
                Started::String => {
                    let Some(index) = self.rest.chars().position(|c| c == '"') else {
                        let line = self.whole[..self.byte].lines().count();
                        self.byte = self.whole.len();
                        self.rest = &self.whole[self.byte..];
                        return Some(Err(Error::UnterminatedString { line }));
                    };

                    let string_end: usize =
                        self.rest.chars().take(index).map(|c| c.len_utf8()).sum();
                    let s = &self.rest[..string_end];

                    self.byte += s.len() + '"'.len_utf8();
                    self.rest = &self.whole[self.byte..];

                    token(s, TokenKind::String)
                }
                Started::IfEqualElse(yes, no) => {
                    // We reset the iterator in the beginning of the loop
                    // So advancing it doesnt affect the next token
                    if chars.next().is_some_and(|c| c == '=') {
                        self.rest = chars.as_str();
                        self.byte += c.len_utf8();
                        break token(&from_c[..2], yes);
                    } else {
                        break token(&from_c[..c.len_utf8()], no);
                    }
                }
                Started::Slash => {
                    if chars.next().is_some_and(|c| c == '/') {
                        let rest_of_line = chars.as_str().lines().next()?;
                        self.byte += rest_of_line.len() + '\n'.len_utf8();

                        // lines().remainder() is on nightly, https://github.com/rust-lang/rust/issues/77998
                        // use that when available for remaining string
                        self.rest = &self.whole[self.byte..];
                        continue;
                    }
                    token(&from_c[0..c.len_utf8()], TokenKind::Slash)
                }
            };
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Token<'de> {
    pub origin: &'de str,
    pub kind: TokenKind,
    // up_until: &'de str,
}

impl<'de> Token<'de> {
    fn new(origin: &'de str, kind: TokenKind) -> Self {
        Self { origin, kind }
    }
    /// Returns a keyword if the string is a keyword
    /// else returns None
    fn keyword(origin: &'de str) -> Option<TokenKind> {
        let token = match origin {
            "and" => TokenKind::And,
            "class" => TokenKind::Class,
            "else" => TokenKind::Else,
            "false" => TokenKind::False,
            "for" => TokenKind::For,
            "fun" => TokenKind::Fun,
            "if" => TokenKind::If,
            "nil" => TokenKind::Nil,
            "or" => TokenKind::Or,
            "print" => TokenKind::Print,
            "return" => TokenKind::Return,
            "super" => TokenKind::Super,
            "this" => TokenKind::This,
            "true" => TokenKind::True,
            "var" => TokenKind::Var,
            "while" => TokenKind::While,
            _ => return None,
        };

        Some(token)
    }
}

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum TokenKind {
    LeftParen,
    RightParen,
    LeftBrace,
    RightBrace,
    Comma,
    Dot,
    Minus,
    Plus,
    Star,
    Slash,
    Semicolon,
    Equal,
    EqualEqual,
    Greater,
    GreaterEqual,
    Less,
    LessEqual,
    Bang,
    BangEqual,
    String,
    Number(f64),
    Ident,
    And,
    Class,
    Else,
    False,
    For,
    Fun,
    If,
    Nil,
    Or,
    Print,
    Return,
    Super,
    This,
    True,
    Var,
    While,
}
impl TokenKind {
    pub fn to_expected_string(&self) -> &'static str {
        match self {
            TokenKind::LeftParen => "(",
            TokenKind::RightParen => ")",
            TokenKind::LeftBrace => "{",
            TokenKind::RightBrace => "}",
            TokenKind::Comma => ",",
            TokenKind::Dot => ".",
            TokenKind::Minus => "-",
            TokenKind::Plus => "+",
            TokenKind::Semicolon => ";",
            TokenKind::Star => "*",
            TokenKind::GreaterEqual => ">",
            TokenKind::LessEqual => "<",
            TokenKind::EqualEqual => "=",
            TokenKind::BangEqual => "!",
            TokenKind::Slash => "/",
            TokenKind::Equal => "=",
            TokenKind::Greater => ">",
            TokenKind::Less => "<",
            TokenKind::Bang => "!",
            TokenKind::String => "STRING",
            TokenKind::Number(_) => "NUMBER",
            TokenKind::Ident => "IDENT",
            TokenKind::And => "AND",
            TokenKind::Class => "CLASS",
            TokenKind::Else => "ELSE",
            TokenKind::False => "FALSE",
            TokenKind::For => "FOR",
            TokenKind::Fun => "FUN",
            TokenKind::If => "IF",
            TokenKind::Nil => "NIL",
            TokenKind::Or => "OR",
            TokenKind::Print => "PRINT",
            TokenKind::Return => "RETURN",
            TokenKind::Super => "SUPER",
            TokenKind::This => "THIS",
            TokenKind::True => "TRUE",
            TokenKind::Var => "VAR",
            TokenKind::While => "WHILE",
        }
    }
}

impl std::fmt::Display for Token<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let origin = self.origin;

        match self.kind {
            TokenKind::LeftParen => write!(f, "LEFT_PAREN {} null", origin),
            TokenKind::RightParen => write!(f, "RIGHT_PAREN {} null", origin),
            TokenKind::LeftBrace => write!(f, "LEFT_BRACE {} null", origin),
            TokenKind::RightBrace => write!(f, "RIGHT_BRACE {} null", origin),
            TokenKind::Comma => write!(f, "COMMA {} null", origin),
            TokenKind::Dot => write!(f, "DOT {} null", origin),
            TokenKind::Minus => write!(f, "MINUS {} null", origin),
            TokenKind::Plus => write!(f, "PLUS {} null", origin),
            TokenKind::Semicolon => write!(f, "SEMICOLON {} null", origin),
            TokenKind::Star => write!(f, "STAR {} null", origin),
            TokenKind::Equal => write!(f, "EQUAL {} null", origin),
            TokenKind::EqualEqual => write!(f, "EQUAL_EQUAL {} null", origin),
            TokenKind::Greater => write!(f, "GREATER {} null", origin),
            TokenKind::GreaterEqual => write!(f, "GREATER_EQUAL {} null", origin),
            TokenKind::Less => write!(f, "LESS {} null", origin),
            TokenKind::LessEqual => write!(f, "LESS_EQUAL {} null", origin),
            TokenKind::Bang => write!(f, "BANG {} null", origin),
            TokenKind::BangEqual => write!(f, "BANG_EQUAL {} null", origin),
            TokenKind::Slash => write!(f, "SLASH {} null", origin),
            TokenKind::String => write!(f, "STRING \"{s}\" {s}", s = origin),
            TokenKind::Ident => write!(f, "IDENTIFIER {} null", origin),
            TokenKind::Number(n) => {
                // If n is a whole number, we need to add the decimal.
                if n == n.trunc() {
                    write!(f, "NUMBER {} {:.1}", self.origin, n)
                } else {
                    write!(f, "NUMBER {} {}", self.origin, n)
                }
            }
            TokenKind::And => write!(f, "AND and null"),
            TokenKind::Class => write!(f, "CLASS class null"),
            TokenKind::Else => write!(f, "ELSE else null"),
            TokenKind::False => write!(f, "FALSE false null"),
            TokenKind::For => write!(f, "FOR for null"),
            TokenKind::Fun => write!(f, "FUN fun null"),
            TokenKind::If => write!(f, "IF if null"),
            TokenKind::Nil => write!(f, "NIL nil null"),
            TokenKind::Or => write!(f, "OR or null"),
            TokenKind::Print => write!(f, "PRINT print null"),
            TokenKind::Return => write!(f, "RETURN return null"),
            TokenKind::Super => write!(f, "SUPER super null"),
            TokenKind::This => write!(f, "THIS this null"),
            TokenKind::True => write!(f, "TRUE true null"),
            TokenKind::Var => write!(f, "VAR var null"),
            TokenKind::While => write!(f, "WHILE while null"),
        }
    }
}

/// Lexing Error variants
#[derive(Debug, From, Error, Clone)]
pub enum Error {
    UnexpectedCharacter {
        line: usize,
        char: char,
    },
    UnterminatedString {
        line: usize,
    },
    UnexpectedToken {
        line: usize,
        expect_msg: &'static str,
        found: TokenKind,
        origin: String,
    },
    Eof,
}

impl Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::UnexpectedCharacter { line, char } => {
                write!(f, "[line {}] Error: Unexpected character: {}", line, char)
            }
            Error::UnterminatedString { line } => {
                write!(f, "[line {line}] Error: Unterminated string.")
            }
            Error::UnexpectedToken {
                line,
                found,
                origin,
                expect_msg,
            } => {
                write!(
                    f,
                    "{}Unexpected token, Expected: {expect_msg}, Found: '{origin}'",
                    crate::line_error(*line)
                )
            }
            Error::Eof => write!(f, "End of the file"),
        }
    }
}
