use std::fmt;
use std::iter::Peekable;

use crate::lexer::{Token, TokenStream};

type ParseResult<'a, T> = Result<T, ParseError<'a>>;

#[derive(Debug, PartialEq)]
pub enum Expression<'a> {
    Bool(bool),
    Number(u64),
    Decimal(f64),
    StringLiteral(&'a str),
    Symbol(&'a str),
    Define {
        decl: Declaration<'a>,
        body: Box<Expression<'a>>,
    },
    List(Vec<Expression<'a>>),
}

#[derive(Debug, PartialEq)]
pub enum Declaration<'a> {
    Variable(&'a str),
    Function(Vec<&'a str>),
}

impl fmt::Display for Expression<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expression::Bool(b) => write!(f, "{b}"),
            Expression::Number(n) => write!(f, "{n}"),
            Expression::Decimal(d) => write!(f, "{d}"),
            Expression::StringLiteral(s) => write!(f, "{s:?}"),
            Expression::Symbol(s) => write!(f, "{s}"),
            Expression::Define { decl, body } => {
                write!(f, "define ")?;
                match decl {
                    Declaration::Variable(var) => write!(f, "{var}")?,
                    Declaration::Function(args) => write!(f, "({})", args.join(" "))?,
                }
                write!(f, " {body}")
            }
            Expression::List(list) => {
                write!(
                    f,
                    "({})",
                    list.iter()
                        .map(|expr| format!("{expr}"))
                        .collect::<Vec<_>>()
                        .join(" ")
                )
            }
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum ParseError<'a> {
    EndOfInput,
    UnexpectedToken(Token<'a>),
    InvalidDefinition,
}

impl fmt::Display for ParseError<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Error: ")?;
        match self {
            ParseError::EndOfInput => write!(f, "Unexpected end of input"),
            ParseError::UnexpectedToken(token) => write!(f, "Unexpected token: {token}"),
            ParseError::InvalidDefinition => write!(f, "Invalid definition"),
        }
    }
}

impl std::error::Error for ParseError<'_> {}

pub struct Parser<'a> {
    tokens: Peekable<TokenStream<'a>>,
}

impl<'a> Parser<'a> {
    pub fn new(input: &'a str) -> Self {
        Self {
            tokens: TokenStream::new(input).peekable(),
        }
    }

    pub fn parse(mut self) -> ParseResult<'a, Expression<'a>> {
        match self.tokens.next() {
            Some(Token::OpenParen) => {
                let list = self.parse_list()?;
                match self.tokens.next() {
                    Some(token) => Err(ParseError::UnexpectedToken(token)),
                    None => Ok(Expression::List(list)),
                }
            }
            Some(token) => Err(ParseError::UnexpectedToken(token)),
            None => Err(ParseError::EndOfInput),
        }
    }

    fn parse_list(&mut self) -> ParseResult<'a, Vec<Expression<'a>>> {
        let mut list = Vec::new();

        while let Some(token) = self.tokens.peek() {
            match token {
                Token::CloseParen => {
                    self.tokens.next();
                    return Ok(list);
                }
                _ => list.push(self.parse_expression()?),
            }
        }

        Err(ParseError::EndOfInput)
    }

    fn parse_expression(&mut self) -> ParseResult<'a, Expression<'a>> {
        let Some(token) = self.tokens.next() else {
            return Err(ParseError::EndOfInput);
        };

        match token {
            Token::Bool(b) => Ok(Expression::Bool(b)),
            Token::Number(n) => Ok(Expression::Number(n)),
            Token::Decimal(d) => Ok(Expression::Decimal(d)),
            Token::Symbol(s) => Ok(Expression::Symbol(s)),
            Token::Define => self.parse_definition(),
            Token::DoubleQuote => {
                // Remove double quotes from the token stream when parsing.
                let literal = match self.tokens.next() {
                    Some(Token::StringLiteral(s)) => match self.tokens.next() {
                        Some(Token::DoubleQuote) => s,
                        Some(token) => return Err(ParseError::UnexpectedToken(token)),
                        None => return Err(ParseError::EndOfInput),
                    },
                    // Turn two consecutive double-quotes into an empty string literal.
                    Some(Token::DoubleQuote) => "",
                    Some(token) => return Err(ParseError::UnexpectedToken(token)),
                    None => return Err(ParseError::EndOfInput),
                };
                Ok(Expression::StringLiteral(literal))
            }
            Token::OpenParen => Ok(Expression::List(self.parse_list()?)),
            // Closing parens need a matching open paren.
            Token::CloseParen => return Err(ParseError::UnexpectedToken(token)),
            // String literals are surrounded by quotes, so bare literals are invalid.
            Token::StringLiteral(_) => return Err(ParseError::UnexpectedToken(token)),
        }
    }

    fn parse_definition(&mut self) -> ParseResult<'a, Expression<'a>> {
        let Some(token) = self.tokens.next() else {
            return Err(ParseError::EndOfInput);
        };

        let decl = match token {
            Token::Symbol(s) => Declaration::Variable(s),
            Token::OpenParen => Declaration::Function(
                self.parse_list()?
                    .into_iter()
                    .map(|e| match e {
                        Expression::Symbol(s) => Some(s),
                        _ => None,
                    })
                    .collect::<Option<Vec<_>>>()
                    .ok_or(ParseError::InvalidDefinition)?,
            ),
            _ => return Err(ParseError::InvalidDefinition),
        };

        let body = Box::new(self.parse_expression()?);

        Ok(Expression::Define { decl, body })
    }
}

pub fn parse(input: &str) -> ParseResult<'_, Expression<'_>> {
    Parser::new(input).parse()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn add() {
        assert_eq!(
            parse("(+ 1 2)"),
            Ok(Expression::List(vec![
                Expression::Symbol("+"),
                Expression::Number(1),
                Expression::Number(2)
            ]))
        )
    }

    #[test]
    fn unmatched_open_paren() {
        assert_eq!(parse("(+ 1 2"), Err(ParseError::EndOfInput),)
    }

    #[test]
    fn unmatched_close_paren() {
        assert_eq!(
            parse("+ 1 2)"),
            Err(ParseError::UnexpectedToken(Token::Symbol("+"))),
        )
    }

    #[test]
    fn nested_lists() {
        assert_eq!(
            parse("(+ 1 (+ 2 3))"),
            Ok(Expression::List(vec![
                Expression::Symbol("+"),
                Expression::Number(1),
                Expression::List(vec![
                    Expression::Symbol("+"),
                    Expression::Number(2),
                    Expression::Number(3),
                ])
            ]))
        )
    }

    #[test]
    fn trailing_tokens() {
        assert_eq!(
            parse("(+ 1 2) a"),
            Err(ParseError::UnexpectedToken(Token::Symbol("a"))),
        )
    }

    #[test]
    fn string() {
        assert_eq!(
            parse(r#"(+ "a" "b")"#),
            Ok(Expression::List(vec![
                Expression::Symbol("+"),
                Expression::StringLiteral("a"),
                Expression::StringLiteral("b"),
            ]))
        )
    }

    #[test]
    fn unterminated_string() {
        assert_eq!(parse(r#"(+ 1 "a)"#), Err(ParseError::EndOfInput))
    }

    #[test]
    fn nested_tokens() {
        assert_eq!(
            parse(r#"(+ "a + " "b + c")"#),
            Ok(Expression::List(vec![
                Expression::Symbol("+"),
                Expression::StringLiteral("a + "),
                Expression::StringLiteral("b + c"),
            ]))
        )
    }

    #[test]
    fn empty_string() {
        assert_eq!(
            parse(r#"(+ "" "a")"#),
            Ok(Expression::List(vec![
                Expression::Symbol("+"),
                Expression::StringLiteral(""),
                Expression::StringLiteral("a"),
            ]))
        )
    }

    #[test]
    fn define_var() {
        assert_eq!(
            parse("(define a 5)"),
            Ok(Expression::List(vec![Expression::Define {
                decl: Declaration::Variable("a"),
                body: Box::new(Expression::Number(5)),
            }]))
        )
    }

    #[test]
    fn define_var_paren() {
        assert_eq!(
            parse("(define (a) 5)"),
            Ok(Expression::List(vec![Expression::Define {
                decl: Declaration::Function(vec!["a"]),
                body: Box::new(Expression::Number(5)),
            }]))
        )
    }

    #[test]
    fn define_function() {
        assert_eq!(
            parse("(define (add1 a) (+ a 1))"),
            Ok(Expression::List(vec![Expression::Define {
                decl: Declaration::Function(vec!["add1", "a"]),
                body: Box::new(Expression::List(vec![
                    Expression::Symbol("+"),
                    Expression::Symbol("a"),
                    Expression::Number(1),
                ])),
            }]))
        )
    }
}
