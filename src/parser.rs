use std::fmt;

use crate::lexer::{Token, TokenStream};

type ParseResult<'a> = Result<Expression<'a>, ParseError<'a>>;

#[derive(Debug, PartialEq)]
pub enum Expression<'a> {
    Bool(bool),
    Number(u64),
    Decimal(f64),
    StringLiteral(&'a str),
    Symbol(&'a str),
    List(Vec<Expression<'a>>),
}

impl fmt::Display for Expression<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expression::Bool(b) => write!(f, "{b}"),
            Expression::Number(n) => write!(f, "{n}"),
            Expression::Decimal(d) => write!(f, "{d}"),
            Expression::StringLiteral(s) => write!(f, "{s:?}"),
            Expression::Symbol(s) => write!(f, "{s}"),
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
}

impl fmt::Display for ParseError<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Error: ")?;
        match self {
            ParseError::EndOfInput => write!(f, "Unexpected end of input"),
            ParseError::UnexpectedToken(token) => write!(f, "Unexpected token: {token}"),
        }
    }
}

impl std::error::Error for ParseError<'_> {}

pub fn parse(input: &str) -> ParseResult<'_> {
    let mut tokens = TokenStream::new(input);
    match tokens.next() {
        Some(Token::OpenParen) => {
            let ast = parse_ast(&mut tokens)?;
            match tokens.next() {
                Some(token) => Err(ParseError::UnexpectedToken(token)),
                None => Ok(ast),
            }
        }
        Some(token) => Err(ParseError::UnexpectedToken(token)),
        None => Err(ParseError::EndOfInput),
    }
}

fn parse_ast<'a>(tokens: &mut TokenStream<'a>) -> ParseResult<'a> {
    let mut list = Vec::new();

    while let Some(token) = tokens.next() {
        match token {
            Token::Bool(b) => list.push(Expression::Bool(b)),
            Token::Number(n) => list.push(Expression::Number(n)),
            Token::Decimal(d) => list.push(Expression::Decimal(d)),
            Token::Symbol(s) => list.push(Expression::Symbol(s)),
            Token::StringLiteral(_) => return Err(ParseError::UnexpectedToken(token)),
            Token::DoubleQuote => {
                // Remove double quotes from the token stream when parsing.
                let literal = match tokens.next() {
                    Some(Token::StringLiteral(s)) => match tokens.next() {
                        Some(Token::DoubleQuote) => s,
                        Some(token) => return Err(ParseError::UnexpectedToken(token)),
                        None => break,
                    },
                    // Turn two consecutive double-quotes into an empty string literal.
                    Some(Token::DoubleQuote) => "",
                    Some(token) => return Err(ParseError::UnexpectedToken(token)),
                    None => break,
                };
                list.push(Expression::StringLiteral(literal));
            }
            Token::OpenParen => list.push(parse_ast(tokens)?),
            Token::CloseParen => return Ok(Expression::List(list)),
        }
    }

    Err(ParseError::EndOfInput)
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
}
