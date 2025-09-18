use std::fmt;
use std::iter::Peekable;

use crate::lexer::{Token, TokenStream};

type ParseResult<'a> = Result<Expression<'a>, ParseError<'a>>;

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
    If {
        cond: Box<Expression<'a>>,
        true_branch: Box<Expression<'a>>,
        false_branch: Box<Expression<'a>>,
    },
    List(Vec<Expression<'a>>),
}

#[derive(Debug, PartialEq)]
pub enum Declaration<'a> {
    Variable(&'a str),
    Function { name: &'a str, params: Vec<&'a str> },
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
                write!(f, "(define ")?;
                match decl {
                    Declaration::Variable(var) => write!(f, "{var}")?,
                    Declaration::Function { name, params } => {
                        if params.is_empty() {
                            write!(f, "({name})")?;
                        } else {
                            write!(f, "({name} {})", params.join(" "))?;
                        }
                    }
                }
                write!(f, " {body})")
            }
            Expression::If {
                cond,
                true_branch,
                false_branch,
            } => write!(f, "(if {cond} {true_branch} {false_branch})"),
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
    InvalidIf,
}

impl fmt::Display for ParseError<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Error: ")?;
        match self {
            ParseError::EndOfInput => write!(f, "Unexpected end of input"),
            ParseError::UnexpectedToken(token) => write!(f, "Unexpected token: {token}"),
            ParseError::InvalidDefinition => write!(f, "Invalid definition"),
            ParseError::InvalidIf => write!(f, "Invalid if clause"),
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

    pub fn parse(mut self) -> ParseResult<'a> {
        match self.next_token()? {
            Token::OpenParen => {
                let list = self.parse_list()?;
                match self.tokens.next() {
                    Some(token) => Err(ParseError::UnexpectedToken(token)),
                    None => Ok(list),
                }
            }
            token => Err(ParseError::UnexpectedToken(token)),
        }
    }

    fn parse_list(&mut self) -> ParseResult<'a> {
        let mut list = Vec::new();

        while let Some(token) = self.tokens.peek() {
            match token {
                Token::Define => return self.parse_definition(),
                Token::If => return self.parse_if(),
                Token::CloseParen => {
                    self.tokens.next();
                    return Ok(Expression::List(list));
                }
                _ => list.push(self.parse_expression()?),
            }
        }

        Err(ParseError::EndOfInput)
    }

    fn parse_expression(&mut self) -> ParseResult<'a> {
        let token = self.next_token()?;
        match token {
            Token::Bool(b) => Ok(Expression::Bool(b)),
            Token::Number(n) => Ok(Expression::Number(n)),
            Token::Decimal(d) => Ok(Expression::Decimal(d)),
            Token::Symbol(s) => Ok(Expression::Symbol(s)),
            Token::DoubleQuote => {
                // Remove double quotes from the token stream when parsing.
                let literal = match self.next_token()? {
                    Token::StringLiteral(s) => match self.next_token()? {
                        Token::DoubleQuote => s,
                        token => return Err(ParseError::UnexpectedToken(token)),
                    },
                    // Turn two consecutive double-quotes into an empty string literal.
                    Token::DoubleQuote => "",
                    token => return Err(ParseError::UnexpectedToken(token)),
                };
                Ok(Expression::StringLiteral(literal))
            }
            Token::OpenParen => self.parse_list(),
            // Closing parens need a matching open paren.
            Token::CloseParen => Err(ParseError::UnexpectedToken(token)),
            // String literals are surrounded by quotes, so bare literals are invalid.
            // Definitions and if statements are parsed inside `self.parse_list` and
            // must be preceded by an open parentheses.
            Token::StringLiteral(_) | Token::Define | Token::If => {
                Err(ParseError::UnexpectedToken(token))
            }
        }
    }

    fn parse_if(&mut self) -> ParseResult<'a> {
        let Token::If = self.next_token()? else {
            return Err(ParseError::InvalidIf);
        };

        let cond = Box::new(self.parse_expression()?);
        let branch = Box::new(self.parse_expression()?);
        let else_branch = Box::new(self.parse_expression()?);

        match self.next_token()? {
            Token::CloseParen => Ok(Expression::If {
                cond,
                true_branch: branch,
                false_branch: else_branch,
            }),
            _ => Err(ParseError::InvalidIf),
        }
    }

    fn parse_definition(&mut self) -> ParseResult<'a> {
        let Token::Define = self.next_token()? else {
            return Err(ParseError::InvalidDefinition);
        };

        let decl = match self.next_token()? {
            Token::Symbol(s) => Declaration::Variable(s),
            Token::OpenParen => {
                let Expression::List(list) = self.parse_list()? else {
                    return Err(ParseError::InvalidDefinition);
                };
                let mut list = list.into_iter();
                let Some(Expression::Symbol(name)) = list.next() else {
                    return Err(ParseError::InvalidDefinition);
                };
                let params = list
                    .map(|e| match e {
                        Expression::Symbol(s) => Some(s),
                        _ => None,
                    })
                    .collect::<Option<Vec<_>>>()
                    .ok_or(ParseError::InvalidDefinition)?;
                Declaration::Function { name, params }
            }
            _ => return Err(ParseError::InvalidDefinition),
        };

        let body = Box::new(self.parse_expression()?);

        match self.next_token()? {
            Token::CloseParen => Ok(Expression::Define { decl, body }),
            _ => Err(ParseError::InvalidDefinition),
        }
    }

    fn next_token(&mut self) -> Result<Token<'a>, ParseError<'a>> {
        self.tokens.next().ok_or(ParseError::EndOfInput)
    }
}

pub fn parse(input: &str) -> ParseResult<'_> {
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
            Ok(Expression::Define {
                decl: Declaration::Variable("a"),
                body: Box::new(Expression::Number(5)),
            })
        )
    }

    #[test]
    fn define_var_paren() {
        assert_eq!(
            parse("(define (a) 5)"),
            Ok(Expression::Define {
                decl: Declaration::Function {
                    name: "a",
                    params: vec![]
                },
                body: Box::new(Expression::Number(5)),
            })
        )
    }

    #[test]
    fn define_function() {
        assert_eq!(
            parse("(define (add1 a) (+ a 1))"),
            Ok(Expression::Define {
                decl: Declaration::Function {
                    name: "add1",
                    params: vec!["a"]
                },
                body: Box::new(Expression::List(vec![
                    Expression::Symbol("+"),
                    Expression::Symbol("a"),
                    Expression::Number(1),
                ])),
            })
        )
    }

    #[test]
    fn nested_define() {
        assert_eq!(
            parse("((define a 1))"),
            Ok(Expression::List(vec![Expression::Define {
                decl: Declaration::Variable("a"),
                body: Box::new(Expression::Number(1)),
            }]))
        )
    }

    #[test]
    fn ill_formed_define() {
        assert_eq!(
            parse("(define x 1 2 3)"),
            Err(ParseError::InvalidDefinition),
        )
    }

    #[test]
    fn factorial() {
        assert_eq!(
            parse("(define (factorial x) (if (< x 1) 1 (* x (factorial (- x 1)))))"),
            Ok(Expression::Define {
                decl: Declaration::Function {
                    name: "factorial",
                    params: vec!["x"]
                },
                body: Box::new(Expression::If {
                    cond: Box::new(Expression::List(vec![
                        Expression::Symbol("<"),
                        Expression::Symbol("x"),
                        Expression::Number(1)
                    ])),
                    true_branch: Box::new(Expression::Number(1)),
                    false_branch: Box::new(Expression::List(vec![
                        Expression::Symbol("*"),
                        Expression::Symbol("x"),
                        Expression::List(vec![
                            Expression::Symbol("factorial"),
                            Expression::List(vec![
                                Expression::Symbol("-"),
                                Expression::Symbol("x"),
                                Expression::Number(1),
                            ])
                        ])
                    ]))
                })
            })
        )
    }

    #[test]
    fn ill_formed_conditional() {
        assert_eq!(parse("(if <= 2 5 1 2)"), Err(ParseError::InvalidIf))
    }
}
