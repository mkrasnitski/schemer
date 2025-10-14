use std::fmt;
use std::iter::Peekable;

use crate::lexer::{Token, TokenStream};

type ParseResult<'a> = Result<Expression<'a>, ParseError<'a>>;

#[derive(Clone, Debug, PartialEq)]
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
    Lambda {
        params: Vec<&'a str>,
        body: Box<Expression<'a>>,
    },
    Apply {
        op: Box<Expression<'a>>,
        args: Vec<Expression<'a>>,
    },
}

#[derive(Clone, Debug, PartialEq)]
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
            Expression::Lambda { params, body } => {
                write!(f, "(lambda ({}) {body})", params.join(" "))
            }
            Expression::Apply { op, args } => {
                if args.is_empty() {
                    write!(f, "({op})")
                } else {
                    write!(
                        f,
                        "({op} {})",
                        args.iter()
                            .map(|expr| format!("{expr}"))
                            .collect::<Vec<_>>()
                            .join(" ")
                    )
                }
            }
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum ParseError<'a> {
    EndOfInput,
    UnexpectedToken(Token<'a>),
    InvalidLambda,
    InvalidDefinition,
    InvalidIf,
    EmptyApply,
}

impl fmt::Display for ParseError<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Error: ")?;
        match self {
            ParseError::EndOfInput => write!(f, "Unexpected end of input"),
            ParseError::UnexpectedToken(token) => write!(f, "Unexpected token: {token}"),
            ParseError::InvalidLambda => write!(f, "Invalid lambda"),
            ParseError::InvalidDefinition => write!(f, "Invalid definition"),
            ParseError::InvalidIf => write!(f, "Invalid if clause"),
            ParseError::EmptyApply => write!(f, "Empty function application"),
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
        let expr = self.parse_expression()?;
        match self.tokens.next() {
            Some(token) => Err(ParseError::UnexpectedToken(token)),
            None => Ok(expr),
        }
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
            // Lambdas, definitions, and if statements are parsed inside `self.parse_list`
            // and must be preceded by an open parentheses.
            Token::StringLiteral(_) | Token::Lambda | Token::Define | Token::If => {
                Err(ParseError::UnexpectedToken(token))
            }
        }
    }

    fn parse_list(&mut self) -> ParseResult<'a> {
        let Some(token) = self.tokens.peek() else {
            return Err(ParseError::EndOfInput);
        };

        match token {
            Token::Lambda => self.parse_lambda(),
            Token::Define => self.parse_definition(),
            Token::If => self.parse_if(),
            Token::CloseParen => Err(ParseError::EmptyApply),
            _ => {
                let op = Box::new(self.parse_expression()?);
                Ok(Expression::Apply {
                    op,
                    args: self.consume_list()?,
                })
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

    fn parse_lambda(&mut self) -> ParseResult<'a> {
        if let Token::Lambda = self.next_token()?
            && let Token::OpenParen = self.next_token()?
        {
            let params = self.consume_symbol_list()?;
            let body = Box::new(self.parse_expression()?);

            if let Token::CloseParen = self.next_token()? {
                return Ok(Expression::Lambda { params, body });
            }
        }

        Err(ParseError::InvalidLambda)
    }

    fn parse_definition(&mut self) -> ParseResult<'a> {
        if let Token::Define = self.next_token()? {
            let decl = match self.next_token()? {
                Token::Symbol(s) => Declaration::Variable(s),
                Token::OpenParen => {
                    let symbols = self.consume_symbol_list()?;
                    let Some((name, params)) = symbols.split_first() else {
                        return Err(ParseError::InvalidDefinition);
                    };
                    Declaration::Function {
                        name,
                        params: params.to_vec(),
                    }
                }
                _ => return Err(ParseError::InvalidDefinition),
            };

            let body = Box::new(self.parse_expression()?);
            if let Token::CloseParen = self.next_token()? {
                return Ok(Expression::Define { decl, body });
            }
        }

        Err(ParseError::InvalidDefinition)
    }

    fn next_token(&mut self) -> Result<Token<'a>, ParseError<'a>> {
        self.tokens.next().ok_or(ParseError::EndOfInput)
    }

    fn consume_list(&mut self) -> Result<Vec<Expression<'a>>, ParseError<'a>> {
        let mut list = Vec::new();
        loop {
            match self.tokens.peek() {
                Some(Token::CloseParen) => {
                    self.tokens.next();
                    return Ok(list);
                }
                Some(_) => list.push(self.parse_expression()?),
                None => return Err(ParseError::EndOfInput),
            }
        }
    }

    fn consume_symbol_list(&mut self) -> Result<Vec<&'a str>, ParseError<'a>> {
        self.consume_list()?
            .into_iter()
            .map(|e| match e {
                Expression::Symbol(s) => Some(s),
                _ => None,
            })
            .collect::<Option<Vec<_>>>()
            .ok_or(ParseError::InvalidDefinition)
    }
}

pub fn parse(input: &str) -> ParseResult<'_> {
    Parser::new(input).parse()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bool() {
        assert_eq!(parse("true"), Ok(Expression::Bool(true)))
    }

    #[test]
    fn number() {
        assert_eq!(parse("1"), Ok(Expression::Number(1)))
    }

    #[test]
    fn decimal() {
        assert_eq!(parse("1.0"), Ok(Expression::Decimal(1.0)))
    }

    #[test]
    fn add() {
        assert_eq!(
            parse("(+ 1 2)"),
            Ok(Expression::Apply {
                op: Box::new(Expression::Symbol("+")),
                args: vec![Expression::Number(1), Expression::Number(2)]
            })
        )
    }

    #[test]
    fn unmatched_open_paren() {
        assert_eq!(parse("(+ 1 2"), Err(ParseError::EndOfInput))
    }

    #[test]
    fn unmatched_close_paren() {
        assert_eq!(
            parse("+ 1 2)"),
            Err(ParseError::UnexpectedToken(Token::Number(1))),
        )
    }

    #[test]
    fn nested_lists() {
        assert_eq!(
            parse("(+ 1 (+ 2 3))"),
            Ok(Expression::Apply {
                op: Box::new(Expression::Symbol("+")),
                args: vec![
                    Expression::Number(1),
                    Expression::Apply {
                        op: Box::new(Expression::Symbol("+")),
                        args: vec![Expression::Number(2), Expression::Number(3)]
                    }
                ]
            })
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
            Ok(Expression::Apply {
                op: Box::new(Expression::Symbol("+")),
                args: vec![
                    Expression::StringLiteral("a"),
                    Expression::StringLiteral("b"),
                ]
            })
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
            Ok(Expression::Apply {
                op: Box::new(Expression::Symbol("+")),
                args: vec![
                    Expression::StringLiteral("a + "),
                    Expression::StringLiteral("b + c"),
                ]
            })
        )
    }

    #[test]
    fn empty_string() {
        assert_eq!(
            parse(r#"(+ "" "a")"#),
            Ok(Expression::Apply {
                op: Box::new(Expression::Symbol("+")),
                args: vec![
                    Expression::StringLiteral(""),
                    Expression::StringLiteral("a"),
                ],
            })
        )
    }

    #[test]
    fn lambda() {
        assert_eq!(
            parse("(lambda (x) (+ x 1))"),
            Ok(Expression::Lambda {
                params: vec!["x"],
                body: Box::new(Expression::Apply {
                    op: Box::new(Expression::Symbol("+")),
                    args: vec![Expression::Symbol("x"), Expression::Number(1)]
                })
            })
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
                body: Box::new(Expression::Apply {
                    op: Box::new(Expression::Symbol("+")),
                    args: vec![Expression::Symbol("a"), Expression::Number(1)]
                })
            })
        )
    }

    #[test]
    fn nested_define() {
        assert_eq!(
            parse("((define a 1))"),
            Ok(Expression::Apply {
                op: Box::new(Expression::Define {
                    decl: Declaration::Variable("a"),
                    body: Box::new(Expression::Number(1))
                }),
                args: vec![],
            })
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
                    cond: Box::new(Expression::Apply {
                        op: Box::new(Expression::Symbol("<")),
                        args: vec![Expression::Symbol("x"), Expression::Number(1)]
                    }),
                    true_branch: Box::new(Expression::Number(1)),
                    false_branch: Box::new(Expression::Apply {
                        op: Box::new(Expression::Symbol("*")),
                        args: vec![
                            Expression::Symbol("x"),
                            Expression::Apply {
                                op: Box::new(Expression::Symbol("factorial")),
                                args: vec![Expression::Apply {
                                    op: Box::new(Expression::Symbol("-")),
                                    args: vec![Expression::Symbol("x"), Expression::Number(1)]
                                }]
                            }
                        ]
                    })
                })
            })
        )
    }

    #[test]
    fn ill_formed_conditional() {
        assert_eq!(parse("(if <= 2 5 1 2)"), Err(ParseError::InvalidIf))
    }
}
