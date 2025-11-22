use std::fmt;
use std::iter::Peekable;

use crate::lexer::{Operator, Token, TokenStream};

type ParseResult<'a> = Result<Expression<'a>, ParseError<'a>>;

#[derive(Clone, Debug, PartialEq)]
pub enum Expression<'a> {
    Bool(bool),
    Number(u64),
    Decimal(f64),
    StringLiteral(&'a str),
    Symbol(&'a str),
    Operator(Operator),
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
            Expression::StringLiteral(lit) => write!(f, "{lit:?}"),
            Expression::Symbol(s) => write!(f, "{s}"),
            Expression::Operator(op) => write!(f, "{op}"),
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

    fn next_token(&mut self) -> Result<Token<'a>, ParseError<'a>> {
        self.tokens.next().ok_or(ParseError::EndOfInput)
    }

    fn parse_expression(&mut self) -> ParseResult<'a> {
        let token = self.next_token()?;
        match token {
            Token::Bool(b) => Ok(Expression::Bool(b)),
            Token::Number(n) => Ok(Expression::Number(n)),
            Token::Decimal(d) => Ok(Expression::Decimal(d)),
            Token::Symbol(s) => Ok(Expression::Symbol(s)),
            Token::Operator(op) => Ok(Expression::Operator(op)),
            Token::DoubleQuote => {
                // Remove double quotes from the token stream when parsing.
                let literal = match self.next_token()? {
                    Token::StringLiteral(s) => match self.next_token()? {
                        Token::DoubleQuote => s,
                        _ => unreachable!(),
                    },
                    // Turn two consecutive double-quotes into an empty string literal.
                    Token::DoubleQuote => "",
                    _ => unreachable!(),
                };
                Ok(Expression::StringLiteral(literal))
            }
            // String literals are surrounded by quotes, and it's impossible for the lexer to
            // produce a bare literal.
            Token::StringLiteral(_) => unreachable!(),
            Token::OpenParen => {
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
                            args: self.parse_expression_list()?,
                        })
                    }
                }
            }
            // Closing parens need a matching open paren.
            Token::CloseParen => Err(ParseError::UnexpectedToken(token)),
            // Lambdas, definitions, and if statements are surrounded by parentheses and must
            // appear immediately following the opening paren.
            Token::Lambda | Token::Define | Token::If => Err(ParseError::UnexpectedToken(token)),
        }
    }

    fn parse_expression_list(&mut self) -> Result<Vec<Expression<'a>>, ParseError<'a>> {
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
            let params = self.parse_symbol_list()?;
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
                    let symbols = self.parse_symbol_list()?;
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

    fn parse_symbol_list(&mut self) -> Result<Vec<&'a str>, ParseError<'a>> {
        self.parse_expression_list()?
            .into_iter()
            .map(|e| match e {
                Expression::Symbol(s) => Some(s),
                _ => None,
            })
            .collect::<Option<Vec<_>>>()
            .ok_or(ParseError::InvalidDefinition)
    }
}

impl<'a> Iterator for Parser<'a> {
    type Item = ParseResult<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.tokens.peek().is_none() {
            None
        } else {
            Some(self.parse_expression())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(input: &str) -> Result<Vec<Expression<'_>>, ParseError<'_>> {
        Parser::new(input).collect()
    }

    #[test]
    fn bool() {
        assert_eq!(parse("true"), Ok(vec![Expression::Bool(true)]))
    }

    #[test]
    fn number() {
        assert_eq!(parse("1"), Ok(vec![Expression::Number(1)]))
    }

    #[test]
    fn decimal() {
        assert_eq!(parse("1.0"), Ok(vec![Expression::Decimal(1.0)]))
    }

    #[test]
    fn add() {
        assert_eq!(
            parse("(+ 1 2)"),
            Ok(vec![Expression::Apply {
                op: Box::new(Expression::Operator(Operator::Plus)),
                args: vec![Expression::Number(1), Expression::Number(2)]
            }])
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
            Err(ParseError::UnexpectedToken(Token::CloseParen))
        )
    }

    #[test]
    fn nested_lists() {
        assert_eq!(
            parse("(+ 1 (+ 2 3))"),
            Ok(vec![Expression::Apply {
                op: Box::new(Expression::Operator(Operator::Plus)),
                args: vec![
                    Expression::Number(1),
                    Expression::Apply {
                        op: Box::new(Expression::Operator(Operator::Plus)),
                        args: vec![Expression::Number(2), Expression::Number(3)]
                    }
                ]
            }])
        )
    }

    #[test]
    fn string() {
        assert_eq!(
            parse(r#"(+ "a" "b")"#),
            Ok(vec![Expression::Apply {
                op: Box::new(Expression::Operator(Operator::Plus)),
                args: vec![
                    Expression::StringLiteral("a"),
                    Expression::StringLiteral("b"),
                ]
            }])
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
            Ok(vec![Expression::Apply {
                op: Box::new(Expression::Operator(Operator::Plus)),
                args: vec![
                    Expression::StringLiteral("a + "),
                    Expression::StringLiteral("b + c"),
                ]
            }])
        )
    }

    #[test]
    fn empty_string() {
        assert_eq!(
            parse(r#"(+ "" "a")"#),
            Ok(vec![Expression::Apply {
                op: Box::new(Expression::Operator(Operator::Plus)),
                args: vec![
                    Expression::StringLiteral(""),
                    Expression::StringLiteral("a"),
                ],
            }])
        )
    }

    #[test]
    fn lambda() {
        assert_eq!(
            parse("(lambda (x) (+ x 1))"),
            Ok(vec![Expression::Lambda {
                params: vec!["x"],
                body: Box::new(Expression::Apply {
                    op: Box::new(Expression::Operator(Operator::Plus)),
                    args: vec![Expression::Symbol("x"), Expression::Number(1)]
                })
            }])
        )
    }

    #[test]
    fn bare_lambda() {
        assert_eq!(
            parse("lambda"),
            Err(ParseError::UnexpectedToken(Token::Lambda))
        )
    }

    #[test]
    fn define_var() {
        assert_eq!(
            parse("(define a 5)"),
            Ok(vec![Expression::Define {
                decl: Declaration::Variable("a"),
                body: Box::new(Expression::Number(5)),
            }])
        )
    }

    #[test]
    fn define_var_paren() {
        assert_eq!(
            parse("(define (a) 5)"),
            Ok(vec![Expression::Define {
                decl: Declaration::Function {
                    name: "a",
                    params: vec![]
                },
                body: Box::new(Expression::Number(5)),
            }])
        )
    }

    #[test]
    fn define_function() {
        assert_eq!(
            parse("(define (add1 a) (+ a 1))"),
            Ok(vec![Expression::Define {
                decl: Declaration::Function {
                    name: "add1",
                    params: vec!["a"]
                },
                body: Box::new(Expression::Apply {
                    op: Box::new(Expression::Operator(Operator::Plus)),
                    args: vec![Expression::Symbol("a"), Expression::Number(1)]
                })
            }])
        )
    }

    #[test]
    fn nested_define() {
        assert_eq!(
            parse("((define a 1))"),
            Ok(vec![Expression::Apply {
                op: Box::new(Expression::Define {
                    decl: Declaration::Variable("a"),
                    body: Box::new(Expression::Number(1))
                }),
                args: vec![],
            }])
        )
    }

    #[test]
    fn ill_formed_define() {
        assert_eq!(parse("(define 1 2)"), Err(ParseError::InvalidDefinition))
    }

    #[test]
    fn ill_formed_define_var() {
        assert_eq!(
            parse("(define x 1 2 3)"),
            Err(ParseError::InvalidDefinition)
        )
    }

    #[test]
    fn ill_formed_define_proc() {
        assert_eq!(
            parse("(define (x 1) 2)"),
            Err(ParseError::InvalidDefinition)
        )
    }

    #[test]
    fn ill_formed_define_empty_proc() {
        assert_eq!(parse("(define () 1)"), Err(ParseError::InvalidDefinition))
    }

    #[test]
    fn factorial() {
        assert_eq!(
            parse("(define (factorial x) (if (< x 1) 1 (* x (factorial (- x 1)))))"),
            Ok(vec![Expression::Define {
                decl: Declaration::Function {
                    name: "factorial",
                    params: vec!["x"]
                },
                body: Box::new(Expression::If {
                    cond: Box::new(Expression::Apply {
                        op: Box::new(Expression::Operator(Operator::Less)),
                        args: vec![Expression::Symbol("x"), Expression::Number(1)]
                    }),
                    true_branch: Box::new(Expression::Number(1)),
                    false_branch: Box::new(Expression::Apply {
                        op: Box::new(Expression::Operator(Operator::Star)),
                        args: vec![
                            Expression::Symbol("x"),
                            Expression::Apply {
                                op: Box::new(Expression::Symbol("factorial")),
                                args: vec![Expression::Apply {
                                    op: Box::new(Expression::Operator(Operator::Minus)),
                                    args: vec![Expression::Symbol("x"), Expression::Number(1)]
                                }]
                            }
                        ]
                    })
                })
            }])
        )
    }

    #[test]
    fn ill_formed_conditional() {
        assert_eq!(parse("(if <= 2 5 1 2)"), Err(ParseError::InvalidIf))
    }

    #[test]
    fn multiple_exprs() {
        assert_eq!(
            parse("(define (inc x) (+ x 1)) (inc 3)"),
            Ok(vec![
                Expression::Define {
                    decl: Declaration::Function {
                        name: "inc",
                        params: vec!["x"],
                    },
                    body: Box::new(Expression::Apply {
                        op: Box::new(Expression::Operator(Operator::Plus)),
                        args: vec![Expression::Symbol("x"), Expression::Number(1)],
                    })
                },
                Expression::Apply {
                    op: Box::new(Expression::Symbol("inc")),
                    args: vec![Expression::Number(3)]
                }
            ])
        )
    }

    #[test]
    fn empty_apply() {
        assert_eq!(parse("()"), Err(ParseError::EmptyApply))
    }
}
