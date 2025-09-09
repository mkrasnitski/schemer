use std::fmt;

#[derive(Debug, PartialEq)]
pub enum Token<'a> {
    OpenParen,
    CloseParen,
    DoubleQuote,
    Bool(bool),
    Number(u64),
    Decimal(f64),
    StringLiteral(&'a str),
    Symbol(&'a str),
}

impl<'a> Token<'a> {
    fn new(word: &'a str, is_literal: bool) -> Option<Self> {
        if is_literal {
            Some(Token::StringLiteral(word))
        } else if word.is_empty() {
            None
        } else {
            Some(match word {
                "(" => Token::OpenParen,
                ")" => Token::CloseParen,
                "\"" => Token::DoubleQuote,
                _ => {
                    if let Ok(b) = word.parse() {
                        Token::Bool(b)
                    } else if let Ok(n) = word.parse() {
                        Token::Number(n)
                    } else if let Ok(d) = word.parse() {
                        Token::Decimal(d)
                    } else {
                        Token::Symbol(word)
                    }
                }
            })
        }
    }
}

impl fmt::Display for Token<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Token::OpenParen => write!(f, "("),
            Token::CloseParen => write!(f, ")"),
            Token::DoubleQuote => write!(f, "\""),
            Token::Bool(b) => write!(f, "{b}"),
            Token::Number(n) => write!(f, "{n}"),
            Token::Decimal(d) => write!(f, "{d}"),
            Token::StringLiteral(s) => write!(f, "{s}"),
            Token::Symbol(s) => write!(f, "{s}"),
        }
    }
}

pub struct TokenStream<'a> {
    input: &'a str,
    start: usize,
    string: bool,
}

impl<'a> TokenStream<'a> {
    pub fn new(input: &'a str) -> Self {
        Self {
            input,
            start: 0,
            string: false,
        }
    }
}

impl<'a> Iterator for TokenStream<'a> {
    type Item = Token<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.string {
            match self.input[self.start..].find('"') {
                Some(idx) => {
                    if idx == 0 {
                        self.start += 1;
                        self.string = false;
                        Some(Token::DoubleQuote)
                    } else {
                        let literal = &self.input[self.start..self.start + idx];
                        self.start += idx;
                        Some(Token::StringLiteral(literal))
                    }
                }
                None => {
                    let literal = &self.input[self.start..];
                    self.start = self.input.len();
                    if literal.is_empty() {
                        None
                    } else {
                        Some(Token::StringLiteral(literal))
                    }
                }
            }
        } else {
            // We split tokens on whitespace, except parentheses and double quotes which don't
            // need to be whitespace-separated.
            match self.input[self.start..]
                .match_indices(|c: char| c == '(' || c == ')' || c == '"' || c.is_whitespace())
                .next()
            {
                Some((idx, matched)) => {
                    if idx == 0 {
                        self.start += matched.len();
                        if matched.chars().all(char::is_whitespace) {
                            self.next()
                        } else {
                            let token = Token::new(matched, false);
                            if let Some(Token::DoubleQuote) = token {
                                self.string = true;
                            }
                            token
                        }
                    } else {
                        let token = Token::new(&self.input[self.start..self.start + idx], false);
                        self.start += idx;
                        token
                    }
                }
                None => {
                    let token = Token::new(&self.input[self.start..], false);
                    self.start = self.input.len();
                    token
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tokenize(input: &str) -> Vec<Token<'_>> {
        TokenStream::new(input).collect()
    }

    #[test]
    fn add() {
        assert_eq!(
            tokenize("(+ 1 2)"),
            vec![
                Token::OpenParen,
                Token::Symbol("+"),
                Token::Number(1),
                Token::Number(2),
                Token::CloseParen
            ]
        );
    }

    #[test]
    fn unmatched_open_paren() {
        assert_eq!(
            tokenize("(+ 1 2"),
            vec![
                Token::OpenParen,
                Token::Symbol("+"),
                Token::Number(1),
                Token::Number(2)
            ]
        )
    }

    #[test]
    fn unmatched_close_paren() {
        assert_eq!(
            tokenize("+ 1 2)"),
            vec![
                Token::Symbol("+"),
                Token::Number(1),
                Token::Number(2),
                Token::CloseParen,
            ]
        )
    }

    #[test]
    fn string() {
        assert_eq!(
            tokenize(r#"(+ "a" "b")"#),
            vec![
                Token::OpenParen,
                Token::Symbol("+"),
                Token::DoubleQuote,
                Token::StringLiteral("a"),
                Token::DoubleQuote,
                Token::DoubleQuote,
                Token::StringLiteral("b"),
                Token::DoubleQuote,
                Token::CloseParen,
            ]
        )
    }

    #[test]
    fn unterminated_string() {
        assert_eq!(
            tokenize(r#"(+ 1 "a)"#),
            vec![
                Token::OpenParen,
                Token::Symbol("+"),
                Token::Number(1),
                Token::DoubleQuote,
                Token::StringLiteral("a)"),
            ]
        )
    }

    #[test]
    fn nested_tokens() {
        assert_eq!(
            tokenize(r#"(+ "a + " "b + c")"#),
            vec![
                Token::OpenParen,
                Token::Symbol("+"),
                Token::DoubleQuote,
                Token::StringLiteral("a + "),
                Token::DoubleQuote,
                Token::DoubleQuote,
                Token::StringLiteral("b + c"),
                Token::DoubleQuote,
                Token::CloseParen,
            ]
        )
    }

    #[test]
    fn empty_string() {
        assert_eq!(
            tokenize(r#"(+ "" "a")"#),
            vec![
                Token::OpenParen,
                Token::Symbol("+"),
                Token::DoubleQuote,
                Token::DoubleQuote,
                Token::DoubleQuote,
                Token::StringLiteral("a"),
                Token::DoubleQuote,
                Token::CloseParen,
            ]
        )
    }
}
