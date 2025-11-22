use std::fmt;
use std::str::FromStr;

#[derive(Clone, Debug, PartialEq)]
pub enum Token<'a> {
    OpenParen,
    CloseParen,
    DoubleQuote,
    Lambda,
    Define,
    If,
    Bool(bool),
    Number(u64),
    Decimal(f64),
    StringLiteral(&'a str),
    Symbol(&'a str),
    Operator(Operator),
}

impl<'a> Token<'a> {
    fn new(word: &'a str, is_literal: bool) -> Self {
        if is_literal {
            Token::StringLiteral(word)
        } else {
            match word {
                "(" => Token::OpenParen,
                ")" => Token::CloseParen,
                "\"" => Token::DoubleQuote,
                "lambda" => Token::Lambda,
                "define" => Token::Define,
                "if" => Token::If,
                _ => {
                    if let Ok(b) = bool::from_str(word) {
                        Token::Bool(b)
                    } else if let Ok(n) = u64::from_str(word) {
                        Token::Number(n)
                    } else if let Ok(d) = f64::from_str(word) {
                        Token::Decimal(d)
                    } else if let Some(op) = Operator::from_str(word) {
                        Token::Operator(op)
                    } else {
                        Token::Symbol(word)
                    }
                }
            }
        }
    }
}

impl fmt::Display for Token<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Token::OpenParen => write!(f, "("),
            Token::CloseParen => write!(f, ")"),
            Token::DoubleQuote => write!(f, "\""),
            Token::Lambda => write!(f, "lambda"),
            Token::Define => write!(f, "define"),
            Token::If => write!(f, "if"),
            Token::Bool(b) => write!(f, "{b}"),
            Token::Number(n) => write!(f, "{n}"),
            Token::Decimal(d) => write!(f, "{d}"),
            Token::StringLiteral(lit) => write!(f, "{lit}"),
            Token::Symbol(s) => write!(f, "{s}"),
            Token::Operator(op) => write!(f, "{op}"),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Operator {
    Plus,
    Minus,
    Star,
    Slash,
    Equal,
    NotEqual,
    Less,
    LessOrEqual,
    Greater,
    GreaterOrEqual,
}

impl Operator {
    fn from_str(s: &str) -> Option<Self> {
        match s {
            "+" => Some(Operator::Plus),
            "-" => Some(Operator::Minus),
            "*" => Some(Operator::Star),
            "/" => Some(Operator::Slash),
            "=" => Some(Operator::Equal),
            "!=" => Some(Operator::NotEqual),
            "<" => Some(Operator::Less),
            "<=" => Some(Operator::LessOrEqual),
            ">" => Some(Operator::Greater),
            ">=" => Some(Operator::GreaterOrEqual),
            _ => None,
        }
    }
}

impl fmt::Display for Operator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Operator::Plus => "+",
                Operator::Minus => "-",
                Operator::Star => "*",
                Operator::Slash => "/",
                Operator::Equal => "=",
                Operator::NotEqual => "!=",
                Operator::Less => "<",
                Operator::LessOrEqual => "<=",
                Operator::Greater => ">",
                Operator::GreaterOrEqual => ">=",
            }
        )
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
        // If we're in "string"-mode, we don't care about other delimiters and treat
        // everything between quotes as part of the string literal.
        let pattern = if self.string {
            |c: char| c == '"'
        } else {
            |c: char| c == '(' || c == ')' || c == '"' || c.is_whitespace()
        };

        // Consume the input incrementally by shifting `self.start` until we get to the end.
        if let Some((idx, matched)) = self.input[self.start..].match_indices(pattern).next() {
            if idx == 0 {
                // If we land right on a delimiter, simply consume it.
                self.start += matched.len();
                // Whitespace doesn't get included in the token stream. This will only get
                // hit when not in "string"-mode.
                if matched.chars().all(char::is_whitespace) {
                    self.next()
                } else {
                    let token = Token::new(matched, false);
                    // If we run into a double-quote, toggle "string"-mode on/off.
                    if let Token::DoubleQuote = token {
                        self.string = !self.string;
                    }
                    Some(token)
                }
            } else {
                // If the delimiter is not at index 0, consume up until the delimiter.
                let token = Token::new(&self.input[self.start..self.start + idx], self.string);
                self.start += idx;
                Some(token)
            }
        } else {
            // If we're out of delimiters, consume the remainder of the input.
            let word = &self.input[self.start..];
            self.start = self.input.len();
            if word.is_empty() {
                None
            } else {
                Some(Token::new(word, self.string))
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
                Token::Operator(Operator::Plus),
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
                Token::Operator(Operator::Plus),
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
                Token::Operator(Operator::Plus),
                Token::Number(1),
                Token::Number(2),
                Token::CloseParen,
            ]
        )
    }

    #[test]
    fn nested_lists() {
        assert_eq!(
            tokenize("(+ 1 (+ 2 3))"),
            vec![
                Token::OpenParen,
                Token::Operator(Operator::Plus),
                Token::Number(1),
                Token::OpenParen,
                Token::Operator(Operator::Plus),
                Token::Number(2),
                Token::Number(3),
                Token::CloseParen,
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
                Token::Operator(Operator::Plus),
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
                Token::Operator(Operator::Plus),
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
                Token::Operator(Operator::Plus),
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
                Token::Operator(Operator::Plus),
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
