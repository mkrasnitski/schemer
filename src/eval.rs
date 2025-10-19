use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt;

use crate::lexer::Operator;
use crate::parser::{Declaration, Expression, ParseError, Parser};

pub type InterpreterResult<'a> = Result<Expression<'a>, InterpreterError<'a>>;
pub type EvalResult<'a> = Result<Expression<'a>, EvalError<'a>>;

#[derive(Debug, PartialEq)]
pub enum InterpreterError<'a> {
    Parse(ParseError<'a>),
    Eval(EvalError<'a>),
}

impl fmt::Display for InterpreterError<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            InterpreterError::Parse(e) => write!(f, "{e}"),
            InterpreterError::Eval(e) => write!(f, "{e}"),
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum EvalError<'a> {
    UndefinedSymbol(&'a str),
    InvalidCondition,
    InvalidApply,
    NotEnoughArgs,
    TooManyArgs,
    InvalidArgs,
}

impl fmt::Display for EvalError<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EvalError::UndefinedSymbol(s) => write!(f, "Undefined symbol: `{s}`"),
            EvalError::InvalidCondition => write!(f, "Invalid `if` condition"),
            EvalError::InvalidApply => write!(f, "Invalid function application"),
            EvalError::NotEnoughArgs => write!(f, "Not enough arguments"),
            EvalError::TooManyArgs => write!(f, "Too many arguments"),
            EvalError::InvalidArgs => write!(f, "Invalid function arguments"),
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq)]
pub struct Environment<'a> {
    env: HashMap<&'a str, Expression<'a>>,
}

impl<'a> Environment<'a> {
    pub fn get(&self, var: &'a str) -> Option<Expression<'a>> {
        self.env.get(var).cloned()
    }

    pub fn insert(&mut self, var: &'a str, expr: Expression<'a>) {
        self.env.insert(var, expr);
    }
}

pub fn eval_expr<'a>(expr: Expression<'a>, env: &mut Environment<'a>) -> EvalResult<'a> {
    match expr {
        Expression::Bool(_)
        | Expression::Number(_)
        | Expression::Decimal(_)
        | Expression::StringLiteral(_)
        | Expression::Operator(_)
        | Expression::Lambda { .. } => Ok(expr),
        Expression::Symbol(s) => env.get(s).ok_or(EvalError::UndefinedSymbol(s)),
        Expression::Define { decl, body } => match decl {
            Declaration::Variable(var) => {
                let value = eval_expr(*body, env)?;
                env.insert(var, value);
                Ok(Expression::Symbol(var))
            }
            Declaration::Function { name, params } => {
                env.insert(name, Expression::Lambda { params, body });
                Ok(Expression::Symbol(name))
            }
        },
        Expression::If {
            cond,
            true_branch,
            false_branch,
        } => match eval_expr(*cond, env)? {
            Expression::Bool(true) => eval_expr(*true_branch, env),
            Expression::Bool(false) => eval_expr(*false_branch, env),
            _ => Err(EvalError::InvalidCondition),
        },
        Expression::Apply { op, args } => match eval_expr(*op, env)? {
            Expression::Lambda { params, body } => match args.len().cmp(&params.len()) {
                Ordering::Less => Err(EvalError::NotEnoughArgs),
                Ordering::Greater => Err(EvalError::TooManyArgs),
                Ordering::Equal => {
                    let mut local_env = env.clone();
                    for (param, arg) in params.into_iter().zip(args) {
                        local_env.insert(param, eval_expr(arg, env)?);
                    }
                    eval_expr(*body, &mut local_env)
                }
            },
            Expression::Operator(op) => {
                let [l, r] = args
                    .try_into()
                    .map_err(|args: Vec<_>| match args.len().cmp(&2) {
                        Ordering::Less => EvalError::NotEnoughArgs,
                        Ordering::Greater => EvalError::TooManyArgs,
                        Ordering::Equal => unreachable!(),
                    })?;
                match (eval_expr(l, env)?, eval_expr(r, env)?) {
                    (Expression::Number(l), Expression::Number(r)) => Ok(op.eval_args(l, r)),
                    (Expression::Decimal(l), Expression::Decimal(r)) => Ok(op.eval_args(l, r)),
                    _ => Err(EvalError::InvalidArgs),
                }
            }
            _ => Err(EvalError::InvalidApply),
        },
    }
}

impl Operator {
    fn eval_args<T, U>(self, left: T, right: U) -> Expression<'static>
    where
        BinaryArgs<T, U>: EvalOperator,
    {
        BinaryArgs { left, right }.eval_operator(self)
    }
}

struct BinaryArgs<T, U> {
    left: T,
    right: U,
}

trait EvalOperator {
    fn eval_operator(&self, op: Operator) -> Expression<'static>;
}

impl EvalOperator for BinaryArgs<u64, u64> {
    fn eval_operator(&self, op: Operator) -> Expression<'static> {
        match op {
            Operator::Plus => Expression::Number(self.left + self.right),
            Operator::Minus => Expression::Number(self.left - self.right),
            Operator::Star => Expression::Number(self.left * self.right),
            Operator::Slash => Expression::Number(self.left / self.right),
            Operator::Equal => Expression::Bool(self.left == self.right),
            Operator::NotEqual => Expression::Bool(self.left != self.right),
            Operator::Less => Expression::Bool(self.left < self.right),
            Operator::LessOrEqual => Expression::Bool(self.left <= self.right),
            Operator::Greater => Expression::Bool(self.left > self.right),
            Operator::GreaterOrEqual => Expression::Bool(self.left >= self.right),
        }
    }
}

impl EvalOperator for BinaryArgs<f64, f64> {
    fn eval_operator(&self, op: Operator) -> Expression<'static> {
        match op {
            Operator::Plus => Expression::Decimal(self.left + self.right),
            Operator::Minus => Expression::Decimal(self.left - self.right),
            Operator::Star => Expression::Decimal(self.left * self.right),
            Operator::Slash => Expression::Decimal(self.left / self.right),
            Operator::Equal => Expression::Bool(self.left == self.right),
            Operator::NotEqual => Expression::Bool(self.left != self.right),
            Operator::Less => Expression::Bool(self.left < self.right),
            Operator::LessOrEqual => Expression::Bool(self.left <= self.right),
            Operator::Greater => Expression::Bool(self.left > self.right),
            Operator::GreaterOrEqual => Expression::Bool(self.left >= self.right),
        }
    }
}

pub fn eval(program: &str) -> InterpreterResult<'_> {
    let mut env = Environment::default();
    Parser::new(program)
        .map(|expr| match expr {
            Ok(expr) => eval_expr(expr, &mut env).map_err(InterpreterError::Eval),
            Err(e) => Err(InterpreterError::Parse(e)),
        })
        .collect::<Result<Vec<_>, _>>()?
        .pop()
        .ok_or(InterpreterError::Parse(ParseError::EndOfInput))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn define_var() {
        assert_eq!(eval("(define x 5)"), Ok(Expression::Symbol("x")))
    }

    #[test]
    fn define_function() {
        assert_eq!(
            eval("(define (inc x) (+ x 1))"),
            Ok(Expression::Symbol("inc"))
        )
    }

    #[test]
    fn undefined_symbol() {
        assert_eq!(
            eval("x"),
            Err(InterpreterError::Eval(EvalError::UndefinedSymbol("x")))
        )
    }

    #[test]
    fn if_true() {
        assert_eq!(eval("(if true 1 2)"), Ok(Expression::Number(1)))
    }

    #[test]
    fn if_false() {
        assert_eq!(eval("(if false 1 2)"), Ok(Expression::Number(2)))
    }

    #[test]
    fn empty_lambda() {
        assert_eq!(eval("((lambda () 1))"), Ok(Expression::Number(1)))
    }

    #[test]
    fn identity_lambda() {
        assert_eq!(eval("((lambda (x) x) 1)"), Ok(Expression::Number(1)))
    }

    #[test]
    fn not_enough_args() {
        assert_eq!(
            eval("((lambda (x y) (+ x y)) 1)"),
            Err(InterpreterError::Eval(EvalError::NotEnoughArgs)),
        )
    }

    #[test]
    fn too_many_args() {
        assert_eq!(
            eval("((lambda (x y) (+ x y)) 1 2 3)"),
            Err(InterpreterError::Eval(EvalError::TooManyArgs)),
        )
    }

    #[test]
    fn nested_lambdas() {
        assert_eq!(
            eval("(((lambda (x) (x)) (lambda () (lambda (x) x))) 1)"),
            Ok(Expression::Number(1)),
        )
    }

    #[test]
    fn fibonacci() {
        assert_eq!(
            eval(
                "(define (fib n)
                    (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2)))))
                 (fib 10)"
            ),
            Ok(Expression::Number(55))
        )
    }

    #[test]
    fn fast_fibonacci() {
        assert_eq!(
            eval(
                "(define (calc-fib n a b)
                    (if (= n 1) a (calc-fib (- n 1) b (+ a b))))
                 (define (fib n) (calc-fib n 1 1))
                 (fib 90)"
            ),
            Ok(Expression::Number(2880067194370816120))
        )
    }
}
