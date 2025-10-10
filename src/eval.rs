use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt;

use crate::parser::{Declaration, Expression, ParseError, parse};

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
}

impl fmt::Display for EvalError<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EvalError::UndefinedSymbol(s) => write!(f, "Undefined symbol: `{s}`"),
            EvalError::InvalidCondition => write!(f, "Invalid `if` condition"),
            EvalError::InvalidApply => write!(f, "Invalid function application"),
            EvalError::NotEnoughArgs => write!(f, "Not enough arguments"),
            EvalError::TooManyArgs => write!(f, "Too many arguments"),
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
        Expression::List(exprs) => {
            if let Some((op, args)) = exprs.split_first()
                && let Expression::Lambda { params, body } = eval_expr(op.clone(), env)?
            {
                match args.len().cmp(&params.len()) {
                    Ordering::Less => Err(EvalError::NotEnoughArgs),
                    Ordering::Greater => Err(EvalError::TooManyArgs),
                    Ordering::Equal => {
                        let mut local_env = env.clone();
                        for (param, arg) in params.into_iter().zip(args) {
                            local_env.insert(param, eval_expr(arg.clone(), env)?);
                        }
                        eval_expr(*body, &mut local_env)
                    }
                }
            } else {
                Err(EvalError::InvalidApply)
            }
        }
    }
}

pub fn eval(program: &str) -> InterpreterResult<'_> {
    let mut env = Environment::default();
    let expr = parse(program).map_err(InterpreterError::Parse)?;
    eval_expr(expr, &mut env).map_err(InterpreterError::Eval)
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
}
