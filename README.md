# schemer

A toy functional Lisp-style language inspired by Scheme. Supports string literals, integer and floating-point arithmetic, bools, variables, and lambdas.

## Usage

Either run a single file:

```console
$ cat fib.sc
(define (calc-fib n a b)
   (if (= n 1) a (calc-fib (- n 1) b (+ a b))))
(define (fib n) (calc-fib n 1 1))
(fib 90)
$ cargo run --release fib.sc
2880067194370816120
```

Or, run the built-in REPL by providing no arguments:
```console
$ cargo run --release
> (define (calc-fib n a b) (if (= n 1) a (calc-fib (- n 1) b (+ a b))))
calc-fib
> (define (fib n) (calc-fib n 1 1))
fib
> (fib 90)
2880067194370816120
```
