# Fast-doubling Fibonacci — O(log n)

## Claim
Using the doubling identities
`fib(2k) = fib k·(2·fib(k+1) − fib k)` and `fib(2k+1) = fib k² + fib(k+1)²`,
`fastpair n` recurses on `n/2` and returns `(fib n, fib (n+1))`:

> **`fast_fib`**: `n <= fuel -> fastpair fuel n = (fib n, fib (S n))`.

This is `O(log n)` arithmetic operations — exponentially faster than the `O(n)`
naive recurrence, for the same result.

## Proof idea
The addition formula `fib(m+n+1) = fib(m+1)·fib(n+1) + fib m·fib n` (proved by
two-step induction) gives both doubling identities; `fast_fib` then follows by
induction on `fuel`, casing on `n mod 2`.

## Cost model
`func-ops`. Reference Rocq proof (`fast_fib`, axiom-free):
[`targets/rocq/FastFib.v`](targets/rocq/FastFib.v).
