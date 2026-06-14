# Exact addition count of iterative Fibonacci

## Claim
Iterative Fibonacci with two accumulators uses **exactly `n`** additions for `n`
steps:
> `snd (fibc a b n) = n`.

One addition `a + b` per step. Contrast the *exponential* call count of naive
recursion — a clean cost-of-algorithm-choice comparison.

## Cost model
`func-ops`, `counts = ["addition"]`. Reference Rocq proof
(`iterative_fibonacci_additions`, axiom-free):
[`targets/rocq/IterativeFibonacci.v`](targets/rocq/IterativeFibonacci.v).
