# Lamé's theorem — Euclid's worst case is consecutive Fibonacci numbers

> *TAOCP Vol. 2 §4.5.3.* The tight `O(log)` bound behind the easy linear bound of
> [`euclid-gcd`](../euclid-gcd/).

## Claim
`steps fuel a b` counts the division steps of the Euclidean algorithm (it mirrors
`snd (euclid ...)` of the `euclid-gcd` unit). If it performs `n >= 1` steps on
`a > b`, then

> **`lame`**: `fib (S n) <= b  /\  fib (S (S n)) <= a`,

i.e. `b >= F(n+1)` and `a >= F(n+2)`. Consecutive Fibonacci numbers are therefore
the **smallest** pair forcing a given number of steps — the worst case. The
corollary `lame_divisor_bound` isolates the divisor bound `b >= F(n+1)`.

## Proof idea
Induction on `fuel` with the joint invariant. The step `(a,b) -> (b, a mod b)`
gives `a >= b + (a mod b)` (since `a > b` forces quotient `>= 1`), and two
consecutive remainders bounded below by consecutive Fibonacci numbers add to the
next one: `F(k) + F(k+1) = F(k+2)`.

## Cost model
`func-ops`, `counts = ["division"]`. Reference Rocq proof (`lame`,
`lame_divisor_bound`, axiom-free): [`targets/rocq/Lame.v`](targets/rocq/Lame.v).
