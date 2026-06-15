# Subtractive GCD — Euclid's original, no division

> Subtraction-only contrast to [`euclid-gcd`](../euclid-gcd/) (which uses `mod`).

## Claim
`gcd(a,b) = gcd(a-b, b)` for `a >= b` (and symmetrically). `subgcd` applies this
repeatedly, with the fuel bound `a + b` (the sum strictly decreases each step).
Then

> **`subgcd_correct`**: `a + b <= fuel -> subgcd fuel a b = Nat.gcd a b`.

## Proof idea
Induction on `fuel`; each step is justified by `Nat.gcd_sub_diag_r`
(`n <= m -> gcd n (m-n) = gcd n m`) and `Nat.gcd_comm`.

## Cost model
`func-ops`. Reference Rocq proof (`subgcd_correct`, axiom-free):
[`targets/rocq/SubGcd.v`](targets/rocq/SubGcd.v).
