# Russian peasant multiplication

## Claim
Using only doubling, halving and addition,
`peasant a b = (a mod 2)*b + peasant (a/2) (2*b)` (and `peasant 0 b = 0`). Then

> **`peasant_correct`**: `a <= fuel -> peasant fuel a b = a * b`.

## Proof idea
Induction on `fuel`; the step rests on `a = 2*(a/2) + a mod 2`
(`Nat.div_mod_eq`), closed by `nia`.

## Cost model
`func-ops`. Reference Rocq proof (`peasant_correct`, axiom-free):
[`targets/rocq/Peasant.v`](targets/rocq/Peasant.v).
