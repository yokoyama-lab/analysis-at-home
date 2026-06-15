# Exponentiation by squaring — correctness

> Correctness twin of [`fast-exponentiation-mults`](../fast-exponentiation-mults/)
> (which counts the `~lg e` multiplications).

## Claim
`fastpow b e = (b^(e/2))^2 * b^(e mod 2)` (and `fastpow b 0 = 1`). Then

> **`fastpow_correct`**: `e <= fuel -> fastpow fuel b e = b ^ e`.

## Proof idea
Induction on `fuel`; combine `b^(e/2) * b^(e/2) * b^(e mod 2) = b^(2*(e/2)+e mod 2)`
via `Nat.pow_add_r`, and `e = 2*(e/2)+e mod 2` (`Nat.div_mod_eq`).

## Cost model
`func-ops`. Reference Rocq proof (`fastpow_correct`, axiom-free):
[`targets/rocq/FastPow.v`](targets/rocq/FastPow.v).
