# Horner's rule — correctness

> Correctness twin of [`horner-multiplications`](../horner-multiplications/) (which
> counts the n multiplications).

## Claim
`horner (a::t) x = a + x * horner t x` computes the polynomial
`poly cs x = Σ_i cs_i · x^i`:

> **`horner_correct`**: `horner cs x = poly cs x`.

## Proof idea
The helper `powsum cs x i = x^i · horner cs x` (induction on `cs`, `Nat.pow_succ_r'`
and `ring`); the theorem is the `i = 0` case.

## Cost model
`func-ops`. Reference Rocq proof (`horner_correct`, axiom-free):
[`targets/rocq/Horner.v`](targets/rocq/Horner.v).
