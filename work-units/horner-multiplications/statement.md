# Linear multiplication count of Horner's rule

## Claim

Evaluating a polynomial with `k` coefficients by **Horner's rule** uses exactly
`k − 1` multiplications:

> `snd (horner x coeffs) = length coeffs − 1`.

(`horner` returns the polynomial value together with the multiplication count;
each step `c + x·v` is one multiplication, the innermost coefficient costs none.)

## Cost model

`func-ops`, `counts = ["multiplication"]`. Reference Rocq proof
(`horner_mults_linear`, axiom-free):
[`targets/rocq/Horner.v`](targets/rocq/Horner.v).

## References
Knuth, *TAOCP* Vol. 2 (evaluation of polynomials).
