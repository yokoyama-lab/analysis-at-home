# Logarithmic multiplication count of square-and-multiply

## Claim

Square-and-multiply (binary) exponentiation computes `base^e` using at most
**`2 · (number of bits of e)`** multiplications:

> `snd (sqm sq ds) ≤ 2 · length ds`,

where `ds` is the binary digit list of the exponent. Since `length ds =
⌊log₂ e⌋ + 1`, this is **logarithmic** in the exponent value.

## Cost model

`func-ops`, `counts = ["multiplication"]`. The reference model and a complete
Rocq proof (`square_and_multiply_mults`, axiom-free) are in
[`targets/rocq/FastExponentiation.v`](targets/rocq/FastExponentiation.v): each
digit costs one squaring, a 1-digit one extra multiply.

This is the project's first **logarithmic** cost bound. A functional-correctness
companion (`fst (sqm sq ds) = sq ^ denote ds`) is a natural open leaf.

## References

Pointers only.
- Knuth, *TAOCP* Vol. 2, evaluation of powers.
