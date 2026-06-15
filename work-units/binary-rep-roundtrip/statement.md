# Binary representation — faithful round-trip

## Claim
`to_bits n = (n mod 2) :: to_bits (n/2)` (bits 0/1, LSB first); `from_bits` reads
them back by Horner in base 2. Then

> **`bits_roundtrip`**: `n <= fuel -> from_bits (to_bits fuel n) = n`.

## Proof idea
Induction on `fuel`; the step is `n = 2*(n/2) + n mod 2` (`Nat.div_mod_eq`).

## Cost model
`func-ops`. Reference Rocq proof (`bits_roundtrip`, axiom-free):
[`targets/rocq/Bits.v`](targets/rocq/Bits.v).
