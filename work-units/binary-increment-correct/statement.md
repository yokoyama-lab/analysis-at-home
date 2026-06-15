# Binary increment — adds exactly one

> Correctness companion to [`binary-counter-increments`](../binary-counter-increments/)
> (its amortized `O(1)` cost).

## Claim
`inc` ripples the carry over a little-endian bit list (0 → 1 and stop; 1 → 0 and
carry). Reading back with Horner base 2,

> **`inc_correct`**: `from_bits (inc l) = S (from_bits l)`.

## Proof idea
Induction on the bit list, casing on the low bit; `lia` closes each case (the
`true` case uses the IH on the carried tail).

## Cost model
`func-ops`. Reference Rocq proof (`inc_correct`, axiom-free):
[`targets/rocq/BinInc.v`](targets/rocq/BinInc.v).
