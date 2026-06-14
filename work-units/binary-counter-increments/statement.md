# Amortized cost of binary counter increments

## Claim

Starting from the empty counter, performing `n` increments costs at most `2n`
bit flips:

> `flips n ≤ 2 · n`,

i.e. **amortized O(1)** per increment, even though a single increment can flip
many bits.

## Cost model

`func-ops`, `counts = ["bit-flip"]`. The reference model and a complete Rocq
proof (`binary_counter_increments_amortized`, axiom-free) are in
[`targets/rocq/BinaryCounterIncrements.v`](targets/rocq/BinaryCounterIncrements.v).
The proof uses the **potential = popcount**: it establishes the invariant
`total flips + ones(state) = 2n`, so `flips n = 2n − ones(state) ≤ 2n`.

This is the project's first **amortized / aggregate** result — the analysis
style the design notes flag as the frontier (time-credits / potential method),
beyond worst-case-per-operation bounds.

## References

Pointers only.
- Cormen, Leiserson, Rivest, Stein, *Introduction to Algorithms* — amortized
  analysis of the binary counter.
