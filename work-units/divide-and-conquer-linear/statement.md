# One recursive call + linear work is linear

## Claim
A divide-and-conquer with a **single** recursive call on half the input plus
linear combine work obeys `T(n) <= T(n/2) + n`. The geometric series
`n + n/2 + n/4 + ... < 2n` is dominated by the top level, so on `2^k` inputs
> `T 0 = 0 -> (forall k, T (S k) <= T k + 2^(S k)) -> forall k, T k <= 2^(S k)`,

i.e. `T(n) <= 2n = O(n)`. This is the Master-Theorem regime where the work shrinks
geometrically (contrast `mergesort-recurrence`, where the two halves balance the
levels into `n log n`).

## Cost model
`func-ops`, `counts = ["operation"]`. Reference Rocq proof (`dc_linear_recurrence`, axiom-free):
[`targets/rocq/DCLinear.v`](targets/rocq/DCLinear.v).
