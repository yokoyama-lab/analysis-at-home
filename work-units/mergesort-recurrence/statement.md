# Mergesort recurrence is n log n

## Claim
Mergesort splits in half, recurses twice, and merges in linear time, so its
comparison cost obeys `T(n) <= 2T(n/2) + n`. On inputs of size `2^k` this gives
> `T 0 = 0 -> (forall k, T (S k) <= 2*T k + 2^(S k)) -> forall k, T k <= k * 2^k`.

Since `k = lg n`, this is the classic `Theta(n log n)` bound.

## Cost model
`func-ops`, `counts = ["comparison"]`. Reference Rocq proof (`mergesort_recurrence`, axiom-free):
[`targets/rocq/MergesortRec.v`](targets/rocq/MergesortRec.v).
