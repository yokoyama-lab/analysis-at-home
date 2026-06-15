# Integer square root — r² ≤ n < (r+1)²

## Claim
`isqrt_aux` scans the candidate upward while `(r+1)² ≤ n`; `isqrt n` runs it with
fuel `S n`. Then

> **`isqrt_correct`**: `isqrt n * isqrt n <= n  /\  n < S (isqrt n) * S (isqrt n)`.

`isqrt n` is the unique `r` with `r² ≤ n < (r+1)²` — the floor of `√n`.

## Proof idea
The lower bound is an invariant (`isqrt_aux_lo`): the scan only advances to `S r`
when `(S r)² ≤ n`. The upper bound (`isqrt_aux_hi`) holds once the scan stops by
its condition `n < (S r)²`; fuel `S n` guarantees it gets there.

## Cost model
`func-ops`. Reference Rocq proof (`isqrt_correct`, axiom-free):
[`targets/rocq/Isqrt.v`](targets/rocq/Isqrt.v).
