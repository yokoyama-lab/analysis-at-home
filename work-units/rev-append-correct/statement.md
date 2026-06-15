# Tail-recursive reversal — correctness

## Claim
`rapp l acc` reverses `l` onto `acc`; `fast_rev l = rapp l []`. Then

> **`fast_rev_correct`**: `fast_rev l = rev l`.

The accumulator version is `O(n)` (one cons per element), unlike the naive `rev`
built from `++` which is `O(n^2)`.

## Proof idea
`rapp l acc = rev l ++ acc` by induction on `l` (with `app_assoc`); then
`fast_rev l = rev l ++ [] = rev l` by `app_nil_r`.

## Cost model
`func-ops`. Reference Rocq proof (`fast_rev_correct`, axiom-free):
[`targets/rocq/RevApp.v`](targets/rocq/RevApp.v).
