# Exact comparison count of list minimum

## Claim
Finding the minimum of a list of length `n` uses **exactly `n − 1`** comparisons:
> `snd (minc l) = length l − 1`.

## Cost model
`func-ops`, `counts = ["comparison"]`. Reference Rocq proof
(`list_minimum_comparisons`, axiom-free):
[`targets/rocq/ListMinimum.v`](targets/rocq/ListMinimum.v).
