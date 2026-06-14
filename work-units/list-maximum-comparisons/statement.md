# Exact comparison count of list maximum

## Claim
Finding the maximum of a list of length `n` uses **exactly `n − 1`** comparisons:

> `snd (maxc l) = length l − 1`.

`maxc` returns the maximum together with the comparison count (one `x <=? m`
test per element after the first).

## Cost model
`func-ops`, `counts = ["comparison"]`. Reference Rocq proof
(`list_maximum_comparisons`, axiom-free):
[`targets/rocq/ListMaximum.v`](targets/rocq/ListMaximum.v).
