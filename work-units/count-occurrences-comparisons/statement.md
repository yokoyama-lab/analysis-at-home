# Exact comparison count of counting occurrences

## Claim
Counting how many times `x` occurs in a list of length `n` uses **exactly `n`**
comparisons:
> `snd (countc x l) = length l`.

## Cost model
`func-ops`, `counts = ["comparison"]`. Reference Rocq proof
(`count_occurrences_comparisons`, axiom-free):
[`targets/rocq/CountOccurrences.v`](targets/rocq/CountOccurrences.v).
