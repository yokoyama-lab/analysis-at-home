# Worst-case comparison count of linear search

## Claim

Linear search over a list of length `n` performs **at most `n`** key
comparisons:

> `snd (lsearch x l) ≤ length l`.

(`lsearch` returns whether `x` was found together with the comparison count: one
`x =? y` test per element, stopping at the first match.)

## Cost model

`func-ops`, `counts = ["comparison"]`. Reference Rocq proof
(`linear_search_comparisons`, axiom-free):
[`targets/rocq/LinearSearch.v`](targets/rocq/LinearSearch.v). A
found-iff-`In x l` correctness companion is a natural open follow-up.

## References
Classic worst-case linear bound.
