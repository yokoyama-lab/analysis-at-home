# Comparison bound of ordered insertion

## Claim
Inserting one element into a list of length `n` (the inner step of insertion
sort) uses **at most `n`** comparisons:

> `snd (insert x l) ≤ length l`.

`insert` returns the new list together with the comparison count (one `x <=? y`
test per element scanned, stopping once the insertion point is found).

## Cost model
`func-ops`, `counts = ["comparison"]`. Reference Rocq proof
(`ordered_insertion_comparisons`, axiom-free):
[`targets/rocq/OrderedInsertion.v`](targets/rocq/OrderedInsertion.v).
