# Best-case comparison count of linear search

## Claim
On a **non-empty** list, linear search performs **at least one** key comparison:
> `1 <= length l -> 1 <= snd (lsearch x l)`.

This is the universal lower bound over all inputs of size `n ≥ 1`; it is achieved
exactly when the target sits in the head position. Paired with
[`linear-search-comparisons`](../linear-search-comparisons/) (worst case `≤ n`),
it brackets the cost on non-empty inputs: `1 ≤ cost ≤ n`.

## Cost model
`func-ops`, `counts = ["comparison"]`. Reference Rocq proof
(`linear_search_best_case`, axiom-free):
[`targets/rocq/LinearSearchBestCase.v`](targets/rocq/LinearSearchBestCase.v).
