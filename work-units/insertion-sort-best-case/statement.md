# Best-case comparison count of insertion sort

## Claim
Sorting a list of length `n` by insertion sort performs **at least `n − 1`** key
comparisons:
> `length l <= S (comparisons l)`   (i.e. `comparisons l ≥ length l − 1`, in `nat`).

One comparison is needed to place each element after the first into a non-empty
sorted prefix. The bound is **achieved by an already-sorted input** (each insert
stops at the first comparison). Paired with
[`insertion-sort-comparisons`](../insertion-sort-comparisons/) (worst case
`2·c ≤ n(n−1)`), it brackets insertion sort between a **linear** best case and a
**quadratic** worst case — the canonical cost-of-input-order story.

## Cost model
`func-ops`, `counts = ["comparison"]`. Same instrumented `insert`/`isort` as the
worst-case unit. Reference Rocq proof (`insertion_sort_best_case`, axiom-free):
[`targets/rocq/InsertionSortBestCase.v`](targets/rocq/InsertionSortBestCase.v).
