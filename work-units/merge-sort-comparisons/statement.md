# O(n log n) comparison count of merge sort

## Claim

Merge sort sorts using `O(n log n)` comparisons. Stated with an explicit level
budget `k` (avoiding `log` in the statement):

> `length l ≤ 2^k  →  comparisons k l ≤ k · length l`.

Taking the least such `k = ⌈log₂ n⌉` gives the familiar `n⌈log₂ n⌉` bound.

## Cost model

`func-ops`, `counts = ["comparison"]`. The reference model and a complete Rocq
proof (`merge_sort_comparisons_nlogn`, axiom-free) are in
[`targets/rocq/MergeSortComparisons.v`](targets/rocq/MergeSortComparisons.v).
Key lemmas: `split` is balanced (each half `≤ 2^{k-1}`) and length-total; `merge`
costs `≤ |l1|+|l2|` and preserves length; the level induction gives
`(k−1)·n + n = k·n`.

This is the project's first **divide-and-conquer / `n log n`** result — the
recurrence `T(n) ≤ 2T(n/2) + n` made machine-checked.

## References

Pointers only.
- Knuth, *TAOCP* Vol. 3 (merge sort).
