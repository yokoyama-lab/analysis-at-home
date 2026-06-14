# Exact comparison count of selection sort

## Claim

Selection sort on a list of length `n` performs **exactly** `n(n−1)/2` key
comparisons — independent of the data (unlike insertion sort, there is no
best/worst case). Division-free form:

> `2 · comparisons l = length l · (length l − 1)`.

## Cost model

`func-ops`, `counts = ["comparison"]`. The reference cost model and a complete
Rocq proof (`selection_sort_comparisons_exact`, axiom-free) are in
[`targets/rocq/SelectionSortComparisons.v`](targets/rocq/SelectionSortComparisons.v):
`select` finds the minimum using exactly `|l|` comparisons; `ssort` sums them;
`Σ_{i<n} i = n(n−1)/2`.

This is the project's first **exact closed form** (an equality, not a bound) and
contrasts cleanly with the data-dependent insertion-sort unit.

## References

Pointers only — do not copy prose into the corpus.
- Knuth, *TAOCP* Vol. 3 (selection sort comparison count).
