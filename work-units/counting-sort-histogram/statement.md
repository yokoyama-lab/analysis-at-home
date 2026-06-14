# Counting sort: buckets partition the input

## Claim
> `(forall x, In x l -> x < K) -> sumhist K l = length l`.

The correctness/linearity invariant of **distribution counting** (and hence radix sort): every key lands in exactly one of K buckets, so the histogram sums to n. Counting sort is comparison-free and runs in O(n + K) — it side-steps the Ω(n log n) lower bound (`decision-tree-leaves-bound`) by not comparing keys. Radix sort iterates this over d digit-passes.

## Cost model
Reference Rocq proof (`counting_sort_histogram`, axiom-free): [`targets/rocq/CountingSort.v`](targets/rocq/CountingSort.v).
