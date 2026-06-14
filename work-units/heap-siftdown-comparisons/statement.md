# Heap sift-down uses at most 2·height comparisons

## Claim
> `sift t <= 2 * height t`.

Sift-down descends the heap one level at a time, doing at most two comparisons per level, so for a balanced heap on n keys it is O(log n) — the per-operation cost behind heapsort.

## Cost model
Reference Rocq proof (`heap_siftdown_comparisons`, axiom-free): [`targets/rocq/HeapSift.v`](targets/rocq/HeapSift.v).
