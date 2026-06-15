# Merge of two sorted lists — full correctness

> The heart of merge sort (TAOCP Vol. 3 §5.2.4); cost counted in
> [`merge-comparisons`](../merge-comparisons/).

## Claim
`merge` is fuel-bounded (the total length strictly decreases). Then

> **`merge_correct`**: `Sorted l1 -> Sorted l2 -> length l1 + length l2 <= fuel ->`
> `Sorted (merge fuel l1 l2) /\ Permutation (merge fuel l1 l2) (l1 ++ l2)`.

The output is sorted **and** a permutation of `l1 ++ l2`.

## Proof idea
Sortedness carries a lower bound `le_hd z` through the recursion (the emitted
head stays ≥ everything before it); the permutation uses `perm_skip` and
`Permutation_middle`.

## Cost model
`func-ops`, `counts = ["comparison"]`. Reference Rocq proof (`merge_correct`,
axiom-free): [`targets/rocq/Merge.v`](targets/rocq/Merge.v).
