# Comparison-sort lower bound — height >= lg(n!)

> *TAOCP Vol. 3 §5.3.1.* The information-theoretic limit on comparison sorting,
> built on [`decision-tree-leaves-bound`](../decision-tree-leaves-bound/).

## Claim
A comparison sort is a binary **decision tree**; to sort `n` elements it must
distinguish all `n!` orderings, so it has at least `n!` leaves. A binary tree of
height `h` has at most `2^h` leaves (`leaves_le_pow_height`). Therefore

> **`comparison_sort_lower_bound`**: `fact n <= leaves t -> Nat.log2 (fact n) <= height t`.

The tree's height — the worst-case number of comparisons — is at least
`log2(n!)`, which is `Theta(n log n)`. No comparison sort beats `n lg n`.

## Proof idea
`fact n <= leaves t <= 2^height t`, then `Nat.log2` is monotone and
`log2 (2^h) = h`.

## Cost model
`func-ops`, `counts = ["comparison"]`. Reference Rocq proof
(`comparison_sort_lower_bound`, axiom-free):
[`targets/rocq/CompSortLB.v`](targets/rocq/CompSortLB.v).
