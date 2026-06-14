# Binary search tree — comparisons bounded by height

> *TAOCP Vol. 3 §6.2.2 (tree search); §6.2.1 (binary search).*

## Claim
Searching a binary search tree for `x` performs at most `height t` key
comparisons — one per level on the root-to-node search path:
> `snd (search x t) <= height t`.

## Corollary (the binary-search bound)
A **balanced** BST on `n` keys has height `O(log n)`, so search costs `O(log n)`
comparisons — exactly Knuth's binary-search bound `⌊lg n⌋ + 1`. This unit proves
the structural heart (cost ≤ height); the balancedness ⇒ `log n` fact is a
separate (queued) unit.

## Cost model
`func-ops`, `counts = ["comparison"]`. Reference Rocq proof
(`bst_search_comparisons`, axiom-free):
[`targets/rocq/BstSearch.v`](targets/rocq/BstSearch.v).
