# Floyd's build-heap is O(n)

> *TAOCP Vol. 3 §5.2.3.* The classic surprise: building a heap bottom-up is
> **linear**, not `n log n`.

## Claim
Sift-down at a node of height `j` costs `O(j)`. Summed over a perfect binary tree
of height `h`, the total work is `sheight h` (sum of all node heights), where
`sheight (S h') = S h' + 2 * sheight h'`. The total node count is
`nodes h = 2^(h+1) - 1`. Then

> **`build_heap_identity`**: `sheight h + h + 1 = nodes h`,
>
> **`build_heap_le_nodes`**: `sheight h <= nodes h`.

Total sift-down work is at most the number of nodes — `O(n)`. (Contrast inserting
elements one by one, which is `O(n log n)`.) The reason is the convergent series
`sum_{j>=1} j / 2^j = 2`: the many low nodes are cheap, the few high nodes are
rare.

## Proof idea
Structural induction on `h`; both `nodes` and `sheight` are simple recurrences, so
the identity falls to `lia` at each step. `nodes_pow` records `nodes h + 1 = 2^(h+1)`.

## Cost model
`func-ops`, `counts = ["comparison", "swap"]`. Reference Rocq proof
(`build_heap_identity`, `build_heap_le_nodes`, axiom-free):
[`targets/rocq/BuildHeap.v`](targets/rocq/BuildHeap.v).
