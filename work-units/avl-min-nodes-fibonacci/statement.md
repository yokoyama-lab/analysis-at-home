# AVL trees are balanced: min nodes >= Fibonacci

## Claim
The minimum number of nodes in an AVL tree of height `h` obeys `N(h)=1+N(h-1)+N(h-2)` (worst-case subtree heights h-1, h-2). We prove it is bounded below by the Fibonacci numbers:
> `fib h <= minnodes h`.

Since `fib h ~ phi^h`, an AVL tree with `n` nodes has height `O(log n)` (TAOCP Vol. 3 §6.2.3; AVL 1962).

Reference Rocq proof (`avl_min_nodes`, axiom-free): [`targets/rocq/AvlMinNodes.v`](targets/rocq/AvlMinNodes.v).
