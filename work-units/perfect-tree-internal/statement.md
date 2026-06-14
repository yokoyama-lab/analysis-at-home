# Perfect binary tree of height h has 2^h - 1 internal nodes

## Claim
> `S (internal (pt h)) = 2 ^ h`.

Stated in nat without subtraction; together with `perfect-tree-leaves` it gives total nodes `2^(h+1) - 1`.

## Cost model
Reference Rocq proof (`perfect_tree_internal`, axiom-free): [`targets/rocq/PerfectTreeInternal.v`](targets/rocq/PerfectTreeInternal.v).
