# Extended binary tree: leaves = internal + 1

## Claim
> `leaves t = S (internal t)`.

Knuth's extended-binary-tree identity: a tree with `n` internal nodes has `n+1` external nodes (leaves).

## Cost model
Reference Rocq proof (`leaves_internal`, axiom-free): [`targets/rocq/TreeLeaves.v`](targets/rocq/TreeLeaves.v).
