# BST insertion adds at most one node

## Claim
> `lsize (fst (insertc x t)) <= S (lsize t)`.

## Cost model
Reference Rocq proof (`bst_insert_size`, axiom-free): [`targets/rocq/BstInsertSize.v`](targets/rocq/BstInsertSize.v).
