# BST insertion uses at most height+1 comparisons

## Claim
> `snd (insertc x t) <= S (lheight t)`.

## Cost model
Reference Rocq proof (`bst_insert_comparisons`, axiom-free): [`targets/rocq/BstInsert.v`](targets/rocq/BstInsert.v).
