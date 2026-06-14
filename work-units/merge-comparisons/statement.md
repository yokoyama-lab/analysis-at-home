# Merging two lists uses at most |l1|+|l2| comparisons

## Claim
> `mergec fuel l1 l2 <= length l1 + length l2`.

## Cost model
Reference Rocq proof (`merge_comparisons`, axiom-free): [`targets/rocq/MergeComp.v`](targets/rocq/MergeComp.v).
