# Adjacent dedup uses n-1 comparisons

## Claim
> `dedupc l = pred (length l)`.

## Cost model
Reference Rocq proof (`list_dedup_comparisons`, axiom-free): [`targets/rocq/ListDedup.v`](targets/rocq/ListDedup.v).
