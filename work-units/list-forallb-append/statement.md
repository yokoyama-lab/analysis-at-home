# forallb distributes over append

## Claim
> `forallb p (l1 ++ l2) = forallb p l1 && forallb p l2`.

## Cost model
Reference Rocq proof (`list_forallb_append`, axiom-free): [`targets/rocq/ForallbApp.v`](targets/rocq/ForallbApp.v).
