# filter distributes over append

## Claim
> `filter p (l1 ++ l2) = filter p l1 ++ filter p l2`.

## Cost model
Reference Rocq proof (`list_filter_append`, axiom-free): [`targets/rocq/FilterApp.v`](targets/rocq/FilterApp.v).
