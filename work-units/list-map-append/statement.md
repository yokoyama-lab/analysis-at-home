# map distributes over append

## Claim
> `map f (l1 ++ l2) = map f l1 ++ map f l2`.

## Cost model
Reference Rocq proof (`list_map_append`, axiom-free): [`targets/rocq/MapApp.v`](targets/rocq/MapApp.v).
