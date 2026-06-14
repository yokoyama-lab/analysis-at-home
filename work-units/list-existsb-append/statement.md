# existsb distributes over append

## Claim
> `existsb p (l1 ++ l2) = existsb p l1 || existsb p l2`.

## Cost model
Reference Rocq proof (`list_existsb_append`, axiom-free): [`targets/rocq/ExistsbApp.v`](targets/rocq/ExistsbApp.v).
