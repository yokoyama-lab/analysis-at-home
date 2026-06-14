# List append uses |l1| operations

## Claim
> `snd (appendc l1 l2) = length l1`.

## Cost model
`func-ops`, `counts = ["cons"]`. Reference Rocq proof (`append_operations`, axiom-free): [`targets/rocq/ListAppend.v`](targets/rocq/ListAppend.v).
