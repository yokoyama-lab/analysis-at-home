# List reversal uses n operations

## Claim
Reversing a list of length `n` (into an accumulator) uses exactly `n` cons operations:
> `snd (rev_list l) = length l`.

## Cost model
`func-ops`, `counts = ["cons"]`. Reference Rocq proof (`reverse_operations`, axiom-free): [`targets/rocq/ListReverse.v`](targets/rocq/ListReverse.v).
