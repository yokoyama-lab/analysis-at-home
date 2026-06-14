# Filtering a list uses n predicate tests

## Claim
> `snd (filterc p l) = length l`.

## Cost model
`func-ops`, `counts = ["predicate-test"]`. Reference Rocq proof (`filter_tests`, axiom-free): [`targets/rocq/ListFilter.v`](targets/rocq/ListFilter.v).
