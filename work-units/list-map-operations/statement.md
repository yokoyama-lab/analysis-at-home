# Mapping over a list uses n applications

## Claim
> `snd (mapc f l) = length l`.

## Cost model
`func-ops`, `counts = ["application"]`. Reference Rocq proof (`map_operations`, axiom-free): [`targets/rocq/ListMap.v`](targets/rocq/ListMap.v).
