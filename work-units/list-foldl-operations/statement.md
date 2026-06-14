# Left fold uses n applications

## Claim
> `snd (foldlc f acc l) = length l`.

## Cost model
Reference Rocq proof (`list_foldl_operations`, axiom-free): [`targets/rocq/ListFoldl.v`](targets/rocq/ListFoldl.v).
