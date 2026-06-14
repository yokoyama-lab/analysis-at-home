# Right fold uses n applications

## Claim
> `snd (foldrc f b l) = length l`.

## Cost model
Reference Rocq proof (`list_foldr_operations`, axiom-free): [`targets/rocq/ListFoldr.v`](targets/rocq/ListFoldr.v).
