# concat distributes over append

## Claim
> `concat (ls1 ++ ls2) = concat ls1 ++ concat ls2`.

## Cost model
Reference Rocq proof (`list_concat_append`, axiom-free): [`targets/rocq/ConcatApp.v`](targets/rocq/ConcatApp.v).
