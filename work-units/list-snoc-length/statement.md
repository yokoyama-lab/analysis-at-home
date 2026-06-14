# Appending one element increments the length

## Claim
> `length (l ++ [x]) = S (length l)`.

## Cost model
Reference Rocq proof (`list_snoc_length`, axiom-free): [`targets/rocq/SnocLen.v`](targets/rocq/SnocLen.v).
