# Map fusion: map g (map f l) = map (g . f) l

## Claim
> `map g (map f l) = map (fun x => g (f x)) l`.

## Cost model
Reference Rocq proof (`map_fusion`, axiom-free): [`targets/rocq/MapFusion.v`](targets/rocq/MapFusion.v).
