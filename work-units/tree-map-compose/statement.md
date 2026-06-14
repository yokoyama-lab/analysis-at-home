# Map fusion on trees

## Claim
> `map_tree g (map_tree f t) = map_tree (fun x => g (f x)) t`.

## Cost model
Reference Rocq proof (`tree_map_compose`, axiom-free): [`targets/rocq/TreeMapCompose.v`](targets/rocq/TreeMapCompose.v).
