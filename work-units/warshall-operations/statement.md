# Warshall transitive closure does V^3 operations

## Claim
> `loop v (loop v (loop v 1)) = v * v * v`.

## Cost model
Reference Rocq proof (`warshall_operations`, axiom-free): [`targets/rocq/Warshall.v`](targets/rocq/Warshall.v).
