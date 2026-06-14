# Geometric recursion: a calls/level => a^k subproblems

## Claim
> `M 0 = 1 -> (forall k, M (S k) = a * M k) -> forall k, M k = a ^ k`.

## Cost model
Reference Rocq proof (`geometric_recursion_count`, axiom-free): [`targets/rocq/GeomRec.v`](targets/rocq/GeomRec.v).
