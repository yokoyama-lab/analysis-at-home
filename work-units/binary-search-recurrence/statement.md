# Binary search recurrence: T(n)=T(n/2)+1 => lg n probes

## Claim
> `T 0 = 0 -> (forall k, T (S k) = T k + 1) -> forall k, T k = k`.

## Cost model
Reference Rocq proof (`binary_search_recurrence`, axiom-free): [`targets/rocq/BinSearchRec.v`](targets/rocq/BinSearchRec.v).
