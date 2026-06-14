# Un-memoized doubling recursion is exponential

## Claim
> `T 0 = 0 -> (forall k, T (S k) = 2 * T k + 1) -> forall k, T k + 1 = 2 ^ k`.

## Cost model
Reference Rocq proof (`naive_recursion_exponential`, axiom-free): [`targets/rocq/NaiveRec.v`](targets/rocq/NaiveRec.v).
