# Three-way mergesort: T(n)=3T(n/3)+n => n log_3 n

## Claim
> `T 0 = 0 -> (forall k, T (S k) <= 3 * T k + 3 ^ (S k)) -> forall k, T k <= k * 3 ^ k`.

## Cost model
Reference Rocq proof (`ternary_mergesort_recurrence`, axiom-free): [`targets/rocq/TernaryMerge.v`](targets/rocq/TernaryMerge.v).
