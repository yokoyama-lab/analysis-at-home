# Leaves-dominate divide-and-conquer is n^2

## Claim
> `T 0 = 0 -> (forall k, T (S k) <= 4 * T k + 2 ^ (S k)) -> forall k, T k + 2 ^ k <= 4 ^ k`.

## Cost model
Reference Rocq proof (`master_leaves_dominate`, axiom-free): [`targets/rocq/MasterLeaves.v`](targets/rocq/MasterLeaves.v).
