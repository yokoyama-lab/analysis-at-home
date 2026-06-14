# Balanced divide-and-conquer is n log_b n

## Claim
> `T 0 = 0 -> (forall k, T (S k) <= b * T k + b ^ (S k)) -> forall k, T k <= k * b ^ k`.

## Cost model
Reference Rocq proof (`general_dc_nlogn`, axiom-free): [`targets/rocq/GeneralDC.v`](targets/rocq/GeneralDC.v).
