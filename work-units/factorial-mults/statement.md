# Exact multiplication count of factorial

## Claim
Computing `n!` by repeated multiplication uses **exactly `n − 1`** multiplications:
> `snd (factc n) = n − 1`.

## Cost model
`func-ops`, `counts = ["multiplication"]`. Reference Rocq proof
(`factorial_mults`, axiom-free): [`targets/rocq/Factorial.v`](targets/rocq/Factorial.v).
