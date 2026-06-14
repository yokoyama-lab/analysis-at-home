# Linear multiplication count of naive exponentiation

## Claim
Naive exponentiation `b^e` by repeated multiplication uses **exactly `e`**
multiplications:

> `snd (powc b e) = e`,

with a correctness companion `fst (powc b e) = b ^ e` (proved on the Rocq
target). This pairs with [`fast-exponentiation-mults`](../fast-exponentiation-mults/)
(≤ 2·bits) to make the naive-vs-fast cost gap machine-checked.

## Cost model
`func-ops`, `counts = ["multiplication"]`. Reference Rocq proof
(`naive_power_mults`, axiom-free):
[`targets/rocq/NaivePower.v`](targets/rocq/NaivePower.v).
