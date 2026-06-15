# Dynamic array (table doubling) — push is amortized O(1)

> *CLRS §17.4; the amortized-analysis sibling of
> [`binary-counter-increments`](../binary-counter-increments/).*

## Claim
A dynamic array doubles its capacity when full. A push writes one element
(cost 1); when `size = capacity` it first copies the `capacity` existing
elements, then doubles. `da_cost n s c` is the total cost of `n` pushes starting
at size `s`, capacity `c`. Then

> **`dynamic_array_amortized`**: `da_cost n 0 1 <= 3 * n`.

Each push costs `3` amortized, even though a single resize is `O(n)`: the
expensive copy is paid for by the cheap pushes before it.

## Proof idea
The **potential method** with `Phi = 2*size - capacity`. The invariant
`1 <= c`, `c/2 <= size <= c` makes the amortized cost (actual + ΔPhi) exactly `3`
for both a plain push and a resize-push. The strengthened lemma
`da_cost n s c + c <= 3*n + 2*s + 1` falls to induction + `lia`. The underlying
fact is the geometric series `1 + 2 + 4 + ... + 2^k < 2^(k+1)`.

## Cost model
`func-ops`, `counts = ["write", "copy"]`. Reference Rocq proof
(`dynamic_array_amortized`, axiom-free):
[`targets/rocq/DynArray.v`](targets/rocq/DynArray.v).
