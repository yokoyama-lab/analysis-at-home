# Misra-Gries — heavy hitters with k-1 counters

> *Misra & Gries (1982).* The generalization of
> [`boyer-moore-majority`](../boyer-moore-majority/) from majority (`n/2`) to every
> element above `n/k`.

## Claim
Keep a dictionary of at most `k-1` `(item, count)` pairs. For each stream element
`a`: increment `a` if stored; else store `(a,1)` if there is room; else decrement
**every** stored count by 1, dropping any that reach 0. After the pass,

> **`misra_gries`**: `2 <= k -> length l < k * cnt m l -> 0 < getc m (mg k l)`.

Every element occupying **more than a `1/k` fraction** of the stream still holds a
positive counter — found with only `k-1` counters and one pass. (`k = 2` is
Boyer-Moore majority.)

## Proof idea
The generalized cancellation invariant over the processed prefix, with `D` the
number of decrement steps:

- `cnt x prefix <= getc x dict + D` (a stored count under-counts by at most `D`);
- `total dict + k * D = length prefix` (each decrement cancels `k` units).

The second gives `k * D <= length l`; combined with `length l < k * cnt m l` we
get `D < cnt m l`, so `getc m dict >= cnt m l - D > 0`.

## Cost model
`func-ops`. Reference Rocq proof (`misra_gries`, axiom-free):
[`targets/rocq/MisraGries.v`](targets/rocq/MisraGries.v).
