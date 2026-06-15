# Boyer-Moore majority vote — O(n) time, O(1) space

> *Boyer & Moore, 'MJRTY' (1981).* A strict majority element found in **one pass**
> with a single counter.

## Claim
Maintain a `(candidate, count)` pair; `step (c,0) a = (a,1)`, and
`step (c, S k) a = (c, S (S k))` if `a = c`, else `(c, k)`. Run it left to right
with `fold_left`. Then

> **`boyer_moore_majority`**: `length l < 2 * cnt m l -> fst (bm l) = m`.

If any value `m` occupies **more than half** the list, the surviving candidate is
exactly `m` — using `O(1)` extra space and `O(n)` time.

## Proof idea
The cancellation invariant over every processed prefix, with candidate `c` and
count `k`:

- **(A)** for every `x <> c`: `2 * cnt x prefix + k <= length prefix`;
- **(B)** `2 * cnt c prefix <= length prefix + k`.

Maintained by induction on the prefix (`rev_ind`). At the end, (A) says every
non-candidate occupies at most half the list, so a strict majority cannot be a
non-candidate — it must be the candidate.

## Cost model
`func-ops`, `counts = ["comparison"]`. Reference Rocq proof
(`boyer_moore_majority`, axiom-free):
[`targets/rocq/BoyerMoore.v`](targets/rocq/BoyerMoore.v).
