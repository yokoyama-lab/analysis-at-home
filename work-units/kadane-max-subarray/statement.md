# Kadane's algorithm — maximum subarray sum in O(n)

> *Bentley, Programming Pearls.* `Theta(n^2)` subarrays, solved in one linear pass.

## Claim
Running variables `cur` (best sum of a subarray ending at the front; `>= 0`,
the empty subarray allowed) and `best` (best over **all** contiguous subarrays):

```
cur  (x::r) = max 0 (x + cur r)
best (x::r) = max (cur (x::r)) (best r)
```

With `window i k l = firstn k (skipn i l)` and `Zsum` the integer sum,

> **`kadane_correct`**:
> `(forall i k, Zsum (window i k l) <= snd (kadane l))`  — best bounds every subarray,
> `(exists i k, snd (kadane l) = Zsum (window i k l))`  — and it is attained.

Together: `best l` is **exactly** the maximum contiguous-subarray sum, computed in
`O(n)`.

## Proof idea
Two structural inductions: every prefix sum `<= cur` and `cur` is some prefix
sum (`prefix_le_cur`, `cur_attained`); then every window `<= best` and `best` is
some window (`sub_le_best`, `best_attained`), splitting a window into "starts at
the head" (a prefix, bounded by `cur`) or "lies in the tail" (the IH).

## Cost model
`func-ops`, `counts = ["add", "max"]`. Reference Rocq proof (`kadane_correct`,
axiom-free): [`targets/rocq/Kadane.v`](targets/rocq/Kadane.v).
