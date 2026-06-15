# Binary search — sound and complete

> Correctness companion to [`binary-search-comparisons`](../binary-search-comparisons/)
> (the ⌊lg n⌋+1 comparison count).

## Claim
Over a **monotone** array `a` (`i ≤ j → a i ≤ a j`), binary search on the index
window `[lo, hi)`:

> **`bsearch_correct`**: `monotone a → hi − lo ≤ fuel →`
> `(bsearch fuel a key lo hi = true ↔ ∃ i, lo ≤ i < hi ∧ a i = key)`.

## Proof idea
- **Soundness** (`→`): a `true` verdict is reached only at an index where
  `a mid = key`, or in a sub-window — so a witness exists (no monotonicity used).
- **Completeness** (`←`): if `a i = key` and `a mid < key`, monotonicity forces
  `i > mid` (else `a i ≤ a mid < key = a i`), so the key stays in the recursed
  half; symmetrically for `a mid > key`.

## Cost model
`func-ops`, `counts = ["comparison"]`. Reference Rocq proof (`bsearch_correct`,
axiom-free): [`targets/rocq/BSearch.v`](targets/rocq/BSearch.v).
