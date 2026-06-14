# Binary search uses at most ⌊lg n⌋+1 comparisons

## Claim
> `n < 2 ^ k -> bsearch fuel n <= k`.

Each probe halves the sorted region; if it holds fewer than 2^k keys, at most k comparisons are made. The minimal such k is ⌊lg n⌋+1.

## Cost model
Reference Rocq proof (`binary_search_comparisons`, axiom-free): [`targets/rocq/BinarySearch.v`](targets/rocq/BinarySearch.v).
