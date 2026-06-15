# Union-Find: find terminates at a root

## Claim
Modelling a disjoint-set forest by a parent array `p` (a root `r` has `p[r]=r`),
`find` follows parent pointers. Under the structural invariant that **parents
point to a not-larger index** (`forall i, nth i p i <= i` — true for union by rank
with the smaller index as root), `find` with enough fuel returns a **root**:
> `(forall i, nth i p i <= i) -> x <= fuel -> nth (find fuel p x) p (find fuel p x) = find fuel p x`.

The parent index strictly decreases at each non-root step, so the search
terminates at a fixed point. Combined with `union-find-rank-bound` (rank ≤ lg n),
this gives `find` running in `O(log n)`.

Reference Rocq proof (`find_reaches_root`, axiom-free): [`targets/rocq/UnionFindFind.v`](targets/rocq/UnionFindFind.v).
