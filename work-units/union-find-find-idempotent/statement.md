# Union-Find: find returns a stable representative

## Claim
`find` computes a canonical representative of an element's set. Under the
invariant `parent[i] <= i`, it is **idempotent**:
> `find fuel p (find fuel p x) = find fuel p x`.

So `find x` is a fixed point (a root), and `find x = find y` is a sound test for
"same set" — the correctness property underlying union-find. Follows from
`find_reaches_root` (find lands on a root) and the fact that find of a root is
itself. With `union-find-rank-bound` (O(log n) depth) this is the full
cost+correctness picture for find.

Reference Rocq proof (`find_idempotent`, axiom-free): [`targets/rocq/UnionFindIdem.v`](targets/rocq/UnionFindIdem.v).
