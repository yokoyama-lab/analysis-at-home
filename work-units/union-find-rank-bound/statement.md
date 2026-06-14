# Union by rank is balanced: rank-r tree has 2^r nodes

## Claim
In a disjoint-set forest with **union by rank**, merging two rank-`r` trees yields
a rank-`(r+1)` tree, so the minimum number of elements obeys `N(r) = 2*N(r-1)`,
`N(0)=1`. We prove
> `uf_minsize r = 2 ^ r`.

Hence a rank-`r` tree has **at least `2^r` elements**, so with `n` elements the rank
(and therefore the `find` path length without compression) is at most `lg n` —
`find`/`union` run in `O(log n)`. (Analogous to `avl-min-nodes-fibonacci`; the full
inverse-Ackermann bound with path compression is a much harder separate result.)

## Cost model
`func-ops`, `counts = ["node"]`. Reference Rocq proof (`union_find_rank_bound`, axiom-free):
[`targets/rocq/UnionFindRank.v`](targets/rocq/UnionFindRank.v).
