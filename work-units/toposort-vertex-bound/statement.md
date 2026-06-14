# Topological sort processes each vertex at most once

## Claim
We define a concrete Kahn-style topological sort on an adjacency-list graph (pop a
ready vertex; if already emitted, skip; else emit it and enqueue its successors)
and prove its output is distinct and bounded, so
> `length (kahn fuel g ready output) <= length g`.

Each vertex is emitted at most once — the **V term of the O(V+E)** cost (with
`graph-edge-count` providing the E term). Proved by the same method as
`dfs-expansions-bound`: the output stays `NoDup` (only unseen vertices are emitted)
and bounded (`< |V|`), then the pigeonhole `visited_vertex_bound` gives the bound.

## Cost model
`func-ops`, `counts = ["vertex-process"]`. Reference Rocq proof (`toposort_vertex_bound`, axiom-free):
[`targets/rocq/Toposort.v`](targets/rocq/Toposort.v).
