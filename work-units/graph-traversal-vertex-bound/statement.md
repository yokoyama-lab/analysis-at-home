# Graph traversal visits at most |V| vertices

## Claim
A list of **distinct** vertices (`NoDup`), each `< n`, has length at most `n`:
> `NoDup l -> (forall x, In x l -> x < n) -> length l <= n`.

This is the pigeonhole bound behind the **O(V)** term of BFS/DFS: the algorithm's
`visited` set is distinct and drawn from `[0, |V|)`, so it marks each vertex at
most once and performs at most `|V|` expansions. (Proved via `NoDup_incl_length`
and `seq`.) Combined with `graph-edge-count` (the E term) this yields O(V+E)
(`graph-bfs-dfs-ove`).

Reference Rocq proof (`visited_vertex_bound`, axiom-free): [`targets/rocq/VertexBound.v`](targets/rocq/VertexBound.v).
