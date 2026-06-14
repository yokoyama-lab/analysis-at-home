# BFS/DFS runs in O(V+E)

## Claim
For a graph `g` stored as adjacency lists (so `|V| = length g`, `|E| = edge_count g`),
any traversal whose `visited` set is distinct and drawn from `[0, |V|)` has cost
> `length visited + edge_count g <= length g + edge_count g`,

i.e. **expansions (≤ |V|) + edge-scans (= |E|) ≤ |V| + |E|**. The two pillars are
`graph-traversal-vertex-bound` (the visited set bounds expansions by |V|) and
`graph-edge-count` (each adjacency entry is one edge-scan). Together they give the
canonical **O(V+E)** cost of BFS/DFS.

The full stateful worklist algorithm (queue/stack, visited-marking, termination) is
a larger separate effort; this unit captures the cost bound it satisfies.

Reference Rocq proof (`bfs_dfs_OVE`, axiom-free): [`targets/rocq/BfsDfsOVE.v`](targets/rocq/BfsDfsOVE.v).
