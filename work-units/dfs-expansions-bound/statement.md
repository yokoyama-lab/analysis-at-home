# A concrete DFS does at most |V| vertex expansions

## Claim
We define an actual fuel-bounded DFS on an adjacency-list graph `g` (pop a vertex;
if visited, skip; else mark it and push its neighbours) and prove it expands each
vertex at most once. Concretely, if the graph's neighbours, the initial stack, and
the initial visited list are all valid vertices (`< length g`), then
> `length (dfs fuel g stack visited) <= length g`.

## Proof structure
1. `dfs_visited_nodup`: the visited set stays `NoDup` (we only add an unvisited v).
2. `dfs_visited_bounded`: visited entries stay `< |V|` (neighbours of a valid
   vertex are valid, via `nth_In` / `nth_overflow`).
3. `visited_vertex_bound` (pigeonhole): `NoDup` + bounded `=> length <= |V|`.

This is the **V term of O(V+E) for a real algorithm** (not just an abstract set);
with `graph-edge-count` (the E term) and `graph-bfs-dfs-ove` it completes the
depth-first-search cost analysis. (A full termination/reachability-correctness
proof is a further effort.)

Reference Rocq proof (`dfs_expansions_le_V`, axiom-free): [`targets/rocq/DfsBound.v`](targets/rocq/DfsBound.v).
