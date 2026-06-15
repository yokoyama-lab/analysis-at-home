# DFS is complete: it visits every reachable vertex

## Claim
For the worklist DFS (returning both `visited` and the leftover stack), if the run
**drains the stack** (`snd (dfs2 fuel g src []) = []`, i.e. it had enough fuel),
then every vertex reachable from the frontier `src` is in the result:
> `snd (dfs2 fuel g src []) = [] -> reach g src v -> In v (fst (dfs2 fuel g src []))`.

## Proof structure
1. `dfs2_inv` (closure invariant): every edge-target of a visited vertex stays
   visited-or-pending; on an empty leftover stack this means `visited` is **closed
   under edges**.
2. `dfs2_src`: every frontier vertex ends up visited (when the stack drains).
3. Induction on `reach`: `src ⊆ visited` (base) and closure (step) give
   `reach ⊆ visited`.

Together with `dfs-soundness` (`visited ⊆ reach`) this pins the visited set to
exactly the reachable vertices, and with `dfs-expansions-bound` / `graph-edge-count`
it completes the DFS analysis (correctness **and** O(V+E) cost).

Reference Rocq proof (`dfs_complete`, axiom-free): [`targets/rocq/DfsComplete.v`](targets/rocq/DfsComplete.v).
