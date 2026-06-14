# Adjacency entries = number of edges (the E in O(V+E))

## Claim
A directed graph stored as adjacency lists `g : list (list nat)` (with `g[v]` the
out-neighbours of vertex `v`) has `|V| = length g` vertices and a number of edges
equal to the total adjacency entries:
> `edge_count g = length (concat g)`.

This is the structural basis of the **O(V+E)** cost of BFS/DFS: a traversal that
visits each vertex once and scans each adjacency entry once does `length g`
vertex-steps plus `edge_count g` edge-steps. (Opening the graph domain; full
BFS/DFS with a visited set is a larger separate unit.)

## Reference Rocq proof
(`handshake_edges`, axiom-free): [`targets/rocq/GraphEdges.v`](targets/rocq/GraphEdges.v).
