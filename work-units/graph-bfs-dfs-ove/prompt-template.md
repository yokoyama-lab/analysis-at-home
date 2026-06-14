<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that BFS/DFS is O(V+E): with edge_count and the visited bound, prove `NoDup visited -> (forall x, In x visited -> x < length g) -> length visited + edge_count g <= length g + edge_count g`. Mirror
`work-units/graph-bfs-dfs-ove/targets/rocq/BfsDfsOVE.v`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
