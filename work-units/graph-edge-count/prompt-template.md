<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that in an adjacency-list graph the total adjacency entries equal the edge count: define edge_count and prove `edge_count g = length (concat g)`. Mirror
`work-units/graph-edge-count/targets/rocq/GraphEdges.v`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
