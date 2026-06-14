<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that a binary tree has one more leaf than internal nodes: with `Lf` leaves and `Nd` internal nodes, prove `leaves t = S (internal t)`. Mirror
`work-units/tree-leaves-internal/targets/rocq/TreeLeaves.v`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
