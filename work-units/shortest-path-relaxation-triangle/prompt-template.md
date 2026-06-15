<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that a relaxed edge satisfies the triangle inequality: prove `v < length d -> nth v (relax d u v w) 0 <= nth u d 0 + w`. Mirror
`work-units/shortest-path-relaxation-triangle/targets/rocq/RelaxTri.v`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
