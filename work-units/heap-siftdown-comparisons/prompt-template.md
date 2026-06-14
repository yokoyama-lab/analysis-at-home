<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that heap sift-down uses at most 2·height comparisons: model the worst-case descent cost on a binary tree and prove `sift t <= 2 * height t`. Mirror
`work-units/heap-siftdown-comparisons/targets/rocq/HeapSift.v`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
