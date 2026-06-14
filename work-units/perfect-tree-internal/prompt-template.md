<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that a perfect binary tree of height h has 2^h - 1 internal nodes: prove `S (internal (pt h)) = 2 ^ h`. Mirror
`work-units/perfect-tree-internal/targets/rocq/PerfectTreeInternal.v`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
