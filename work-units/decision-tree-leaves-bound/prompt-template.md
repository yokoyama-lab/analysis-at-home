<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, the comparison-sort lower-bound core: a binary tree of height h has at most 2^h leaves. Prove `leaves t <= 2 ^ height t`. Mirror
`work-units/decision-tree-leaves-bound/targets/rocq/DecisionTree.v`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
