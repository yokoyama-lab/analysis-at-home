<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that searching a
binary search tree costs at most height-many comparisons. Mirror
`work-units/bst-search-comparisons/targets/rocq/BstSearch.v`: define a binary
`tree`, its `height`, and `search x t` returning (found, #comparisons) — one
comparison per node, recursing left/right by `<`. Prove
`snd (search x t) <= height t`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
