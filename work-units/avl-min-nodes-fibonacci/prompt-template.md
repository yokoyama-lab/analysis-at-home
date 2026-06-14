<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that an AVL tree of height h has at least fib(h) nodes: define minnodes via the AVL recurrence and prove fib h <= minnodes h. Mirror
`work-units/avl-min-nodes-fibonacci/targets/rocq/AvlMinNodes.v`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
