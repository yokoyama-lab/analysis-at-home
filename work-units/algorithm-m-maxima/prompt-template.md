<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, the worst-case
register-update count of TAOCP Algorithm M. Mirror
`work-units/algorithm-m-maxima/targets/rocq/AlgorithmM.v`: define
`lr_changes cur l`, which scans l left to right with running maximum `cur` and
counts how many times the maximum is updated (one per element that exceeds the
current max). Prove `lr_changes cur l <= length l`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
