<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that mirroring a binary tree performs one operation per internal node: `mirrorc t` returns (mirrored, #ops); prove `snd (mirrorc t) = internal t`. Mirror
`work-units/tree-mirror-operations/targets/rocq/TreeMirror.v`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
