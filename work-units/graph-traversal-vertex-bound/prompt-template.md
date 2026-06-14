<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, the visited-set bound: prove `NoDup l -> (forall x, In x l -> x < n) -> length l <= n` (pigeonhole; use NoDup_incl_length and seq). Mirror
`work-units/graph-traversal-vertex-bound/targets/rocq/VertexBound.v`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
