<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that a Kahn-style topological sort emits each vertex at most once: define kahn (skip if already output, else emit + enqueue successors), prove the output stays NoDup and bounded, and conclude `length (kahn fuel g ready output) <= length g`. Mirror
`work-units/toposort-vertex-bound/targets/rocq/Toposort.v`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
