<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that Union-Find's find is idempotent: with the invariant nth i p i <= i, prove `find fuel p (find fuel p x) = find fuel p x` (find lands on a root, and find of a root is itself). Mirror
`work-units/union-find-find-idempotent/targets/rocq/UnionFindIdem.v`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
