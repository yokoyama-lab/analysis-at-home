<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that Union-Find's find terminates at a root: with the invariant nth i p i <= i, prove `x <= fuel -> nth (find fuel p x) p (find fuel p x) = find fuel p x`. Mirror
`work-units/union-find-find-root/targets/rocq/UnionFindFind.v`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
