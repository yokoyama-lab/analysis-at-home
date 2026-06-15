<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that path compression gives one-step find: with upd p x r setting p[x]:=r, prove `x < length p -> find 1 (upd p x r) x = r`. Mirror
`work-units/union-find-path-compression/targets/rocq/PathCompression.v`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
