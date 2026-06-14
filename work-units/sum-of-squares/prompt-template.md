<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, the sum-of-squares identity: define `sumsq n = 1^2+...+n^2` and prove `6 * sumsq n = n * (n + 1) * (2 * n + 1)`. Mirror
`work-units/sum-of-squares/targets/rocq/SumSquares.v`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
