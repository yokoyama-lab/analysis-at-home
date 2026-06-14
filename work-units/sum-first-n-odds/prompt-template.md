<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that the sum of the first n odd numbers is n^2: define `oddsum n = 1+3+...+(2n-1)` and prove `oddsum n = n * n`. Mirror
`work-units/sum-first-n-odds/targets/rocq/OddSum.v`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
