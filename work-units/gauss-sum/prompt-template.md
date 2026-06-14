<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, the arithmetic series identity: define `sum_upto n = 1+2+...+n` and prove `2 * sum_upto n = n * (n + 1)`. Mirror
`work-units/gauss-sum/targets/rocq/GaussSum.v`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
