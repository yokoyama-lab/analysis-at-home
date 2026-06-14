<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, Nicomachus's theorem: define `sumcube n = 1^3+...+n^3` and prove `4 * sumcube n = (n * (n + 1)) * (n * (n + 1))`. Mirror
`work-units/nicomachus-cubes/targets/rocq/Nicomachus.v`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
