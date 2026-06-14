<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, the worst-case comparison count of quickselect: define the worst-case recurrence `qsel_worst` and prove `2 * qsel_worst n + n = n * n`. Mirror
`work-units/quickselect-worst-case/targets/rocq/Quickselect.v`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
