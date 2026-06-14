<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that finding the
minimum of a list of length n uses exactly n − 1 comparisons. Mirror
`work-units/list-minimum-comparisons/targets/rocq/ListMinimum.v`: `minc l`
returns (minimum, #comparisons); prove `snd (minc l) = length l - 1`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
