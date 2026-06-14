<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that the naive simultaneous min-and-max scan uses 2n comparisons: `mmc mn mx l` returns ((min,max), #comparisons); prove `snd (mmc mn mx l) = 2 * length l`. Mirror
`work-units/min-and-max-comparisons/targets/rocq/MinMax.v`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
