<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that a sorted (nondecreasing) list has zero inversions: define `inv` and `sorted` and prove `sorted l -> inv l = 0`. Mirror
`work-units/sorted-zero-inversions/targets/rocq/SortedInv.v`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
