<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, the **correctness of
insertion sort**. Mirror `work-units/insertion-sort-correct/targets/rocq/InsSort.v`:
define `insert`/`isort` and a `Sorted` predicate, and prove `isort_correct`:
`Sorted (isort l) /\ Permutation (isort l) l`. Return only the proof-assistant
source, with no axioms / sorry / admit / postulate.
