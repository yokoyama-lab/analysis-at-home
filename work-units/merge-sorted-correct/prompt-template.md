<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, the **correctness of
merging two sorted lists**. Mirror `work-units/merge-sorted-correct/targets/rocq/Merge.v`:
define `merge` and prove `merge_correct`: `Sorted l1 -> Sorted l2 -> length l1 + length l2 <= fuel -> Sorted (merge fuel l1 l2) /\ Permutation (merge fuel l1 l2) (l1 ++ l2)`.
Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
