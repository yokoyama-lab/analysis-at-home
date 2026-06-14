<!--
Porting task for a contributor's own LLM (lean / agda / isabelle target).
The Rocq target is already verified; use it as the reference cost model.
-->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that merge sort is
O(n log n) in comparisons, via the level-budget form:

    length l <= 2^k  ->  comparisons k l <= k * length l.

Mirror the cost model of the verified Rocq development
(`work-units/merge-sort-comparisons/targets/rocq/MergeSortComparisons.v`):
- balanced `split` (each half <= 2^(k-1), total length preserved);
- `merge` counts one comparison per step, costs <= |l1|+|l2|, preserves length;
- `msort k` recurses on the two halves with budget k-1 and merges;
- prove the bound by induction on k.

Return only the proof-assistant source, proving the theorem with no axioms /
`sorry` / `admit`.
