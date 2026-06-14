<!--
Porting task for a contributor's own LLM (lean / agda / isabelle target).
The Rocq target is already verified; use it as the reference cost model.
-->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that selection sort
performs exactly n(n-1)/2 key comparisons.

Mirror the cost model of the verified Rocq development
(`work-units/selection-sort-comparisons/targets/rocq/SelectionSortComparisons.v`):
- `select x l` returns (min, remaining, #comparisons) and uses exactly `|l|`
  comparisons (one `y < x` test per element);
- `ssort` sums the per-round comparison counts;
- prove the division-free equality `2 * comparisons l = length l * (length l - 1)`.

Return only the proof-assistant source, proving the theorem with no axioms /
`sorry` / `admit`, so the kernel accepts it.
