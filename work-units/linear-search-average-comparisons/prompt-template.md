<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, the exact average
comparison count of linear search for a uniformly random present target. Mirror
`work-units/linear-search-average-comparisons/targets/rocq/LinearSearchAverage.v`:

1. `lsearch x l` returns (found, #comparisons); prove the cost-model grounding
   `lsearch_at`: if `x` does not occur in `pref` then
   `snd (lsearch x (pref ++ x :: l)) = S (length pref)` (cost at 1-based position
   p is p).
2. Define `sum_upto n = 1 + 2 + ... + n` and prove the exact total
   `2 * sum_upto n = n * (n + 1)`, so the average over the n positions is (n+1)/2.

The canonical theorem to certify is `linear_search_avg_total`. Return only the
proof-assistant source, with no axioms / sorry / admit / postulate.
