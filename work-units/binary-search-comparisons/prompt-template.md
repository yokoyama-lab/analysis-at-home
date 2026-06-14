<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that binary search on a region of size n uses at most k comparisons when n < 2^k: model the search by halving the size, and prove `n < 2 ^ k -> bsearch fuel n <= k`. Mirror
`work-units/binary-search-comparisons/targets/rocq/BinarySearch.v`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
