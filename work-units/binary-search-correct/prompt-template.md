<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, the correctness of
**binary search**. Mirror `work-units/binary-search-correct/targets/rocq/BSearch.v`:
define `bsearch` on an index window and prove `bsearch_correct`:
`monotone a -> hi-lo<=fuel -> (bsearch fuel a key lo hi = true <-> exists i, lo<=i<hi /\ a i = key)`
(soundness needs nothing; completeness uses monotonicity). Return only the
proof-assistant source, with no axioms / sorry / admit / postulate.
