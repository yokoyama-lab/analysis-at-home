<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that insertion sort
performs at least n-1 key comparisons on a list of length n. Mirror
`work-units/insertion-sort-best-case/targets/rocq/InsertionSortBestCase.v`:
the instrumented `insert`/`isort` count one comparison per `x <=? y` test;
`comparisons l = snd (isort l)`. Prove
`length l <= S (comparisons l)` (i.e. comparisons >= length - 1).

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
