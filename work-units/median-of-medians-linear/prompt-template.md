<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that the median-of-medians selection recurrence is linear: prove that `T 0 = 0` and `forall n, T n <= T (n/5) + T (7*n/10) + n` imply `forall n, T n <= 10 * n` (bounded strong induction; the contraction 1/5+7/10 < 1 is the key). Mirror
`work-units/median-of-medians-linear/targets/rocq/MedianOfMedians.v`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
