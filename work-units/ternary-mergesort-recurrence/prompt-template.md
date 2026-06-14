<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, `T 0 = 0 -> (forall k, T (S k) <= 3 * T k + 3 ^ (S k)) -> forall k, T k <= k * 3 ^ k` (mirror the Rocq target). Mirror
`work-units/ternary-mergesort-recurrence/targets/rocq/TernaryMerge.v`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
