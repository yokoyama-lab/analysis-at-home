<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that the mergesort recurrence is n log n: prove `T 0 = 0 -> (forall k, T (S k) <= 2*T k + 2^(S k)) -> forall k, T k <= k * 2^k`. Mirror
`work-units/mergesort-recurrence/targets/rocq/MergesortRec.v`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
