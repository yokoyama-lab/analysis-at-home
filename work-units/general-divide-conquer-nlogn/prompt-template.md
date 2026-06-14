<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, `T 0 = 0 -> (forall k, T (S k) <= b * T k + b ^ (S k)) -> forall k, T k <= k * b ^ k` (mirror the Rocq target). Mirror
`work-units/general-divide-conquer-nlogn/targets/rocq/GeneralDC.v`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
