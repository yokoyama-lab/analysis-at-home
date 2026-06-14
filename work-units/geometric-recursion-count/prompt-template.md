<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, `M 0 = 1 -> (forall k, M (S k) = a * M k) -> forall k, M k = a ^ k` (mirror the Rocq target). Mirror
`work-units/geometric-recursion-count/targets/rocq/GeomRec.v`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
