<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, `T 0 = 0 -> (forall k, T (S k) = T k + S k) -> forall k, 2 * T k = k * (k + 1)` (mirror the Rocq target). Mirror
`work-units/linear-recursion-quadratic/targets/rocq/LinRecQuad.v`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
