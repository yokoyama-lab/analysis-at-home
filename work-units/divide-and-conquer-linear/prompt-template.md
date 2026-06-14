<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that a single-recursive-call divide-and-conquer with linear work is linear: prove `T 0 = 0 -> (forall k, T (S k) <= T k + 2^(S k)) -> forall k, T k <= 2^(S k)`. Mirror
`work-units/divide-and-conquer-linear/targets/rocq/DCLinear.v`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
