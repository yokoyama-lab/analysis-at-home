<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that Karatsuba makes 3^k multiplications: prove `M 0 = 1 -> (forall k, M (S k) = 3 * M k) -> forall k, M k = 3 ^ k`. Mirror
`work-units/karatsuba-multiplications/targets/rocq/Karatsuba.v`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
