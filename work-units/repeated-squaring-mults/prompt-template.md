<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that computing x^(2^k) by repeated squaring uses k multiplications: `repsq k x` returns (value, #mults); prove `snd (repsq k x) = k`. Mirror
`work-units/repeated-squaring-mults/targets/rocq/RepSquare.v`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
