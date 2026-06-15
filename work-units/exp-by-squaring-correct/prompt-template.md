<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, the correctness of
**exponentiation by squaring**. Mirror
`work-units/exp-by-squaring-correct/targets/rocq/FastPow.v`: define `fastpow` and
prove `fastpow_correct`: `e <= fuel -> fastpow fuel b e = b ^ e`. Return only the
proof-assistant source, with no axioms / sorry / admit / postulate.
