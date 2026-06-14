<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that computing n! by
repeated multiplication uses exactly n − 1 multiplications. Mirror
`work-units/factorial-mults/targets/rocq/Factorial.v`: `factc n` returns
(n!, #multiplications); prove `snd (factc n) = n - 1`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
