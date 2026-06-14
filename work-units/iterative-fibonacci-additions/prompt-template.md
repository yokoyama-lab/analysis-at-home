<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that iterative
Fibonacci (two accumulators) uses exactly n additions for n steps. Mirror
`work-units/iterative-fibonacci-additions/targets/rocq/IterativeFibonacci.v`:
`fibc a b n` returns (result, #additions), one `a + b` per step; prove
`snd (fibc a b n) = n`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
