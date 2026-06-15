<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, **fast-doubling
Fibonacci**. Mirror `work-units/fib-fast-doubling/targets/rocq/FastFib.v`: prove the
addition formula, the two doubling identities, and `fast_fib`:
`n <= fuel -> fastpair fuel n = (fib n, fib (S n))`. Return only the
proof-assistant source, with no axioms / sorry / admit / postulate.
