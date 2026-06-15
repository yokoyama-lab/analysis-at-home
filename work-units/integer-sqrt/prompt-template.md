<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, the **integer square
root**. Mirror `work-units/integer-sqrt/targets/rocq/Isqrt.v`: define `isqrt` and
prove `isqrt_correct`: `isqrt n * isqrt n <= n /\ n < S (isqrt n) * S (isqrt n)`.
Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
