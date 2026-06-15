<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, the **XOR swap**.
Mirror `work-units/xor-swap/targets/rocq/XorSwap.v`: define `xorswap` (three XORs)
and prove `xorswap_correct`: `xorswap a b = (b, a)`. Return only the
proof-assistant source, with no axioms / sorry / admit / postulate.
