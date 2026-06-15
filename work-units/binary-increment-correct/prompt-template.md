<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that a **binary
counter increment adds one**. Mirror `work-units/binary-increment-correct/targets/rocq/BinInc.v`:
define `from_bits` (base-2 Horner over `list bool`) and `inc` (ripple carry), and
prove `inc_correct`: `from_bits (inc l) = S (from_bits l)`. Return only the
proof-assistant source, with no axioms / sorry / admit / postulate.
