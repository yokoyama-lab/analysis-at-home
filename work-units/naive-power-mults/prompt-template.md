<!-- Porting task for a contributor's own LLM (lean | agda | isabelle target).
The Rocq target is verified; mirror its cost model. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that naive
exponentiation b^e by repeated multiplication uses exactly e multiplications.

Mirror the Rocq development
(`work-units/naive-power-mults/targets/rocq/NaivePower.v`):
- `powc b e` returns (value, #multiplications); each exponent step multiplies once;
- prove `snd (powc b e) = e` (optionally the correctness companion
  `fst (powc b e) = b ^ e`).

Return only the proof-assistant source, with no axioms / sorry / admit /
postulate.
