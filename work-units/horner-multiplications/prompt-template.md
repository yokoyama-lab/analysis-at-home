<!-- Porting task for a contributor's own LLM (lean | agda | isabelle target).
The Rocq target is verified; mirror its cost model. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that Horner's rule
on k coefficients uses exactly k − 1 multiplications.

Mirror the Rocq development
(`work-units/horner-multiplications/targets/rocq/Horner.v`):
- `horner x coeffs` returns (value, #multiplications): the innermost coefficient
  costs no multiply, every outer step `c + x*v` costs one;
- prove `snd (horner x coeffs) = length coeffs - 1`.

Return only the proof-assistant source, with no axioms / sorry / admit /
postulate.
