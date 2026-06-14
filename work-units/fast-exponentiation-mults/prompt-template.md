<!--
Porting task for a contributor's own LLM (lean / agda / isabelle target).
The Rocq target is already verified; use it as the reference cost model.
-->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that square-and-
multiply exponentiation uses at most 2 * (number of bits of the exponent)
multiplications.

Mirror the cost model of the verified Rocq development
(`work-units/fast-exponentiation-mults/targets/rocq/FastExponentiation.v`):
- exponent = binary digit list (LSB first);
- `sqm sq ds` returns (base^(value of ds), #mults): one squaring per digit, plus
  one multiply for each 1-digit;
- prove `snd (sqm sq ds) <= 2 * length ds`.

Return only the proof-assistant source, proving the theorem with no axioms /
`sorry` / `admit`.
