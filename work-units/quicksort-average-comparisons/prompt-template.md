<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, the closed form of the
average comparison count of randomized quicksort. Mirror
`work-units/quicksort-average-comparisons/targets/rocq/QuicksortAverage.v`, working
in the rationals:

1. Define the harmonic number `H n = Σ_{i=1}^n 1/i`.
2. Define `C` as the solution of the reduced recurrence
   `C(0)=0`, `C(S m) = ((m+2)·C(m) + 2m)/(m+1)`
   (i.e. `n·C(n) = (n+1)·C(n−1) + 2(n−1)`).
3. Define `Cf n = 2·(n+1)·H n − 4·n`.
4. Prove `C n == Cf n` (rational equality). The induction step is the certificate
   "the closed form solves the recurrence"; a field-arithmetic tactic closes it
   given that `n+1 ≠ 0`.

This unit needs **rationals + a field-arithmetic tactic**, so pull in the
relevant library: for Lean use **Mathlib** (`Rat`/`ℚ`, `field_simps`/`ring`); for
Agda use **agda-stdlib** `Data.Rational` (and its ring/field reasoning). The Rocq
target uses `QArith` + `field`; the Isabelle target uses `rat` + `field_simps`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
