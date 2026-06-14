<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, the closed form of
the weighted geometric sum. Mirror
`work-units/geometric-weighted-sum/targets/rocq/GeometricWeightedSum.v`:
define `pow2 n = 2^n` and `wsum n = Σ_{k=0}^{n-1} k * 2^k`, then prove
`wsum n + 2 * pow2 n = n * pow2 n + 2` (the nat form of `Σ k·2^k = (n-2)·2^n + 2`).

The induction step is the telescoping certificate `F(k+1) - F(k) = k·2^k` for
`F(k) = (k-2)·2^k`; nonlinear integer arithmetic (e.g. `nia` / `nlinarith`)
closes it given the induction hypothesis.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
