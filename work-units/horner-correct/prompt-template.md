<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, the correctness of
**Horner's rule**. Mirror `work-units/horner-correct/targets/rocq/Horner.v`: define
`horner` (nested form) and `poly` (explicit Σ cs_i x^i), and prove
`horner_correct`: `horner cs x = poly cs x`. Return only the proof-assistant
source, with no axioms / sorry / admit / postulate.
