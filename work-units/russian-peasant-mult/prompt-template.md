<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, **Russian peasant
multiplication**. Mirror `work-units/russian-peasant-mult/targets/rocq/Peasant.v`:
define `peasant` (halve/double/add) and prove `peasant_correct`:
`a <= fuel -> peasant fuel a b = a * b`. Return only the proof-assistant source,
with no axioms / sorry / admit / postulate.
