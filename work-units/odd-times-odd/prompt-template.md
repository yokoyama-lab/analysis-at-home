<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, `(exists k, a=2*k+1) -> (exists k, b=2*k+1) -> exists k, a*b = 2*k+1` (mirror the Rocq target). Mirror
`work-units/odd-times-odd/targets/rocq/OddTimes.v`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
