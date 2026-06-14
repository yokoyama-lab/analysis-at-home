<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, `forallb p (l1 ++ l2) = forallb p l1 && forallb p l2` (mirror the Rocq target). Mirror
`work-units/list-forallb-append/targets/rocq/ForallbApp.v`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
