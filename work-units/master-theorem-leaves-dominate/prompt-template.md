<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, `T 0 = 0 -> (forall k, T (S k) <= 4 * T k + 2 ^ (S k)) -> forall k, T k + 2 ^ k <= 4 ^ k` (mirror the Rocq target). Mirror
`work-units/master-theorem-leaves-dominate/targets/rocq/MasterLeaves.v`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
