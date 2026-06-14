<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, `T 0 = 0 -> (forall k, T (S k) = T k + 1) -> forall k, T k = k` (mirror the Rocq target). Mirror
`work-units/binary-search-recurrence/targets/rocq/BinSearchRec.v`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
