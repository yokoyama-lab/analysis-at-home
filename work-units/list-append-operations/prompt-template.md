<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that appending l2 onto l1 uses length(l1) cons operations: `appendc l1 l2` returns (result, #cons); prove `snd (appendc l1 l2) = length l1`. Mirror
`work-units/list-append-operations/targets/rocq/ListAppend.v`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
