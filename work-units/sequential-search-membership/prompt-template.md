<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that sequential search uses at most n comparisons (stopping at the first match): `memberc x l` returns (found, #comparisons); prove `snd (memberc x l) <= length l`. Mirror
`work-units/sequential-search-membership/targets/rocq/Membership.v`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
