<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that filtering a length-n list evaluates the predicate n times: `filterc p l` returns (kept, #tests); prove `snd (filterc p l) = length l`. Mirror
`work-units/list-filter-tests/targets/rocq/ListFilter.v`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
