<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that mapping f over a length-n list uses n applications: `mapc f l` returns (mapped, #applications); prove `snd (mapc f l) = length l`. Mirror
`work-units/list-map-operations/targets/rocq/ListMap.v`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
