<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that reversing a length-n list into an accumulator uses n cons operations: `rev_list l` returns (reversed, #cons); prove `snd (rev_list l) = length l`. Mirror
`work-units/list-reversal-operations/targets/rocq/ListReverse.v`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
