<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, the counting-sort invariant: with `cnt`/`sumhist` (histogram over K buckets), prove `(forall x, In x l -> x < K) -> sumhist K l = length l`. Mirror
`work-units/counting-sort-histogram/targets/rocq/CountingSort.v`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
