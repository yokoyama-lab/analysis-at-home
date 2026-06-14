<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, `map_tree g (map_tree f t) = map_tree (fun x => g (f x)) t` (mirror the Rocq target). Mirror
`work-units/tree-map-compose/targets/rocq/TreeMapCompose.v`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
