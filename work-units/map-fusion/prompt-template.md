<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, `map g (map f l) = map (fun x => g (f x)) l` (mirror the Rocq target). Mirror
`work-units/map-fusion/targets/rocq/MapFusion.v`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
