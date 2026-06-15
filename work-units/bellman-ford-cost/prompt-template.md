<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that Bellman-Ford does rounds*edges relaxations: with the loop cost model, prove `loop rounds (loop edges 1) = rounds * edges`. Mirror
`work-units/bellman-ford-cost/targets/rocq/BellmanFord.v`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
