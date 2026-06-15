<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that edge relaxation is monotone: with relax d u v w = upd d v (min (nth v d 0) (nth u d 0 + w)), prove `nth i (relax d u v w) 0 <= nth i d 0`. Mirror
`work-units/shortest-path-relaxation-monotone/targets/rocq/RelaxMono.v`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
