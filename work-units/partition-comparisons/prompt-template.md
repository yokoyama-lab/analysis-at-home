<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that partitioning a list around a pivot uses one comparison per element: `partitionc piv l` returns ((lo,hi), #comparisons); prove `snd (partitionc piv l) = length l`. Mirror
`work-units/partition-comparisons/targets/rocq/Partition.v`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
