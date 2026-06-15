<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, DFS completeness: prove that if the worklist drains (snd (dfs2 fuel g src []) = []) then reach g src v -> In v (fst (dfs2 fuel g src [])), via a closure invariant. Mirror
`work-units/dfs-completeness/targets/rocq/DfsComplete.v`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
