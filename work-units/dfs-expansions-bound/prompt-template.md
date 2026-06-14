<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that a concrete fuel-based DFS does at most |V| vertex expansions: define dfs (skip if visited, else mark+push neighbours), prove its visited set stays NoDup and bounded by length g, and conclude `length (dfs fuel g stack visited) <= length g`. Mirror
`work-units/dfs-expansions-bound/targets/rocq/DfsBound.v`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
