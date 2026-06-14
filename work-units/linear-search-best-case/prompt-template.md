<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that linear search
over a non-empty list performs at least one key comparison. Mirror
`work-units/linear-search-best-case/targets/rocq/LinearSearchBestCase.v`:
`lsearch x l` returns (found, #comparisons); prove
`1 <= length l -> 1 <= snd (lsearch x l)`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
