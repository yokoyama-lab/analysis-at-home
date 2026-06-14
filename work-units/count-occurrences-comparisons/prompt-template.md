<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that counting the
occurrences of x in a list of length n uses exactly n comparisons. Mirror
`work-units/count-occurrences-comparisons/targets/rocq/CountOccurrences.v`:
`countc x l` returns (count, #comparisons); prove `snd (countc x l) = length l`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
