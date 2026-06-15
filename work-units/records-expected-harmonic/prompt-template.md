<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that the **expected
number of records of a uniformly random permutation of [n] is H_n**. Mirror
`work-units/records-expected-harmonic/targets/rocq/Records.v`: model uniform
permutations by sequential-rank vectors (`ranks n`, c_i ∈ {1..i}), define
`records` and `E`, prove the recurrence `Tot (S m) = (S m)*Tot m + m!` and conclude
`records_expected`: `E records (ranks n) == harmonic n`. Return only the
proof-assistant source, with no axioms / sorry / admit / postulate.
