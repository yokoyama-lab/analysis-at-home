<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that the **expected
number of hash collisions of n keys in n slots is (n-1)/2**. Mirror
`work-units/collisions-expected-hashing/targets/rocq/Coll.v`: model the assignment
space `{1..n}^k`, define `coll`/`Tot_coll`, prove the recurrence and the
subtraction-free identity `2*n*Tot_coll n k + k*n^k = k*k*n^k`, and conclude
`collisions_expected`: `0 < n -> 2 * Tot_coll n n = (n-1) * n^n`. Return only the
proof-assistant source, with no axioms / sorry / admit / postulate.
