<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that summing the n
numbers in a list uses n-1 additions. Mirror
`work-units/list-sum-additions/targets/rocq/ListSum.v`: fold the tail into an
accumulator seeded with the head, counting one addition per folded element;
`sum_list l` returns (sum, #additions). Prove
`snd (sum_list l) = pred (length l)`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
