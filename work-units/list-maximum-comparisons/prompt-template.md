<!-- Porting task for a contributor's own LLM (lean | agda | isabelle target).
The Rocq target is verified; mirror its cost model. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that finding the
maximum of a list of length n uses exactly n − 1 comparisons.

Mirror the Rocq development
(`work-units/list-maximum-comparisons/targets/rocq/ListMaximum.v`):
- `maxc l` returns (maximum, #comparisons): one comparison per element after the
  first;
- prove `snd (maxc l) = length l - 1`.

Return only the proof-assistant source, with no axioms / sorry / admit /
postulate.
