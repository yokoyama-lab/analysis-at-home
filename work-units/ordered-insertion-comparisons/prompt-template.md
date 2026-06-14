<!-- Porting task for a contributor's own LLM (lean | agda | isabelle target).
The Rocq target is verified; mirror its cost model. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that inserting one
element into a list of length n uses at most n comparisons.

Mirror the Rocq development
(`work-units/ordered-insertion-comparisons/targets/rocq/OrderedInsertion.v`):
- `insert x l` returns (new list, #comparisons): one `x <=? y` test per element
  scanned, stopping at the insertion point;
- prove `snd (insert x l) <= length l`.

Return only the proof-assistant source, with no axioms / sorry / admit /
postulate.
