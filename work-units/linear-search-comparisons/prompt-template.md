<!-- Porting task for a contributor's own LLM (lean | agda | isabelle target).
The Rocq target is verified; mirror its cost model. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that linear search
over a list of length n uses at most n comparisons.

Mirror the Rocq development
(`work-units/linear-search-comparisons/targets/rocq/LinearSearch.v`):
- `lsearch x l` returns (found?, #comparisons): one `x =? y` test per element,
  stopping at the first match;
- prove `snd (lsearch x l) <= length l`.

Return only the proof-assistant source, with no axioms / sorry / admit /
postulate.
