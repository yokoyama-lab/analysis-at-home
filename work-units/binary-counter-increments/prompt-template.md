<!--
Porting task for a contributor's own LLM (lean / agda / isabelle target).
The Rocq target is already verified; use it as the reference cost model.
-->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that n increments of
a binary counter (from empty) cost at most 2n bit flips.

Mirror the cost model of the verified Rocq development
(`work-units/binary-counter-increments/targets/rocq/BinaryCounterIncrements.v`):
- counter = list of bits (LSB first); `incr` returns (new bits, #flips);
- `incr_n n` performs n increments from empty, summing flips; `flips n` is the total;
- prove `flips n <= 2 * n`. The clean route is the invariant
  `total flips + count_ones(state) = 2n` (potential = popcount).

Return only the proof-assistant source, proving the theorem with no axioms /
`sorry` / `admit`.
