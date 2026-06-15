<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, **Kadane's algorithm**
for the maximum subarray sum. Mirror
`work-units/kadane-max-subarray/targets/rocq/Kadane.v`:

1. over integers, define `cur (x::r) = max 0 (x + cur r)`,
   `best (x::r) = max (cur (x::r)) (best r)`, and `window i k l = firstn k (skipn i l)`;
2. prove `kadane_correct`: `best l` is `>=` the sum of every window and equals the
   sum of some window (so it is the maximum contiguous-subarray sum).

The canonical theorem to certify is `kadane_correct`. Return only the
proof-assistant source, with no axioms / sorry / admit / postulate.
