<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, the correctness of the
**Boyer-Moore majority vote** (MJRTY, 1981). Mirror
`work-units/boyer-moore-majority/targets/rocq/BoyerMoore.v`:

1. define `cnt x l`, the streaming `step` on a `(candidate,count)` pair, and
   `bm l = fold_left step l (0,0)`;
2. prove `boyer_moore_majority`: `length l < 2 * cnt m l -> fst (bm l) = m`,
   carrying the cancellation invariant
   `(forall x<>c, 2*cnt x prefix + count <= length prefix) /\ (2*cnt c prefix <= length prefix + count)`
   by induction on the prefix.

The canonical theorem to certify is `boyer_moore_majority`. Return only the
proof-assistant source, with no axioms / sorry / admit / postulate.
