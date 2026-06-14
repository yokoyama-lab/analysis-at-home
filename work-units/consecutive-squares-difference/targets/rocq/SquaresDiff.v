(* analysis@home — work unit: consecutive-squares-difference (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Consecutive squares differ by the n-th odd number. *)

Require Import Arith Lia.

Theorem consecutive_squares_difference : forall n, (S n) * (S n) = n * n + (2 * n + 1).
Proof. intro n. nia. Qed.
