(* analysis@home — work unit: triangular-le-square (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Twice the n-th triangular number is at most 2n^2. *)

Require Import Arith Lia.

Theorem triangular_le_square : forall n, n*(n+1) <= 2*n*n.
Proof. intro n. nia. Qed.
