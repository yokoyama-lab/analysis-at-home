(* analysis@home — work unit: n-le-square (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Every n is at most its square. *)

Require Import Arith Lia.

Theorem n_le_square : forall n, n <= n * n.
Proof. intro n. nia. Qed.
